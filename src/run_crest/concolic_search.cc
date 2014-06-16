// Copyright (c) 2008, Jacob Burnim (jburnim@cs.berkeley.edu)
//
// This file is part of CREST, which is distributed under the revised
// BSD license.  A copy of this license can be found in the file LICENSE.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See LICENSE
// for details.

#include <algorithm>
#include <assert.h>
#include <cmath>
#include <fstream>
#include <functional>
#include <limits>
#include <stdio.h>
#include <stdlib.h>
#include <queue>
#include <utility>

#include "base/z3_solver.h"
#include "run_crest/concolic_search.h"

using std::binary_function;
using std::ifstream;
using std::ios;
using std::min;
using std::max;
using std::numeric_limits;
using std::pair;
using std::queue;
using std::random_shuffle;
using std::stable_sort;

namespace crest {

namespace {

typedef pair<size_t,int> ScoredBranch;
typedef pair<size_t,double> ExpectScoredBranch;

struct ScoredBranchComp
  : public binary_function<ScoredBranch, ScoredBranch, bool>
{
  bool operator()(const ScoredBranch& a, const ScoredBranch& b) const {
    return (a.second < b.second);
  }
};

struct ExpectScoredBranchComp
  : public binary_function<ExpectScoredBranch, ExpectScoredBranch, bool>
{
  bool operator()(const ExpectScoredBranch& a, const ExpectScoredBranch& b) const {
    return (a.second > b.second);
  }
};
}  // namespace


////////////////////////////////////////////////////////////////////////
//// Search ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

Search::Search(const string& program, int max_iterations)
  : program_(program), max_iters_(max_iterations), num_iters_(0) {

  start_time_ = time(NULL);

  { // Read in the set of branches.
    max_branch_ = 0;
    max_function_ = 0;
    branches_.reserve(100000);
    branch_count_.reserve(100000);
    branch_count_.push_back(0);

    ifstream in("branches");
    assert(in);
    function_id_t fid;
    int numBranches;
    while (in >> fid >> numBranches) {
      branch_count_.push_back(2 * numBranches);
      branch_id_t b1, b2;
      for (int i = 0; i < numBranches; i++) {
	assert(in >> b1 >> b2);
	branches_.push_back(b1);
	branches_.push_back(b2);
	max_branch_ = max(max_branch_, max(b1, b2));
      }
    }
    in.close();
    max_branch_ ++;
    max_function_ = branch_count_.size();
  }

  // Compute the paired-branch map.
  paired_branch_.resize(max_branch_);
  for (size_t i = 0; i < branches_.size(); i += 2) {
    paired_branch_[branches_[i]] = branches_[i+1];
    paired_branch_[branches_[i+1]] = branches_[i];
  }

  // Compute the branch-to-function map.
  branch_function_.resize(max_branch_);
  { size_t i = 0;
    for (function_id_t j = 0; j < branch_count_.size(); j++) {
      for (size_t k = 0; k < branch_count_[j]; k++) {
	branch_function_[branches_[i++]] = j;
      }
    }
  }

  // Initialize all branches to "uncovered" (and functions to "unreached").
  total_num_covered_ = num_covered_ = 0;
  reachable_functions_ = reachable_branches_ = 0;
  covered_.resize(max_branch_, false);
  total_covered_.resize(max_branch_, false);
  reached_.resize(max_function_, false);

#if 0
  { // Read in any previous coverage (for faster debugging).
    ifstream in("coverage");
    branch_id_t bid;
    while (in >> bid) {
      covered_[bid] = true;
      num_covered_ ++;
      if (!reached_[branch_function_[bid]]) {
	reached_[branch_function_[bid]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[bid]];
      }
    }

    total_num_covered_ = 0;
    total_covered_ = covered_;
  }
#endif

  // Print out the initial coverage.
  fprintf(stderr, "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
          num_covered_, reachable_functions_, reachable_branches_);

  // Sort the branches.
  sort(branches_.begin(), branches_.end());
}


Search::~Search() { }


void Search::WriteInputToFileOrDie(const string& file,
				   const vector<value_t>& input) {
  FILE* f = fopen(file.c_str(), "w");
  if (!f) {
    fprintf(stderr, "Failed to open %s.\n", file.c_str());
    perror("Error: ");
    exit(-1);
  }

  for (size_t i = 0; i < input.size(); i++) {
    fprintf(f, "%lld\n", input[i]);
  }

  fclose(f);
}


void Search::WriteCoverageToFileOrDie(const string& file) {
  FILE* f = fopen(file.c_str(), "w");
  if (!f) {
    fprintf(stderr, "Failed to open %s.\n", file.c_str());
    perror("Error: ");
    exit(-1);
  }

  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    if (total_covered_[*i]) {
      fprintf(f, "%d\n", *i);
    }
  }

  fclose(f);
}


void Search::LaunchProgram(const vector<value_t>& inputs) {
  WriteInputToFileOrDie("input", inputs);

  /*
  pid_t pid = fork();
  assert(pid != -1);

  if (!pid) {
    system(program_.c_str());
    exit(0);
  }
  */

  system(program_.c_str());
}


void Search::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  if (++num_iters_ > max_iters_) {
    // TODO(jburnim): Devise a better system for capping the iterations.
    exit(0);
  }
  // Save the given inputs.
  char fname[32];
  snprintf(fname, 32, "input.%d", num_iters_);
  WriteInputToFileOrDie(fname, inputs);

  // Run the program.
  LaunchProgram(inputs);

  // Read the execution from the program.
  // Want to do this with sockets.  (Currently doing it with files.)
  ifstream in("szd_execution", ios::in | ios::binary);
  assert(in && ex->Parse(in));
  in.close();

  /*
  for (size_t i = 0; i < ex->path().branches().size(); i++) {
    fprintf(stderr, "%d ", ex->path().branches()[i]);
  }
  fprintf(stderr, "\n");
  */
}
  

bool Search::UpdateCoverage(const SymbolicExecution& ex) {
  return UpdateCoverage(ex, NULL);
}

bool Search::UpdateCoverage(const SymbolicExecution& ex,
			    set<branch_id_t>* new_branches) {

  const unsigned int prev_covered_ = num_covered_;
  const vector<branch_id_t>& branches = ex.path().branches();
  for (BranchIt i = branches.begin(); i != branches.end(); ++i) {
    if ((*i > 0) && !covered_[*i]) {
      covered_[*i] = true;
      num_covered_++;
      if (new_branches) {
	new_branches->insert(*i);
      }
      if (!reached_[branch_function_[*i]]) {
	reached_[branch_function_[*i]] = true;
	reachable_functions_ ++;
	reachable_branches_ += branch_count_[branch_function_[*i]];
      }
    }
    if ((*i > 0) && !total_covered_[*i]) {
      total_covered_[*i] = true;
      total_num_covered_++;
    }
  }

  fprintf(stderr, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);

  bool found_new_branch = (num_covered_ > prev_covered_);
  if (found_new_branch) {
    WriteCoverageToFileOrDie("coverage");
  }

  return found_new_branch;
}


void Search::RandomInput(const map<var_t,type_t>& vars, vector<value_t>* input) {
  input->resize(vars.size());

  for (map<var_t,type_t>::const_iterator it = vars.begin(); it != vars.end(); ++it) {
    unsigned long long val = 0;
    for (size_t j = 0; j < 8; j++)
      val = (val << 8) + (rand() / 256);

    switch (it->second) {
    case types::U_CHAR:
      input->at(it->first) = (unsigned char)val; break;
    case types::CHAR:
      input->at(it->first) = (char)val; break;
    case types::U_SHORT:
      input->at(it->first) = (unsigned short)val; break;
    case types::SHORT:
      input->at(it->first) = (short)val; break;
    case types::U_INT:
      input->at(it->first) = (unsigned int)val; break;
    case types::INT:
      input->at(it->first) = (int)val; break;
    case types::U_LONG:
      input->at(it->first) = (unsigned long)val; break;
    case types::LONG:
      input->at(it->first) = (long)val; break;
    case types::U_LONG_LONG:
      input->at(it->first) = (unsigned long long)val; break;
    case types::LONG_LONG:
      input->at(it->first) = (long long)val; break;
    }
  }
}


bool Search::SolveAtBranch(const SymbolicExecution& ex,
                           size_t branch_idx,
                           vector<value_t>* input) {

  const vector<SymbolicPred*>& constraints = ex.path().constraints();

  // Optimization: If any of the previous constraints are idential to the
  // branch_idx-th constraint, immediately return false.
  for (int i = static_cast<int>(branch_idx) - 1; i >= 0; i--) {
    if (constraints[branch_idx]->Equal(*constraints[i]))
      return false;
  }

  vector<const SymbolicPred*> cs(constraints.begin(),
				 constraints.begin()+branch_idx+1);
  map<var_t,value_t> soln;
  constraints[branch_idx]->Negate();
  bool success = Z3Solver::IncrementalSolve(ex.inputs(), ex.vars(), cs, &soln);
  fprintf(stderr, "%d\n", success);
  constraints[branch_idx]->Negate();

  if (success) {
    // Merge the solution with the previous input to get the next
    // input.  (Could merge with random inputs, instead.)
    *input = ex.inputs();
    // RandomInput(ex.vars(), input);

    typedef map<var_t,value_t>::const_iterator SolnIt;
    for (SolnIt i = soln.begin(); i != soln.end(); ++i) {
      (*input)[i->first] = i->second;
    }
    return true;
  }

  return false;
}


bool Search::CheckPrediction(const SymbolicExecution& old_ex,
			     const SymbolicExecution& new_ex,
			     size_t branch_idx) {

  if ((old_ex.path().branches().size() <= branch_idx)
      || (new_ex.path().branches().size() <= branch_idx)) {
    return false;
  }

   for (size_t j = 0; j < branch_idx; j++) {
     if  (new_ex.path().branches()[j] != old_ex.path().branches()[j]) {
       return false;
     }
   }
   return (new_ex.path().branches()[branch_idx]
           == paired_branch_[old_ex.path().branches()[branch_idx]]);
}


////////////////////////////////////////////////////////////////////////
//// BoundedDepthFirstSearch ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

BoundedDepthFirstSearch::BoundedDepthFirstSearch
(const string& program, int max_iterations, int max_depth)
  : Search(program, max_iterations), max_depth_(max_depth) { }

BoundedDepthFirstSearch::~BoundedDepthFirstSearch() { }

void BoundedDepthFirstSearch::Run() {
  // Initial execution (on empty/random inputs).
  SymbolicExecution ex;
  RunProgram(vector<value_t>(), &ex);
  UpdateCoverage(ex);

  DFS(0, max_depth_, ex);
  // DFS(0, ex);
}

  /*
void BoundedDepthFirstSearch::DFS(int depth, SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;

  const SymbolicPath& path = prev_ex.path();

  int last = min(max_depth_, static_cast<int>(path.constraints().size()) - 1);
  for (int i = last; i >= depth; i--) {
    // Solve constraints[0..i].
    if (!SolveAtBranch(prev_ex, i, &input)) {
      continue;
    }

    // Run on those constraints.
    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);

    // Check for prediction failure.
    size_t branch_idx = path.constraints_idx()[i];
    if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
      fprintf(stderr, "Prediction failed!\n");
      continue;
    }

    // Recurse.
    DFS(i+1, cur_ex);
  }
}
  */


void BoundedDepthFirstSearch::DFS(size_t pos, int depth, SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;

  const SymbolicPath& path = prev_ex.path();

  for (size_t i = pos; (i < path.constraints().size()) && (depth > 0); i++) {
    // Solve constraints[0..i].
    if (!SolveAtBranch(prev_ex, i, &input)) {
      continue;
    }

    // Run on those constraints.
    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);

    // Check for prediction failure.
    size_t branch_idx = path.constraints_idx()[i];
    if (!CheckPrediction(prev_ex, cur_ex, branch_idx)) {
      fprintf(stderr, "Prediction failed!\n");
      continue;
    }

    // We successfully solved the branch, recurse.
    depth--;
    DFS(i+1, depth, cur_ex);
  }
}


////////////////////////////////////////////////////////////////////////
//// RandomInputSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomInputSearch::RandomInputSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomInputSearch::~RandomInputSearch() { }

void RandomInputSearch::Run() {
  vector<value_t> input;
  RunProgram(input, &ex_);

  while (true) {
    RandomInput(ex_.vars(), &input);
    RunProgram(input, &ex_);
    UpdateCoverage(ex_);
  }
}


////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

RandomSearch::RandomSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

RandomSearch::~RandomSearch() { }

void RandomSearch::Run() {
  SymbolicExecution next_ex;

  while (true) {
    // Execution (on empty/random inputs).
    fprintf(stderr, "RESET\n");
    vector<value_t> next_input;
    RunProgram(next_input, &ex_);
    UpdateCoverage(ex_);

    // Do some iterations.
    int count = 0;
    while (count++ < 10000) {
      // fprintf(stderr, "Uncovered bounded DFS.\n");
      // SolveUncoveredBranches(0, 20, ex_);

      size_t idx;
      if (SolveRandomBranch(&next_input, &idx)) {
	RunProgram(next_input, &next_ex);
	bool found_new_branch = UpdateCoverage(next_ex);
	bool prediction_failed =
	  !CheckPrediction(ex_, next_ex, ex_.path().constraints_idx()[idx]);

	if (found_new_branch) {
	  count = 0;
	  ex_.Swap(next_ex);
	  if (prediction_failed)
	    fprintf(stderr, "Prediction failed (but got lucky).\n");
	} else if (!prediction_failed) {
	  ex_.Swap(next_ex);
	} else {
	  fprintf(stderr, "Prediction failed.\n");
	}
      }
    }
  }
}

  /*
bool RandomSearch::SolveUncoveredBranches(SymbolicExecution& prev_ex) {
  SymbolicExecution cur_ex;
  vector<value_t> input;

  bool success = false;

  int cnt = 0;

  for (size_t i = 0; i < prev_ex.path().constraints().size(); i++) {

    size_t bid_idx = prev_ex.path().constraints_idx()[i];
    branch_id_t bid = prev_ex.path().branches()[bid_idx];
    if (covered_[paired_branch_[bid]])
      continue;

    if (!SolveAtBranch(prev_ex, i, &input)) {
      if (++cnt == 1000) {
	cnt = 0;
	fprintf(stderr, "Failed to solve at %u/%u.\n",
		i, prev_ex.path().constraints().size());
      }
      continue;
    }
    cnt = 0;

    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);
    if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
      fprintf(stderr, "Prediction failed.\n");
      continue;
    }

    success = true;
    cur_ex.Swap(prev_ex);
  }

  return success;
}
  */

void RandomSearch::SolveUncoveredBranches(size_t i, int depth,
					  const SymbolicExecution& prev_ex) {
  if (depth < 0)
    return;

  fprintf(stderr, "position: %zu/%zu (%d)\n",
	  i, prev_ex.path().constraints().size(), depth);

  SymbolicExecution cur_ex;
  vector<value_t> input;

  int cnt = 0;

  for (size_t j = i; j < prev_ex.path().constraints().size(); j++) {
    size_t bid_idx = prev_ex.path().constraints_idx()[j];
    branch_id_t bid = prev_ex.path().branches()[bid_idx];
    if (covered_[paired_branch_[bid]])
      continue;

    if (!SolveAtBranch(prev_ex, j, &input)) {
      if (++cnt == 1000) {
	cnt = 0;
	fprintf(stderr, "Failed to solve at %zu/%zu.\n",
		j, prev_ex.path().constraints().size());
      }
      continue;
    }
    cnt = 0;

    RunProgram(input, &cur_ex);
    UpdateCoverage(cur_ex);
    if (!CheckPrediction(prev_ex, cur_ex, bid_idx)) {
      fprintf(stderr, "Prediction failed.\n");
      continue;
    }

    SolveUncoveredBranches(j+1, depth-1, cur_ex);
  }
}


  bool RandomSearch::SolveRandomBranch(vector<value_t>* next_input, size_t* idx) {
  /*
  const SymbolicPath& p = ex_.path();
  vector<ScoredBranch> zero_branches, other_branches;
  zero_branches.reserve(p.constraints().size());
  other_branches.reserve(p.constraints().size());

  vector<size_t> idxs(p.constraints().size());
  for (size_t i = 0; i < idxs.size(); i++) {
    idxs[i] = i;
  }
  random_shuffle(idxs.begin(), idxs.end());

  vector<int> seen(max_branch_);
  for (vector<size_t>::const_iterator i = idxs.begin(); i != idxs.end(); ++i) {
    branch_id_t bid = p.branches()[p.constraints_idx()[*i]];
    if (!covered_[paired_branch_[bid]]) {
      zero_branches.push_back(make_pair(*i, seen[bid]));
    } else {
      other_branches.push_back(make_pair(*i, seen[bid]));
    }
    seen[bid] += 1;
  }

  stable_sort(zero_branches.begin(), zero_branches.end(), ScoredBranchComp());

  int tries = 1000;
  for (size_t i = 0; (i < zero_branches.size()) && (tries > 0); i++, tries--) {
    if (SolveAtBranch(ex_, zero_branches[i].first, next_input))
      return;
  }

  stable_sort(other_branches.begin(), other_branches.end(), ScoredBranchComp());
  for (size_t i = 0; (i < other_branches.size()) && (tries > 0); i++, tries--) {
    if (SolveAtBranch(ex_, other_branches[i].first, next_input))
      return;
  }
  */

  vector<size_t> idxs(ex_.path().constraints().size());
  for (size_t i = 0; i < idxs.size(); i++)
    idxs[i] = i;

  for (int tries = 0; tries < 1000; tries++) {
    // Pick a random index.
    if (idxs.size() == 0)
      break;
    size_t r = rand() % idxs.size();
    size_t i = idxs[r];
    swap(idxs[r], idxs.back());
    idxs.pop_back();

    if (SolveAtBranch(ex_, i, next_input)) {
      fprintf(stderr, "Solved %zu/%zu\n", i, idxs.size());
      *idx = i;
      return true;
    }
  }

  // We failed to solve a branch, so reset the input.
  fprintf(stderr, "FAIL\n");
  next_input->clear();
  return false;
}


////////////////////////////////////////////////////////////////////////
//// RandomSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

UniformRandomSearch::UniformRandomSearch(const string& program,
					 int max_iterations,
					 size_t max_depth)
  : Search(program, max_iterations), max_depth_(max_depth) { }

UniformRandomSearch::~UniformRandomSearch() { }

void UniformRandomSearch::Run() {
  // Initial execution (on empty/random inputs).
  RunProgram(vector<value_t>(), &prev_ex_);
  UpdateCoverage(prev_ex_);

  while (true) {
    fprintf(stderr, "RESET\n");

    // Uniform random path.
    DoUniformRandomPath();
  }
}

void UniformRandomSearch::DoUniformRandomPath() {
  vector<value_t> input;

  size_t i = 0;
  size_t depth = 0;
  fprintf(stderr, "%zu constraints.\n", prev_ex_.path().constraints().size());
  while ((i < prev_ex_.path().constraints().size()) && (depth < max_depth_)) {
    if (SolveAtBranch(prev_ex_, i, &input)) {
      fprintf(stderr, "Solved constraint %zu/%zu.\n",
	      (i+1), prev_ex_.path().constraints().size());
      depth++;

      // With probability 0.5, force the i-th constraint.
      if (rand() % 2 == 0) {
	RunProgram(input, &cur_ex_);
	UpdateCoverage(cur_ex_);
	size_t branch_idx = prev_ex_.path().constraints_idx()[i];
	if (!CheckPrediction(prev_ex_, cur_ex_, branch_idx)) {
	  fprintf(stderr, "prediction failed\n");
	  depth--;
	} else {
	  cur_ex_.Swap(prev_ex_);
	}
      }
    }

    i++;
  }
}


////////////////////////////////////////////////////////////////////////
//// HybridSearch //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

HybridSearch::HybridSearch(const string& program, int max_iterations, int step_size)
  : Search(program, max_iterations), step_size_(step_size) { }

HybridSearch::~HybridSearch() { }

void HybridSearch::Run() {
  SymbolicExecution ex;

  while (true) {
    // Execution on empty/random inputs.
    RunProgram(vector<value_t>(), &ex);
    UpdateCoverage(ex);

    // Local searches at increasingly deeper execution points.
    for (size_t pos = 0; pos < ex.path().constraints().size(); pos += step_size_) {
      RandomLocalSearch(&ex, pos, pos+step_size_);
    }
  }
}

void HybridSearch::RandomLocalSearch(SymbolicExecution *ex, size_t start, size_t end) {
  for (int iters = 0; iters < 100; iters++) {
    if (!RandomStep(ex, start, end))
      break;
  }
}

bool HybridSearch::RandomStep(SymbolicExecution *ex, size_t start, size_t end) {

  if (end > ex->path().constraints().size()) {
    end = ex->path().constraints().size();
  }
  assert(start < end);

  SymbolicExecution next_ex;
  vector<value_t> input;

  fprintf(stderr, "%zu-%zu\n", start, end);
  vector<size_t> idxs(end - start);
  for (size_t i = 0; i < idxs.size(); i++) {
    idxs[i] = start + i;
  }

  for (int tries = 0; tries < 1000; tries++) {
    // Pick a random index.
    if (idxs.size() == 0)
      break;
    size_t r = rand() % idxs.size();
    size_t i = idxs[r];
    swap(idxs[r], idxs.back());
    idxs.pop_back();

    if (SolveAtBranch(*ex, i, &input)) {
      RunProgram(input, &next_ex);
      UpdateCoverage(next_ex);
      if (CheckPrediction(*ex, next_ex, ex->path().constraints_idx()[i])) {
	ex->Swap(next_ex);
	return true;
      }
    }
  }

  return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgBaselineSearch /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgBaselineSearch::CfgBaselineSearch(const string& program, int max_iterations)
  : Search(program, max_iterations) { }

CfgBaselineSearch::~CfgBaselineSearch() { }


void CfgBaselineSearch::Run() {
  SymbolicExecution ex;

  while (true) {
    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    UpdateCoverage(ex);

    while (DoSearch(5, 250, 0, ex)) {
      // As long as we keep finding new branches . . . .
      ex.Swap(success_ex_);
    }
  }
}


bool CfgBaselineSearch::DoSearch(int depth, int iters, int pos,
				 const SymbolicExecution& prev_ex) {

  // For each symbolic branch/constraint in the execution path, we will
  // compute a heuristic score, and then attempt to force the branches
  // in order of increasing score.
  vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    scoredBranches[i].first = i + pos;
  }

  { // Compute (and sort by) the scores.
    random_shuffle(scoredBranches.begin(), scoredBranches.end());
    map<branch_id_t,int> seen;
    for (size_t i = 0; i < scoredBranches.size(); i++) {
      size_t idx = scoredBranches[i].first;
      size_t branch_idx = prev_ex.path().constraints_idx()[idx];
      branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];
      if (covered_[bid]) {
	scoredBranches[i].second = 100000000 + seen[bid];
      } else {
	scoredBranches[i].second = seen[bid];
      }
      seen[bid] += 1;
    }
  }
  stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

  // Solve.
  SymbolicExecution cur_ex;
  vector<value_t> input;
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    if (iters <= 0) {
      return false;
    }

    if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
      continue;
    }

    RunProgram(input, &cur_ex);
    iters--;

    if (UpdateCoverage(cur_ex, NULL)) {
      success_ex_.Swap(cur_ex);
      return true;
    }
  }

  return false;
}


////////////////////////////////////////////////////////////////////////
//// CfgHeuristicSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

CfgHeuristicSearch::CfgHeuristicSearch
(const string& program, int max_iterations)
  : Search(program, max_iterations),
    cfg_(max_branch_), cfg_rev_(max_branch_), dist_(max_branch_) {

  // Read in the CFG.
  ifstream in("cfg_branches", ios::in | ios::binary);
  assert(in);
  size_t num_branches;
  in.read((char*)&num_branches, sizeof(num_branches));
  assert(num_branches == branches_.size());
  for (size_t i = 0; i < num_branches; i++) {
    branch_id_t src;
    size_t len;
    in.read((char*)&src, sizeof(src));
    in.read((char*)&len, sizeof(len));
    cfg_[src].resize(len);
    in.read((char*)&cfg_[src].front(), len * sizeof(branch_id_t));
  }
  in.close();

  // Construct the reversed CFG.
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
      cfg_rev_[*j].push_back(*i);
    }
  }
}


CfgHeuristicSearch::~CfgHeuristicSearch() { }


void CfgHeuristicSearch::Run() {
  set<branch_id_t> newly_covered_;
  SymbolicExecution ex;

  while (true) {
    covered_.assign(max_branch_, false);
    num_covered_ = 0;

    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      UpdateBranchDistances();
      PrintStats();
    }

    // while (DoSearch(3, 200, 0, kInfiniteDistance+10, ex)) {
    while (DoSearch(5, 30, 0, kInfiniteDistance, ex)) {
    // while (DoSearch(3, 10000, 0, kInfiniteDistance, ex)) {
      PrintStats();
      // As long as we keep finding new branches . . . .
      UpdateBranchDistances();
      ex.Swap(success_ex_);
    }
    PrintStats();
  }
}


void CfgHeuristicSearch::PrintStats() {
  fprintf(stderr, "Cfg solves: %u/%u (%u lucky [%u continued], %u on 0's, %u on others,"
	  "%u unsats, %u prediction failures)\n",
	  (num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
	  num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
	  num_inner_zero_successes_, num_inner_nonzero_successes_,
	  num_inner_unsats_, num_inner_pred_fails_);
  fprintf(stderr, "    (recursive successes: %u)\n", num_inner_recursive_successes_);
  fprintf(stderr, "Top-level SolveAlongCfg: %u/%u\n",
	  num_top_solve_successes_, num_top_solves_);
  fprintf(stderr, "All SolveAlongCfg: %u/%u  (%u all concrete, %u no paths)\n",
	  num_solve_successes_, num_solves_,
	  num_solve_all_concrete_, num_solve_no_paths_);
  fprintf(stderr, "    (sat failures: %u/%u)  (prediction failures: %u) (recursions: %u)\n",
	  num_solve_unsats_, num_solve_sat_attempts_,
	  num_solve_pred_fails_, num_solve_recurses_);
}


void CfgHeuristicSearch::UpdateBranchDistances() {
  // We run a BFS backward, starting simultaneously at all uncovered vertices.
  queue<branch_id_t> Q;
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    if (!covered_[*i]) {
      dist_[*i] = 0;
      Q.push(*i);
    } else {
      dist_[*i] = kInfiniteDistance;
    }
  }

  while (!Q.empty()) {
    branch_id_t i = Q.front();
    size_t dist_i = dist_[i];
    Q.pop();

    for (BranchIt j = cfg_rev_[i].begin(); j != cfg_rev_[i].end(); ++j) {
      if (dist_i + 1 < dist_[*j]) {
	dist_[*j] = dist_i + 1;
	Q.push(*j);
      }
    }
  }
}


bool CfgHeuristicSearch::DoSearch(int depth,
				  int iters,
				  int pos,
				  int maxDist,
				  const SymbolicExecution& prev_ex) {

  fprintf(stderr, "DoSearch(%d, %d, %d, %zu)\n",
	  depth, pos, maxDist, prev_ex.path().branches().size());

  if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
    return false;

  if (depth == 0)
    return false;


  // For each symbolic branch/constraint in the execution path, we will
  // compute a heuristic score, and then attempt to force the branches
  // in order of increasing score.
  vector<ScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    scoredBranches[i].first = i + pos;
  }

  { // Compute (and sort by) the scores.
    random_shuffle(scoredBranches.begin(), scoredBranches.end());
    map<branch_id_t,int> seen;
    for (size_t i = 0; i < scoredBranches.size(); i++) {
      size_t idx = scoredBranches[i].first;
      size_t branch_idx = prev_ex.path().constraints_idx()[idx];
      branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];

      scoredBranches[i].second = dist_[bid] + seen[bid];
      seen[bid] += 1;

      /*
      if (dist_[bid] == 0) {
        scoredBranches[i].second = 0;
      } else {
        scoredBranches[i].second = dist_[bid] + seen[bid];
        seen[bid] += 1;
      }
      */
    }
  }
  stable_sort(scoredBranches.begin(), scoredBranches.end(), ScoredBranchComp());

  // Solve.
  SymbolicExecution cur_ex;
  vector<value_t> input;
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    if ((iters <= 0) || (scoredBranches[i].second > maxDist))
      return false;

    num_inner_solves_ ++;

    if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
      num_inner_unsats_ ++;
      continue;
    }

    RunProgram(input, &cur_ex);
    iters--;

    size_t b_idx = prev_ex.path().constraints_idx()[scoredBranches[i].first];
    branch_id_t bid = paired_branch_[prev_ex.path().branches()[b_idx]];
    set<branch_id_t> new_branches;
    bool found_new_branch = UpdateCoverage(cur_ex, &new_branches);
    bool prediction_failed = !CheckPrediction(prev_ex, cur_ex, b_idx);


    if (found_new_branch && prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(stderr, "Found new branch by forcing at "
	              "distance %zu (%d) [lucky, pred failed].\n",
	      dist_[bid], scoredBranches[i].second);

      // We got lucky, and can't really compute any further stats
      // because prediction failed.
      num_inner_lucky_successes_ ++;
      num_inner_successes_pred_fail_ ++;
      success_ex_.Swap(cur_ex);
      return true;
    }

    if (found_new_branch && !prediction_failed) {
      fprintf(stderr, "Found new branch by forcing at distance %zu (%d).\n",
	      dist_[bid], scoredBranches[i].second);
      size_t min_dist = MinCflDistance(b_idx, cur_ex, new_branches);
      // Check if we were lucky.
      if (FindAlongCfg(b_idx, dist_[bid], cur_ex, new_branches)) {
	assert(min_dist <= dist_[bid]);
	// A legitimate find -- return success.
	if (dist_[bid] == 0) {
	  num_inner_zero_successes_ ++;
	} else {
	  num_inner_nonzero_successes_ ++;
	}
	success_ex_.Swap(cur_ex);
	return true;
      } else {
	// We got lucky, but as long as there were no prediction failures,
	// we'll finish the CFG search to see if that works, too.
	assert(min_dist > dist_[bid]);
	assert(dist_[bid] != 0);
	num_inner_lucky_successes_ ++;
      }
    }

    if (prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      if (!found_new_branch) {
	num_inner_pred_fails_ ++;
	continue;
      }
    }

    // If we reached here, then scoredBranches[i].second is greater than 0.
    num_top_solves_ ++;
    if ((dist_[bid] > 0) &&
        SolveAlongCfg(b_idx, scoredBranches[i].second-1, cur_ex)) {
      num_top_solve_successes_ ++;
      PrintStats();
      return true;
    }

    if (found_new_branch) {
      success_ex_.Swap(cur_ex);
      return true;
    }

    /*
    if (DoSearch(depth-1, 5, scoredBranches[i].first+1, scoredBranches[i].second-1, cur_ex)) {
      num_inner_recursive_successes_ ++;
      return true;
    }
    */
  }

  return false;
}


size_t CfgHeuristicSearch::MinCflDistance
(size_t i, const SymbolicExecution& ex, const set<branch_id_t>& bs) {

  const vector<branch_id_t>& p = ex.path().branches();

  if (i >= p.size())
    return numeric_limits<size_t>::max();

  if (bs.find(p[i]) != bs.end())
    return 0;

  vector<size_t> stack;
  size_t min_dist = numeric_limits<size_t>::max();
  size_t cur_dist = 1;

  fprintf(stderr, "Found uncovered branches at distances:");
  for (BranchIt j = p.begin()+i+1; j != p.end(); ++j) {
    if (bs.find(*j) != bs.end()) {
      min_dist = min(min_dist, cur_dist);
      fprintf(stderr, " %zu", cur_dist);
    }

    if (*j >= 0) {
      cur_dist++;
    } else if (*j == kCallId) {
      stack.push_back(cur_dist);
    } else if (*j == kReturnId) {
      if (stack.size() == 0)
	break;
      cur_dist = stack.back();
      stack.pop_back();
    } else {
      fprintf(stderr, "\nBad branch id: %d\n", *j);
      exit(1);
    }
  }

  fprintf(stderr, "\n");
  return min_dist;
}

bool CfgHeuristicSearch::FindAlongCfg(size_t i, unsigned int dist,
				      const SymbolicExecution& ex,
				      const set<branch_id_t>& bs) {

  const vector<branch_id_t>& path = ex.path().branches();

  if (i >= path.size())
    return false;

  branch_id_t bid = path[i];
  if (bs.find(bid) != bs.end())
    return true;

  if (dist == 0)
    return false;

  // Compute the indices of all branches on the path that immediately
  // follow the current branch (corresponding to the i-th constraint)
  // in the CFG. For example, consider the path:
  //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
  // where '*' is the current branch.  The branches immediately
  // following '*' are : 1, 4, 5, 8, and 9.
  vector<size_t> idxs;
  { size_t pos = i + 1;
    CollectNextBranches(path, &pos, &idxs);
  }

  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
    if (FindAlongCfg(*j, dist-1, ex, bs))
      return true;
  }

  return false;
}


bool CfgHeuristicSearch::SolveAlongCfg(size_t i, unsigned int max_dist,
				       const SymbolicExecution& prev_ex) {
  num_solves_ ++;

  fprintf(stderr, "SolveAlongCfg(%zu,%u)\n", i, max_dist);
  SymbolicExecution cur_ex;
  vector<value_t> input;
  const vector<branch_id_t>& path = prev_ex.path().branches();

  // Compute the indices of all branches on the path that immediately
  // follow the current branch (corresponding to the i-th constraint)
  // in the CFG. For example, consider the path:
  //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
  // where '*' is the current branch.  The branches immediately
  // following '*' are : 1, 4, 5, 8, and 9.
  bool found_path = false;
  vector<size_t> idxs;
  { size_t pos = i + 1;
    CollectNextBranches(path, &pos, &idxs);
    // fprintf(stderr, "Branches following %d:", path[i]);
    for (size_t j = 0; j < idxs.size(); j++) {
      // fprintf(stderr, " %d(%u,%u,%u)", path[idxs[j]], idxs[j],
      //      dist_[path[idxs[j]]], dist_[paired_branch_[path[idxs[j]]]]);
      if ((dist_[path[idxs[j]]] <= max_dist)
	  || (dist_[paired_branch_[path[idxs[j]]]] <= max_dist))
	found_path = true;
    }
    //fprintf(stderr, "\n");
  }

  if (!found_path) {
    num_solve_no_paths_ ++;
    return false;
  }

  bool all_concrete = true;
  num_solve_all_concrete_ ++;

  // We will iterate through these indices in some order (random?
  // increasing order of distance? decreasing?), and try to force and
  // recurse along each one with distance no greater than max_dist.
  random_shuffle(idxs.begin(), idxs.end());
  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
    // Skip if distance is wrong.
    if ((dist_[path[*j]] > max_dist)
	&& (dist_[paired_branch_[path[*j]]] > max_dist)) {
      continue;
    }

    if (dist_[path[*j]] <= max_dist) {
      // No need to force, this branch is on a shortest path.
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, max_dist-1, prev_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }

    // Find the constraint corresponding to branch idxs[*j].
    vector<size_t>::const_iterator idx =
      lower_bound(prev_ex.path().constraints_idx().begin(),
		  prev_ex.path().constraints_idx().end(), *j);
    if ((idx == prev_ex.path().constraints_idx().end()) || (*idx != *j)) {
      continue;  // Branch is concrete.
    }
    size_t c_idx = idx - prev_ex.path().constraints_idx().begin();

    if (all_concrete) {
      all_concrete = false;
      num_solve_all_concrete_ --;
    }

    if(dist_[paired_branch_[path[*j]]] <= max_dist) {
      num_solve_sat_attempts_ ++;
      // The paired branch is along a shortest path, so force.
      if (!SolveAtBranch(prev_ex, c_idx, &input)) {
	num_solve_unsats_ ++;
	continue;
      }
      RunProgram(input, &cur_ex);
      if (UpdateCoverage(cur_ex)) {
	num_solve_successes_ ++;
	success_ex_.Swap(cur_ex);
	return true;
      }
      if (!CheckPrediction(prev_ex, cur_ex, *j)) {
	num_solve_pred_fails_ ++;
	continue;
      }

      // Recurse.
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, max_dist-1, cur_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }
  }

  return false;
}

void CfgHeuristicSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
  while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
    if (path[*pos] == kCallId) {
      (*pos)++;
      SkipUntilReturn(path, pos);
      if (*pos >= path.size())
	return;
      assert(path[*pos] == kReturnId);
    }
    (*pos)++;
  }
}

void CfgHeuristicSearch::CollectNextBranches
(const vector<branch_id_t>& path, size_t* pos, vector<size_t>* idxs) {
  // fprintf(stderr, "Collect(%u,%u,%u)\n", path.size(), *pos, idxs->size());

  // Eat an arbitrary sequence of call-returns, collecting inside each one.
  while ((*pos < path.size()) && (path[*pos] == kCallId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
    SkipUntilReturn(path, pos);
    if (*pos >= path.size())
      return;
    assert(path[*pos] == kReturnId);
    (*pos)++;
  }

  // If the sequence of calls is followed by a branch, add it.
  if ((*pos < path.size()) && (path[*pos] >= 0)) {
    idxs->push_back(*pos);
    (*pos)++;
    return;
  }

  // Alternatively, if the sequence is followed by a return, collect the branches
  // immediately following the return.
  /*
  if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
  }
  */
}


bool CfgHeuristicSearch::DoBoundedBFS(int i, int depth, const SymbolicExecution& prev_ex) {
  if (depth <= 0)
    return false;

  fprintf(stderr, "%d (%d: %d) (%d: %d)\n", depth,
          i-1, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i-1]],
          i, prev_ex.path().branches()[prev_ex.path().constraints_idx()[i]]);

  SymbolicExecution cur_ex;
  vector<value_t> input;
  const vector<SymbolicPred*>& constraints = prev_ex.path().constraints();
  for (size_t j = static_cast<size_t>(i); j < constraints.size(); j++) {
    if (!SolveAtBranch(prev_ex, j, &input)) {
      continue;
    }

    RunProgram(input, &cur_ex);
    iters_left_--;
    if (UpdateCoverage(cur_ex)) {
      success_ex_.Swap(cur_ex);
      return true;
    }

    if (!CheckPrediction(prev_ex, cur_ex, prev_ex.path().constraints_idx()[j])) {
      fprintf(stderr, "Prediction failed!\n");
      continue;
    }

    return (DoBoundedBFS(j+1, depth-1, cur_ex)
	    || DoBoundedBFS(j+1, depth-1, prev_ex));
  }

  return false;
}
////////////////////////////////////////////////////////////////////////
//// MaxExpectLocalSearch ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////

MaxExpectLocalSearch::MaxExpectLocalSearch
(const string& program, int max_iterations)
  : Search(program, max_iterations),
    cfg_(max_branch_), cfg_rev_(max_branch_),
    icfg_(max_branch_),icfg_rev_(max_branch_), dist_(max_branch_){

  
  ifstream in("cfg_branches", ios::in | ios::binary);
  out = fopen("debug","w");//DEBUG
  assert(in);
  size_t num_branches;
  in.read((char*)&num_branches, sizeof(num_branches));
  assert(num_branches == branches_.size());
  fprintf(out,"branches number: %d\n",num_branches);
  for (size_t i = 0; i < num_branches; i++) {
    branch_id_t src;
    size_t len;
    in.read((char*)&src, sizeof(src));
    in.read((char*)&len, sizeof(len));
    cfg_[src].resize(len);
    in.read((char*)&cfg_[src].front(), len * sizeof(branch_id_t));

    fprintf(out,"src %d (%d):",src,len);//DEBUG
    for(vector<branch_id_t>::const_iterator it = cfg_[src].begin();it != cfg_[src].end(); ++it){//DEBUG
       fprintf(out," %d",*it);//DEBUG
    }
    fprintf(out,"\n");//DEBUG
  }
  in.close();

  // Construct the reversed CFG.
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    for (BranchIt j = cfg_[*i].begin(); j != cfg_[*i].end(); ++j) {
      cfg_rev_[*j].push_back(*i);
    }
  }
  
  // initialize the new_paired_branch_
  fprintf(out, "new paired branch.\n");
  for(vector<branch_id_t>::const_iterator paired_it = paired_branch_.begin(); paired_it != paired_branch_.end(); paired_it++){
    new_paired_branch_.push_back(*paired_it);
    fprintf(out, "%d %d\n",paired_it-paired_branch_.begin(), *paired_it);
  }

  fprintf(out, "Iteration 0 (0s): covered %u branches [%u reach funs, %u reach branches].\n",
          num_covered_, reachable_functions_, reachable_branches_);//DEBUG
}


MaxExpectLocalSearch::~MaxExpectLocalSearch() { 
  if(out != NULL){ 
    fclose(out);
  }
}


void MaxExpectLocalSearch::Run() {

  SymbolicExecution ex;
  

  while (true) {
    //covered_.assign(max_branch_, false);
    //num_covered_ = 0;

    // Execution on empty/random inputs.
    fprintf(stderr, "RESET\n");
    fprintf(out, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      UpdateBranchScore(); 
      PrintStats();
    }

   
    while (DoSearch(5, 30, 0, ex)) { 
  
      // As long as we keep finding new branches . . . .
      UpdateBranchScore();
         
      PrintStats();
      ex.Swap(success_ex_);
    }
    PrintStats();
/*    int failedTimes = 0;
    while(true){
      if(DoSearch(5, 30, 0, ex)){
        failedTimes = 0;
        ex.Swap(success_ex_);
        // As long as we keep finding new branches . . . .
        UpdateBranchScore();
         
        PrintStats();
      }else{
        SymbolicExecution tempEx(initialize_ex);
        ex.Swap(tempEx);
        failedTimes ++;
        fprintf(out,"%d failed find new Branch in run\n",failedTimes);
        if(failedTimes > 2){
           break;
           fprintf(out,"the while is break,because too manay RESET!(%d)\n",failedTimes);
        }
      }

    }*/
  }
}


void MaxExpectLocalSearch::PrintStats() {
  fprintf(stderr, "Cfg solves in DoSearch: %u(find new path)/%u(total called time) (%u lucky [%u should SloveAlongCfg],"
          " %u on uncovered branch first, %u on others,%u unsats, %u prediction failures)\n",
	  (num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
	  num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
	  num_inner_zero_successes_, num_inner_nonzero_successes_,
	  num_inner_unsats_, num_inner_pred_fails_);
  fprintf(stderr, "Top-level SolveAlongCfg(called sucess/called times): %u/%u\n",
	  num_top_solve_successes_, num_top_solves_);
  fprintf(stderr, "All SolveAlongCfg(in SolveAlongCfg): %u(sucess)/%u(total) (%u all concrete, %u can't find uncovered branch.\n"
          " %u recursions)",
	  num_solve_successes_, num_solves_,
	  num_solve_all_concrete_, num_solve_no_paths_, num_solve_recurses_);
  fprintf(stderr, "    (sat failure/total sloveAtbranch attempts in SloveAlongCfg: %u/%u) (prediction failures: %u)\n\n\n",
	  num_solve_unsats_, num_solve_sat_attempts_,num_solve_pred_fails_);

  fprintf(out, "Cfg solves in DoSearch: %u(find new path)/%u(total called time) (%u lucky [%u should SloveAlongCfg],"
          " %u on uncovered branch first, %u on others,%u unsats, %u prediction failures)\n",
	  (num_inner_lucky_successes_ + num_inner_zero_successes_ + num_inner_nonzero_successes_ + num_top_solve_successes_),
	  num_inner_solves_, num_inner_lucky_successes_, (num_inner_lucky_successes_ - num_inner_successes_pred_fail_),
	  num_inner_zero_successes_, num_inner_nonzero_successes_,
	  num_inner_unsats_, num_inner_pred_fails_);
  fprintf(out, "Top-level SolveAlongCfg(called sucess/called times): %u/%u\n",
	  num_top_solve_successes_, num_top_solves_);
  fprintf(out, "All SolveAlongCfg(in SolveAlongCfg): %u(sucess)/%u(total) (%u all concrete, %u can't find uncovered branch.\n"
          " %u recursions)",
	  num_solve_successes_, num_solves_,
	  num_solve_all_concrete_, num_solve_no_paths_, num_solve_recurses_);
  fprintf(out, "    (sat failure/total sloveAtbranch attempts in SloveAlongCfg: %u/%u) (prediction failures: %u)\n\n\n",
	  num_solve_unsats_, num_solve_sat_attempts_,num_solve_pred_fails_);

}



double MaxExpectLocalSearch::DFSBranchScore(branch_id_t branch, set<branch_id_t> path) { 
 
//  if(path.find(branch) != path.end())
//       return 0.0;
  if(dist_[branch] >= 0.0) return dist_[branch];
  fprintf(stderr, "\tbranch id %d, branch size %d\n",branch,cfg_[branch].size());
  if(cfg_[branch].size() == 0 || path.find(branch) != path.end()){
     if(!total_covered_[branch]){
        dist_[branch] = 1.0;
     	return 1.0;
     }else{
        dist_[branch] = 0.0;
        return 0.0;
     }  

  }
  double totalScore =0.0;
//  for (BranchIt j = cfg_[branch].begin(); j != cfg_[branch].end(); ++j) {
//      set<branch_id_t> newPath(path);
//      newPath.insert(branch);
//      totalScore += DFSBranchScore(*j,newPath);
//  }
//  totalScore /= cfg_[branch].size();
//  if(!total_covered_[branch])
//	totalScore += 1;
  int count = 0;
  bool isEqual = true;
  for(BranchIt j = cfg_[branch].begin(); j!= cfg_[branch].end(); ++j,count++) {
      set<branch_id_t> newPath(path);
      newPath.insert(branch);
      double tempScore = DFSBranchScore(*j,newPath);
      totalScore += tempScore;
      if(fabs(totalScore - tempScore * count)>0.00001){
        isEqual = false;
      }
  }
  totalScore /= cfg_[branch].size();
  if(!total_covered_[branch]){
	totalScore += 1;
  }else{
    if(isEqual){
      totalScore *= 0.75;
    }
  }
  dist_[branch] = totalScore;
  return totalScore;
}

double MaxExpectLocalSearch::UpdateBranchScore(){
  fprintf(out, "Expect Value in UpdateBranchScore:\n");
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    dist_[*i] = -1;
  }
  double maxScore = 0.0;
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    set<branch_id_t> path;
    dist_[*i] = DFSBranchScore(*i,path);
    fprintf(stderr,"branch id %d,socre %f\n",*i,dist_[*i]);
    fprintf(out,"branch id %d,socre %f\n",*i,dist_[*i]);
    if(dist_[*i]>maxScore)
       maxScore = dist_[*i];
    fprintf(out, "%d:%f  ",*i,dist_[*i]);
  }
    fprintf(out, "\n");
  return maxScore;
}

bool MaxExpectLocalSearch::DoSearch(int depth,
				  int iters,
				  int pos,
				  const SymbolicExecution& prev_ex) {

  fprintf(stderr, "DoSearch(%d, %d, %zu)\n",
	  depth, pos, prev_ex.path().branches().size());
  fprintf(out, "DoSearch(%d, %d, %zu)\npath:\n",
	  depth, pos, prev_ex.path().branches().size());

  for(vector<branch_id_t>::const_iterator it = prev_ex.path().branches().begin(); it != prev_ex.path().branches().end(); ++it){
  	fprintf(out,"%d ",*it);
  	fprintf(stderr,"%d ",*it);
  }

  fprintf(out,"\n");
  fprintf(stderr,"constraint size:%d\n",prev_ex.path().constraints().size());
  fprintf(out,"constraint size:%d\n",prev_ex.path().constraints().size());

  if (pos >= static_cast<int>(prev_ex.path().constraints().size()))
    return false;

  if (depth == 0)
    return false;


  // For each symbolic branch/constraint in the execution path, we will
  // compute a heuristic score, and then attempt to force the branches
  // in order of increasing score.
  vector<ExpectScoredBranch> scoredBranches(prev_ex.path().constraints().size() - pos);
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    scoredBranches[i].first = i + pos;
  }
  //fprintf(stderr,"new_paired_branch_:\n");
  //for(size_t i = 0; i < new_paired_branch_.size(); i++){
  //  if(new_paired_branch_[i]!=0)
  //   fprintf(stderr,"%d-%d ",i, new_paired_branch_[i]);
  //}
  //fprintf(stderr,"\n");
  vector<branch_id_t> new_branch_;
  MapBranch(prev_ex, &new_branch_);
  { // Compute (and sort by) the scores.
    random_shuffle(scoredBranches.begin(), scoredBranches.end());
    map<branch_id_t,int> seen;
    for (size_t i = 0; i < scoredBranches.size(); i++) {
      size_t idx = scoredBranches[i].first;
      size_t branch_idx = prev_ex.path().constraints_idx()[idx];
      //branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];

   
      branch_id_t bid = new_paired_branch_[new_branch_[branch_idx]];
      
      //scoredBranches[i].second = dist_[bid]-seen[bid] > 0? dist_[bid]-seen[bid] : 0.0;
      //scoredBranches[i].second = dist_[bid]-seen[bid] > 0? dist_[bid]-seen[bid] : 0.01;//
      scoredBranches[i].second = seen[bid] > 0? dist_[bid]/seen[bid] : dist_[bid];
      fprintf(out,"branch src %d invert to %d score %f seen %d actually score:%f\n",new_branch_[branch_idx], bid, dist_[bid],
      seen[bid], scoredBranches[i].second);
      seen[bid] += 1;
    }
  }
  stable_sort(scoredBranches.begin(), scoredBranches.end(), ExpectScoredBranchComp());

  fprintf(out,"sorted path(every line is a branch) :\n");
  fprintf(stderr,"sorted path(every line is a branch) :\n");
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    size_t idx = scoredBranches[i].first;
    size_t branch_idx = prev_ex.path().constraints_idx()[idx];
    //branch_id_t bid = paired_branch_[prev_ex.path().branches()[branch_idx]];
 
    branch_id_t bid = new_paired_branch_[new_branch_[branch_idx]];
    fprintf(out, "   branch index %zu,branch id %zu,constraint index in path to invert %zu,socre %f \n",
      branch_idx,bid,scoredBranches[i].first, scoredBranches[i].second);
  }
  fprintf(out,"\n");

  // Solve.
  SymbolicExecution cur_ex;
  vector<value_t> input;
  for (size_t i = 0; i < scoredBranches.size(); i++) {
    if ((iters <= 0) || (scoredBranches[i].second <= 0.0))
      return false;

    num_inner_solves_ ++;
    if (!SolveAtBranch(prev_ex, scoredBranches[i].first, &input)) {
      num_inner_unsats_ ++;
      continue;
    }
    fprintf(stderr,"input:\n");
    for(vector<value_t>::const_iterator iter = input.begin(); iter != input.end(); iter++){
    	fprintf(stderr,"%lld ",*iter);
    }
    fprintf(stderr,"\n");
    RunProgram(input, &cur_ex);
    iters--;

    size_t b_idx = prev_ex.path().constraints_idx()[scoredBranches[i].first];
    branch_id_t bid = paired_branch_[prev_ex.path().branches()[b_idx]];
    set<branch_id_t> new_branches;
    bool isCovered = covered_[bid];
    bool found_new_branch = UpdateCoverage(cur_ex, &new_branches);
    bool prediction_failed = !CheckPrediction(prev_ex, cur_ex, b_idx);
    //fprintf(out,"run program :\n");
    fprintf(out, "constraint size:%d\n",cur_ex.path().constraints().size());
    if (found_new_branch && prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(stderr, "Found new branch by forcing constraint at %zu"
	              "Expect score %f actually find new branch size %d [lucky, pred failed].\n",
	      scoredBranches[i].first, dist_[bid], new_branches.size());
      fprintf(out, "Prediction failed.\n");
      fprintf(out, "Found new branch by forcing constraint at %zu"
	              "Expect score %f actually find new branch size %d [lucky, pred failed].\n",
	      scoredBranches[i].first, dist_[bid], new_branches.size());

      // We got lucky, and can't really compute any further stats
      // because prediction failed.
      num_inner_lucky_successes_ ++;
      num_inner_successes_pred_fail_ ++;
      success_ex_.Swap(cur_ex);
      return true;
    }

    if (found_new_branch && !prediction_failed) {
      fprintf(stderr,"Found new branch by forcing constraint at %zu Expect score %f actually find new branch size %d.\n",
	      scoredBranches[i].first, scoredBranches[i].second, new_branches.size());
      fprintf(out, "Found new branch by forcing constraint at %zu Expect score %f actually find new branch size %d.\n",
	      scoredBranches[i].first, scoredBranches[i].second, new_branches.size());
      /*size_t min_dist = MinCflDistance(b_idx, cur_ex, new_branches);
      // Check if we were lucky.
      //if (FindAlongCfg(b_idx, dist_[bid], cur_ex, new_branches)) {
	//assert(min_dist <= dist_[bid]);
	// A legitimate find -- return success.*/
	//if (covered_[bid]) {
	if(!isCovered){
	  num_inner_zero_successes_ ++;
	  fprintf(stderr,"the inverted branch is uncovered before\n");
	  fprintf(out,"the inverted branch is uncovered before\n");
	} else {
	  num_inner_nonzero_successes_ ++;
	  fprintf(stderr,"the inverted branch is covered before\n");
	  fprintf(out,"the inverted branch is covered before\n");
	}
	fprintf(stderr,"before swap\n");
	success_ex_.Swap(cur_ex);
	fprintf(stderr,"after swap\n");
	return true;
     /* } else {
	// We got lucky, but as long as there were no prediction failures,
	// we'll finish the CFG search to see if that works, too.
	assert(min_dist > dist_[bid]);
	assert(dist_[bid] != 0);
	num_inner_lucky_successes_ ++;
      }*/
    }

    if (prediction_failed) {
      fprintf(stderr, "Prediction failed.\n");
      fprintf(out, "Prediction failed.\n");
      if (!found_new_branch) {
	num_inner_pred_fails_ ++;
	continue;
      }
    }

    // If we reached here, then scoredBranches[i].second is greater than 0.
 
    num_top_solves_ ++;
     fprintf(out, "no new branch, prediction successly at constraint id %zu.\ncontinue to search\n",scoredBranches[i].first);
      fprintf(out, "continue to recurise search\n");
      if(DoSearch(depth-1, 5, scoredBranches[i].first+1, cur_ex)) {
        
        num_top_solve_successes_ ++;
        PrintStats();
        return true;
      }
    //}

    if (found_new_branch) {
      success_ex_.Swap(cur_ex);
      return true;
    }

    /*
    if (DoSearch(depth-1, 5, scoredBranches[i].first+1, scoredBranches[i].second-1, cur_ex)) {
      num_inner_recursive_successes_ ++;
      return true;
    }
    */
  }

  return false;
}

void MaxExpectLocalSearch::MapBranch(const SymbolicExecution& ex, vector<branch_id_t>* new_branches_){
  //fprintf(out,"call MapBranch\n");
  //fprintf(stderr,"call MapBranch\nnew branch:\n");
  new_branches_->clear();
  //new_branches_->resize(ex.path().branches().size());
  for(vector<branch_id_t>::const_iterator it = ex.path().branches().begin(); it != ex.path().branches().end(); ++it){
    new_branches_->push_back(*it);
  }
  /*for(vector<branch_id_t>::const_iterator it = new_branches_->begin(); it != new_branches_->end(); ++it){
    fprintf(out, "%d ",*it);
  }
  fprintf(out,"\n");*/
}

bool MaxExpectLocalSearch::SolveAlongCfg(size_t i,
				       const SymbolicExecution& prev_ex) {
  num_solves_ ++;

  fprintf(stderr, "SolveAlongCfg(%zu)\n", i);
  fprintf(out, "SolveAlongCfg(%zu)\n", i);
  SymbolicExecution cur_ex;
  vector<value_t> input;
  const vector<branch_id_t>& path = prev_ex.path().branches();

  // Compute the indices of all branches on the path that immediately
  // follow the current branch (corresponding to the i-th constraint)
  // in the CFG. For example, consider the path:
  //     * ( ( ( 1 2 ) 4 ) ( 5 ( 6 7 ) ) 8 ) 9
  // where '*' is the current branch.  The branches immediately
  // following '*' are : 1, 4, 5, 8, and 9.
  bool found_path = false;
  vector<size_t> idxs;
  { size_t pos = i + 1;
    CollectNextBranches(path, &pos, &idxs);
     fprintf(out, "Branches following %d:", path[i]);
    for (size_t j = 0; j < idxs.size(); j++) {

      if ((dist_[path[idxs[j]]] !=0)
	  || (dist_[paired_branch_[path[idxs[j]]]] != 0))
	found_path = true;
    }
    fprintf(out, "\n");
  }

  if (!found_path) {
    num_solve_no_paths_ ++;
    return false;
  }

  bool all_concrete = true;
  num_solve_all_concrete_ ++;

  // We will iterate through these indices in some order (random?
  // increasing order of distance? decreasing?), and try to force and
  // recurse along each one with distance no greater than max_dist.
  //random_shuffle(idxs.begin(), idxs.end());

  vector<ExpectScoredBranch> scoredNextBranches(idxs.size());
  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
//    scoredNextBranches[index].first = *j;
//    scoredNextBranches[index].second = dist_[paired_branch_[path[*j]]];
    scoredNextBranches.push_back(make_pair(*j,dist_[paired_branch_[path[*j]]]));
  }
  stable_sort(scoredNextBranches.begin(), scoredNextBranches.end(), ExpectScoredBranchComp());
  idxs.clear();
  fprintf(out,"sorted next branches:");
  for(vector<ExpectScoredBranch>::const_iterator it = scoredNextBranches.begin(); it != scoredNextBranches.end(); ++it){
	idxs.push_back(it->first);
	fprintf(out,"%d ",it->first);
  }
 ///////////////////

  for (vector<size_t>::const_iterator j = idxs.begin(); j != idxs.end(); ++j) {
    // Skip if distance is wrong.
    if ((dist_[path[*j]] == 0)
	&& (dist_[paired_branch_[path[*j]]] == 0)) {
      continue;
    }

    if (dist_[path[*j]] > dist_[paired_branch_[path[*j]]] ) {
     
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, prev_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }

    // Find the constraint corresponding to branch idxs[*j].
  
    vector<size_t>::const_iterator idx =
      lower_bound(prev_ex.path().constraints_idx().begin(),
		  prev_ex.path().constraints_idx().end(), *j);
    if ((idx == prev_ex.path().constraints_idx().end()) || (*idx != *j)) { 
      continue;  // Branch is concrete.
    }
    size_t c_idx = idx - prev_ex.path().constraints_idx().begin(); 

    if (all_concrete) {
      all_concrete = false;
      num_solve_all_concrete_ --;
    }

    if(dist_[paired_branch_[path[*j]]] != 0 && 
	(dist_[path[*j]] <= dist_[paired_branch_[path[*j]]] )) {
      num_solve_sat_attempts_ ++;
      // The paired branch is along a shortest path, so force.
      if (!SolveAtBranch(prev_ex, c_idx, &input)) {
	num_solve_unsats_ ++;
	continue;
      }
      RunProgram(input, &cur_ex);
      if (UpdateCoverage(cur_ex)) {
	num_solve_successes_ ++;
	success_ex_.Swap(cur_ex);
	return true;
      }
      if (!CheckPrediction(prev_ex, cur_ex, *j)) {
	num_solve_pred_fails_ ++;
	continue;
      }

      // Recurse.
      num_solve_recurses_ ++;
      if (SolveAlongCfg(*j, cur_ex)) {
	num_solve_successes_ ++;
	return true;
      }
    }
  }

  return false;
}

void MaxExpectLocalSearch::SkipUntilReturn(const vector<branch_id_t> path, size_t* pos) {
  while ((*pos < path.size()) && (path[*pos] != kReturnId)) {
    if (path[*pos] == kCallId) {
      (*pos)++;
      SkipUntilReturn(path, pos);
      if (*pos >= path.size())
	return;
      assert(path[*pos] == kReturnId);
    }
    (*pos)++;
  }
}

void MaxExpectLocalSearch::CollectNextBranches
(const vector<branch_id_t>& path, size_t* pos, vector<size_t>* idxs) {
   fprintf(out, "Collect(%u,%u,%u)\n", path.size(), *pos, idxs->size());

  // Eat an arbitrary sequence of call-returns, collecting inside each one.
  while ((*pos < path.size()) && (path[*pos] == kCallId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
    SkipUntilReturn(path, pos);
    if (*pos >= path.size())
      return;
    assert(path[*pos] == kReturnId);
    (*pos)++;
  }

  // If the sequence of calls is followed by a branch, add it.
  if ((*pos < path.size()) && (path[*pos] >= 0)) {
    idxs->push_back(*pos);
    (*pos)++;
    return;
  }

  // Alternatively, if the sequence is followed by a return, collect the branches
  // immediately following the return.
  /*
  if ((*pos < path.size()) && (path[*pos] == kReturnId)) {
    (*pos)++;
    CollectNextBranches(path, pos, idxs);
  }
  */
}
bool MaxExpectLocalSearch::UpdateCoverage(const SymbolicExecution& ex,
		      set<branch_id_t>* new_branches){
  bool b = Search::UpdateCoverage(ex,new_branches);
  fprintf(out, "Iteration %d (%lds): covered %u branches [%u reach funs, %u reach branches].\ncovered branch:\n",
	  num_iters_, time(NULL)-start_time_, total_num_covered_, reachable_functions_, reachable_branches_);
  for (BranchIt i = branches_.begin(); i != branches_.end(); ++i) {
    if (total_covered_[*i]) {
      fprintf(out, "%d ", *i);
    }
  }
  fprintf(out,"\n");
  return b;
}

bool MaxExpectLocalSearch::UpdateCoverage(const SymbolicExecution& ex){
	return UpdateCoverage(ex,NULL);
}

void MaxExpectLocalSearch::RunProgram(const vector<value_t>& inputs, SymbolicExecution* ex) {
  fprintf(out,"input:\n");
  for (size_t i = 0; i < inputs.size(); i++) {
    fprintf(out, "%lld ", inputs[i]);
  }
  fprintf(out,"\n");
  Search::RunProgram(inputs,ex);

}


MaxExpectGlobalSearch::MaxExpectGlobalSearch(const string& program, int max_iterations)
  : MaxExpectLocalSearch(program, max_iterations){
    exs.reserve(max_iterations);
}

MaxExpectGlobalSearch::~MaxExpectGlobalSearch(){ }

double MaxExpectGlobalSearch::UpdateExScore(const SymbolicExecution ex){
  double maxScore = 0.0;
  vector<branch_id_t>temp_branches_ = ex.path().branches();
  vector<size_t>idx = ex.path().constraints_idx();

  for(size_t i = 0 ; i < ex.path().constraints().size(); i++){
    size_t bidx = idx[i];
    branch_id_t bid = temp_branches_[bidx];
    if(maxScore < dist_[paired_branch_[bid]]){
    	maxScore = dist_[paired_branch_[bid]];
    }
  }
  return maxScore;	
}

void MaxExpectGlobalSearch::PrintAllEx(const vector<ExpectScoredBranch> scoredExsID) {
   fprintf(out,"\nExecutions (vector) exs:\n");
     fprintf(stderr,"\nExecutions (vector) exs:\n");
   for(vector<ExpectScoredBranch>::const_iterator it = scoredExsID.begin(); it != scoredExsID.end(); it++){
      fprintf(out,"execute orders %d, score %f: \nPath:\n",it->first,it->second);
      fprintf(stderr,"execute orders %d, score %f: \nPath:\n",it->first,it->second);
      for(vector<branch_id_t>::const_iterator iter = exs[it->first].path().branches().begin(); 
      iter != exs[it->first].path().branches().end(); iter++){
              fprintf(out,"%d: ",*iter);
              fprintf(stderr,"%d: ",*iter);
      }
      fprintf(out,"\n");
      fprintf(stderr,"\n");
   }
   fprintf(out,"\n");
   fprintf(stderr,"\n");
}

void MaxExpectGlobalSearch::Run() {

  vector<int> penalty(max_iters_,0);
  vector<double> score(max_iters_,0.0);
  double tempScore = 0.0;
  

  
  SymbolicExecution ex;
  while (true) {
//   covered_.assign(max_branch_, false);
//    num_covered_ = 0;
    exs.clear();
    penalty.clear();
    score.clear();

      // Execution on empty/random inputs.
    fprintf(stderr, "RESET New\n");
    fprintf(out, "RESET\n");
    RunProgram(vector<value_t>(), &ex);
    if (UpdateCoverage(ex)) {
      UpdateBranchScore(); //modified by dqx
      PrintStats();
//    PrintAllEx();
    }

    exs.push_back(ex);
    fprintf(stderr, "exs size %d\n",exs.size());
    

    
    size_t index = 0;
    while(true){
      bool hasNewBranch = DoSearch(5, 30, 0, ex);  
      ex.Swap(exs[index]);
      if(hasNewBranch){
        // As long as we keep finding new branches . . . .
        UpdateBranchScore();
        exs.push_back(success_ex_);
      } else{
        penalty[index] += 1;       
      }
      vector<ExpectScoredBranch> scoredExsID(exs.size());
      for (size_t i = 0; i < scoredExsID.size(); i++) {
       scoredExsID[i].first = i;
       tempScore = UpdateExScore(exs[i]);
       if(penalty[i] > 0){
         if(fabs(tempScore - score[i])>0.00001){
           scoredExsID[i].second = tempScore;
           penalty[i] = 0;
         }else{
           scoredExsID[i].second = 0.0;
         }
       }else{
       	 scoredExsID[i].second = tempScore;
       }
       score[i] = tempScore;
      }
      random_shuffle(scoredExsID.begin(), scoredExsID.end());
      stable_sort(scoredExsID.begin(), scoredExsID.end(), ExpectScoredBranchComp());
      fprintf(stderr,"in run 1\n");
      PrintStats();
      PrintAllEx(scoredExsID);
      
      index  = scoredExsID.front().first;
      if(scoredExsID.front().second <= 0)
        break;
      fprintf(out,"ex index:%d",index);
      ex.Swap(exs[index]);
    }
    PrintStats();
  }
}

IcfgMaxExpectLocalSearch::IcfgMaxExpectLocalSearch(const string& program, int max_iterations) 
  : MaxExpectLocalSearch(program,  max_iterations){
  
  ifstream in("icfg_branches", ios::in | ios::binary);
  assert(in);
  size_t num_branches;
  in.read((char*)&num_branches, sizeof(num_branches));
  //assert(num_branches == branches_.size());
  fprintf(stderr,"ICFG branches number: %d\n",num_branches);///////////////////
  fprintf(out,"ICFG branches number: %d\n",num_branches);///////////////////
  for (size_t i = 0; i < num_branches; i++) {
    branch_id_t src;
    size_t len;
    in.read((char*)&src, sizeof(src));
    in.read((char*)&len, sizeof(len));
    if(icfg_.size()<=(unsigned)src)
      icfg_.resize(src+1);
    icfg_[src].resize(len);
    in.read((char*)&icfg_[src].front(), len * sizeof(branch_id_t));


    fprintf(out,"src %d :",src);//DEBUG
    fprintf(stderr,"src %d :",src);//DEBUG
    for(vector<branch_id_t>::const_iterator it = icfg_[src].begin();it != icfg_[src].end(); ++it){//DEBUG
       fprintf(out," %d",*it);//DEBUG
       fprintf(stderr," %d",*it);//DEBUG
    }
    fprintf(out,"\n");//DEBUG
    fprintf(stderr,"\n");//DEBUG
  }
  in.close();

  // Construct the reversed ICFG.
  size_t index = 1;
  size_t count= 0; //size_t
  while(count < num_branches && (unsigned)index < icfg_.size()) {
    while(icfg_[index].size() <= 0 && index < icfg_.size()){
      index++;
      //fprintf(stderr,"index %d :",index);//DEBUG
    }
    if( index >= icfg_.size()){
      break;
    }
    fprintf(stderr,"index %d \n",index);//DEBUG
    if(icfg_[index].size()>0){
      for (BranchIt j = icfg_[index].begin(); j != icfg_[index].end(); ++j) {
        icfg_rev_[*j].push_back(index);
      }
      count++;
    }
  }
  in.open("branch_map");
  int oldId,newId;
  in >> new_branch_num_;
//  vector<branch_id_t> temp_branch;
  while (in >> newId >> oldId) {
    if(branch_map_.size() <= (unsigned)newId){
      branch_map_.resize(newId + 1);
    }
    branch_map_[newId] = oldId;
 //   temp_branch.push_back(newId);
    if(new_max_branch_ < newId)
      new_max_branch_ = newId;
  }
  new_max_branch_ ++;
  in.close();
  
 
  fprintf(out, "read new paired branch.\n");
  fprintf(stderr, "read new paired branch.\n");
  in.open("branch_pairs",std::ios::in);
  int num_paired_branches;
  in>>num_paired_branches;
  fprintf(stderr,"branch paired:%d,branch size get from icfg=%d\n",num_paired_branches,num_branches);
  fprintf(out,"branch paired:%d,branch size get from icfg=%d\n",num_paired_branches,num_branches);
  //assert(num_paired_branches*2 == num_branches);
  for(size_t i = 0; i < (unsigned)num_paired_branches; i++){
    branch_id_t b1,b2;
    in>>b1>>b2;
    branch_id_t max = b1>b2?b1:b2;
    if(new_paired_branch_.size() <= (unsigned)max){
      new_paired_branch_.resize(max+1);
    }
    new_paired_branch_[b1] = b2;
    new_paired_branch_[b2] = b1;
  }
  in.close();
}


double IcfgMaxExpectLocalSearch::DFSBranchScore(branch_id_t branch, set<branch_id_t> path) { 

//  if(path.find(branch) != path.end())
//       return 0.0;
  if(dist_[branch] >= 0.0) return dist_[branch];
  if(icfg_[branch].size() == 0 || path.find(branch) != path.end()){
     //if(!total_covered_[branch]){
     if(!total_covered_[branch_map_[branch]]){
     	return 1.0;
     }else{
        return 0.0;
     }  

  }
  double totalScore =0.0;
  int count = 0;
  bool isEqual = true;
  for (BranchIt j = icfg_[branch].begin(); j != icfg_[branch].end(); ++j, count++) {
      set<branch_id_t> newPath(path);
      newPath.insert(branch);
      double tempScore = DFSBranchScore(*j,newPath);
      totalScore += tempScore;
      if(fabs(totalScore - tempScore * count)>0.00001){
        isEqual = false;
      }
  }
  totalScore /= icfg_[branch].size();
  if(!total_covered_[branch_map_[branch]]){
	totalScore += 1;
  }else{
    if(isEqual){
      totalScore *= 0.75;
    }
  }
  dist_[branch] = totalScore;
  return totalScore;
}

double IcfgMaxExpectLocalSearch::UpdateBranchScore(){
  fprintf(out, "Expect Value in UpdateBranchScore(IcfgMaxExpectLocalSearch):\n");
  double maxScore = 0.0;
  for (hash_map<int,int>::const_iterator i = branch_map_.begin(); i != branch_map_.end(); ++i) {
  
    
    if(dist_.size() <= (unsigned)i->first)
      dist_.resize(i->first + 1);
    dist_[i->first] = -1;
  }
  for (hash_map<int,int>::const_iterator i = branch_map_.begin(); i != branch_map_.end(); ++i) {
    set<branch_id_t> path;
    dist_[i->first] = DFSBranchScore(i->first,path);
    if(dist_[i->first]>maxScore)
       maxScore = dist_[i->first];
    fprintf(out, "new branch %d(old %d):score %f  ", i->first, i->second, dist_[i->first]);
  }
    fprintf(out, "\n");
  return maxScore;
}

void IcfgMaxExpectLocalSearch::MapBranch(const SymbolicExecution& ex, vector<branch_id_t>* new_branches_){
  fprintf(out,"call MapBranch in(IcfgMax..Local..)\n");
  fprintf(stderr,"call MapBranch in(IcfgMax..Local..)branch_map_ size:%d\n",branch_map_.size());
  new_branches_->clear();
//  new_branches_->resize(ex.path().branches().size());
  hash_map<branch_id_t,branch_id_t>::const_iterator branch_map_it = branch_map_.begin();
//  vector<nbhr_list_t>::const_iterator icfg_it = icfg_.begin();
  for(branch_map_it = branch_map_.begin(); branch_map_it != branch_map_.end(); branch_map_it++){
    fprintf(out,"%d(%d) ", branch_map_it->first, branch_map_it->second);
    fprintf(stderr,"%d(%d) ", branch_map_it->first, branch_map_it->second);
  }
  fprintf(out,"\n path(%zu):\n",ex.path().branches().size());
  fprintf(stderr,"\n path(%zu):\n",ex.path().branches().size());
/*  branch_map_it = branch_map_.begin();
  for(vector<branch_id_t>::const_iterator it = ex.path().branches().begin(); it != ex.path().branches().end(); ++it){
    if(*it > 0){
      while(*it != branch_map_it->second){
         branch_map_it++;
         if(branch_map_it == branch_map_.end())
           break;
      }
      if(branch_map_it == branch_map_.end())
           break;
      new_branches_->push_back(branch_map_it->first);
    }else{
      new_branches_->push_back(*it);
    }
  	fprintf(out,"%d(%d) ", branch_map_it->first, *it);
  	fprintf(stderr,"%d(%d) ", branch_map_it->first, *it);
  }
  fprintf(out,"\n");*/
  

  bool isFirst_ = true;
  bool isUnknown = false;
  size_t unknownCall = 0;
  int icfg_index_ = 1;
  int old_index_ = 1;
  vector<branch_id_t> next_branches_; 
  for(vector<branch_id_t>::const_iterator it = ex.path().branches().begin(); it != ex.path().branches().end(); ++it){
    fprintf(stderr,"(%d)", *it);
    if(*it > 0){
      if(isUnknown){
        new_branches_->push_back(0);
      }else if(isFirst_){
        isFirst_ = false;
        while(*it != branch_map_[icfg_index_]){
          icfg_index_++;
          if(icfg_index_ >= new_max_branch_){
            fprintf(stderr, "out of icfg_ size:%d",icfg_.size());
            fprintf(out, "out of icfg_ size:%d",icfg_.size());
            break;
          }
        }
        if(*it != branch_map_[icfg_index_]){
          isUnknown = true;
          new_branches_->push_back(0);
          vector<branch_id_t>::const_iterator temp_it = it -1;
          while(*temp_it==-1 && temp_it !=ex.path().branches().begin()){
            unknownCall ++;
            temp_it--;
          }
        }else{
          assert(*it == branch_map_[icfg_index_]);
          old_index_ = icfg_index_;
          vector<branch_id_t> temp_branches_(icfg_[icfg_index_]);
          next_branches_.swap(temp_branches_);
          next_branches_.push_back(icfg_index_);
          
          new_branches_->push_back(icfg_index_);
        }
      }else{
        //assert(next_branches_.size()>0);
        vector<branch_id_t>::const_iterator branch_it;
        for( branch_it = next_branches_.begin(); branch_it != next_branches_.end(); branch_it ++){
          if(*it == branch_map_[*branch_it]){
            break;
          }
        }
        if(*it != branch_map_[*branch_it]){
          isUnknown = true;
          new_branches_->push_back(0);
          vector<branch_id_t>::const_iterator temp_it = it -1;
          while(*temp_it==-1 && temp_it !=ex.path().branches().begin()){
            unknownCall ++;
            temp_it--;
          }
        }else{
          assert(*it == branch_map_[*branch_it]);
          old_index_ = icfg_index_;
          
          vector<branch_id_t> temp_branches_(icfg_[*branch_it]);
          next_branches_.swap(temp_branches_);
          next_branches_.push_back(*branch_it);
          
          new_branches_->push_back(*branch_it);
        }
      }
    }else{
      if(isUnknown){
        if(*it==-1){
          unknownCall++;
        }else{
          unknownCall--;
          if(unknownCall == 0){
           isUnknown = false;
           isFirst_ = true;
           icfg_index_ = old_index_;
          }
        }
      }
      new_branches_->push_back(*it);
    }
  	fprintf(out,"%d(%d) ", (*new_branches_)[it-ex.path().branches().begin()], *it);
  	fprintf(stderr,"%d(%d) ", (*new_branches_)[it-ex.path().branches().begin()], *it);
  }
  fprintf(out,"\n");
  
  //check 
  for(size_t i = 0; i < new_branches_->size(); i++){
    if((*new_branches_)[i]>0){
      if(branch_map_[(*new_branches_)[i]] != ex.path().branches()[i]){
      	fprintf(out,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
  	fprintf(stderr,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
      }
    }else if(ex.path().branches()[i] > 0){
      fprintf(out,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
      fprintf(stderr,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
    }
  }
}

IcfgMaxExpectGlobalSearch::IcfgMaxExpectGlobalSearch(const string& program, int max_iterations) 
  : MaxExpectGlobalSearch(program,  max_iterations){
  
  ifstream in("icfg_branches", ios::in | ios::binary);
  assert(in);
  size_t num_branches;
  in.read((char*)&num_branches, sizeof(num_branches));
  //assert(num_branches == branches_.size());
  fprintf(stderr,"ICFG branches number: %d\n",num_branches);///////////////////
  fprintf(out,"ICFG branches number: %d\n",num_branches);///////////////////
  for (size_t i = 0; i < num_branches; i++) {
    branch_id_t src;
    size_t len;
    in.read((char*)&src, sizeof(src));
    in.read((char*)&len, sizeof(len));
    if(icfg_.size() <= (unsigned)src){
      icfg_.resize(src+1);
    }
    icfg_[src].resize(len);
    in.read((char*)&icfg_[src].front(), len * sizeof(branch_id_t));

    fprintf(out,"src %d (%d):",src,len);//DEBUG
    for(vector<branch_id_t>::const_iterator it = icfg_[src].begin();it != icfg_[src].end(); ++it){//DEBUG
       fprintf(out," %d",*it);//DEBUG
    }
    fprintf(out,"\n");//DEBUG
  }
  in.close();

  // Construct the reversed ICFG.
  size_t index = 1;
  size_t count= 0;
  while(count < num_branches && index < icfg_.size()) {
    while(icfg_[index].size() <= 0 && index < icfg_.size()){
      index++;
    }
    if(index >= icfg_.size())
      break;
    if(icfg_[index].size()>0){
      for (BranchIt j = icfg_[index].begin(); j != icfg_[index].end(); ++j) {
        icfg_rev_[*j].push_back(index);
      }
      count++;
    }
  }
  
  in.open("branch_map");
  int oldId,newId;
  in >> new_branch_num_;
  vector<branch_id_t> temp_branch;
  while (in >> newId >> oldId) {
    if(branch_map_.size() <= (unsigned)newId){
      branch_map_.resize(newId + 1);
    }
    branch_map_[newId] = oldId;
    temp_branch.push_back(newId);
    if(new_max_branch_ < newId)
      new_max_branch_ = newId;
  }
  new_max_branch_ ++;
  in.close();
  
 
  fprintf(out, "read new paired branch.\n");
  fprintf(stderr, "read new paired branch.\n");
  in.open("branch_pairs",std::ios::in);
  int num_paired_branches;
  in>>num_paired_branches;
  assert(unsigned (num_paired_branches*2) == num_branches);
  for(size_t i = 0; i < (unsigned)num_paired_branches; i++){
    branch_id_t b1,b2;
    in>>b1>>b2;
    branch_id_t max = b1>b2?b1:b2;
    if(new_paired_branch_.size() <= (unsigned)max){
      new_paired_branch_.resize(max+1);
    }
    new_paired_branch_[b1] = b2;
    new_paired_branch_[b2] = b1;
  }
  in.close();
}

double IcfgMaxExpectGlobalSearch::DFSBranchScore(branch_id_t branch, set<branch_id_t> path) { 


  if(dist_[branch] >= 0.0) return dist_[branch];
  if(icfg_[branch].size() == 0 || path.find(branch) != path.end()){
     //if(!total_covered_[branch]){
     if(!total_covered_[branch_map_[branch]]){
     	return 1.0;
     }else{
        return 0.0;
     }  

  }
  double totalScore =0.0;
  int count = 0;
  bool isEqual = true;
  for (BranchIt j = icfg_[branch].begin(); j != icfg_[branch].end(); ++j, count++) {
      set<branch_id_t> newPath(path);
      newPath.insert(branch);
      double tempScore = DFSBranchScore(*j,newPath);
      totalScore += tempScore;
      if(fabs(totalScore - tempScore * count)>0.00001){
        isEqual = false;
      }
  }
  totalScore /= icfg_[branch].size();
  if(!total_covered_[branch_map_[branch]]){
	totalScore += 1;
  }else{
    if(isEqual){
      totalScore *= 0.75;
    }
  }
  dist_[branch] = totalScore;
  return totalScore;
}
double IcfgMaxExpectGlobalSearch::UpdateBranchScore(){
  fprintf(out, "Expect Value in UpdateBranchScore(IcfgMaxExpectGlobalSearch):\n");
  double maxScore = 0.0;
  for (hash_map<int,int>::const_iterator i = branch_map_.begin(); i != branch_map_.end(); ++i) {
 
    if(dist_.size() <= (unsigned)i->first)
      dist_.resize(i->first + 1);
    dist_[i->first] = -1;
  }
  for (hash_map<int,int>::const_iterator i = branch_map_.begin(); i != branch_map_.end(); ++i) {
    set<branch_id_t> path;
    dist_[i->first] = DFSBranchScore(i->first,path);
    if(dist_[i->first]>maxScore)
       maxScore = dist_[i->first];
    fprintf(out, "new branch %d(old %d):score %f  ", i->first, i->second, dist_[i->first]);
  }
    fprintf(out, "\n");
  return maxScore;
}

double IcfgMaxExpectGlobalSearch::UpdateExScore(const SymbolicExecution ex){
  double maxScore = 0.0;
  vector<branch_id_t>new_branches_;
  vector<size_t> idx = ex.path().constraints_idx();
  MapBranch(ex, &new_branches_);

  for(size_t i = 0 ; i < ex.path().constraints().size(); i++){
    size_t bidx = idx[i];
    branch_id_t bid = new_branches_[bidx];
    if(maxScore < dist_[new_paired_branch_[bid]]){
    	maxScore = dist_[new_paired_branch_[bid]];
    }
  }
  return maxScore;	
}

void IcfgMaxExpectGlobalSearch::MapBranch(const SymbolicExecution& ex, vector<branch_id_t>* new_branches_){
  fprintf(out,"call MapBranch in(IcfgMax..global..)branch_map_ size:%d\n",branch_map_.size());
  fprintf(stderr,"call MapBranch in(IcfgMax..global..)branch_map_ size:%d\n",branch_map_.size());
  new_branches_->clear();
//  new_branches_->resize(ex.path().branches().size());
//  vector<nbhr_list_t>::const_iterator icfg_it = icfg_.begin();
  hash_map<branch_id_t,branch_id_t>::const_iterator branch_map_it = branch_map_.begin();
//  vector<nbhr_list_t>::const_iterator icfg_it = icfg_.begin();
  for(branch_map_it = branch_map_.begin(); branch_map_it != branch_map_.end(); branch_map_it++){
    fprintf(out,"%d(%d) ", branch_map_it->first, branch_map_it->second);
    fprintf(stderr,"%d(%d) ", branch_map_it->first, branch_map_it->second);
  }
  fprintf(out,"\n");
  fprintf(stderr,"\n path:\n");
/*  branch_map_it = branch_map_.begin();
  for(vector<branch_id_t>::const_iterator it = ex.path().branches().begin(); it != ex.path().branches().end(); ++it){
    if(*it > 0){
      while(*it != branch_map_it->second){
         branch_map_it++;
         if(branch_map_it == branch_map_.end())
           break;
      }
      if(branch_map_it == branch_map_.end())
           break;
      new_branches_->push_back(branch_map_it->first);
    }else{
      new_branches_->push_back(*it);
    }
  	fprintf(out,"%d(%d) ", branch_map_it->first, *it);
  	fprintf(stderr,"%d(%d) ", branch_map_it->first, *it);
  }
  fprintf(out,"\n");*/
    

  bool isFirst_ = true;
  int icfg_index_ = 1;
  vector<branch_id_t> next_branches_; 
  for(vector<branch_id_t>::const_iterator it = ex.path().branches().begin(); it != ex.path().branches().end(); ++it){
    if(*it > 0){
      if(isFirst_){
        isFirst_ = false;
        while(*it != branch_map_[icfg_index_]){
          icfg_index_++;
          if(icfg_index_ >= new_max_branch_){
            fprintf(stderr, "out of icfg_ size:%d",icfg_.size());
            fprintf(out, "out of icfg_ size:%d",icfg_.size());
            icfg_index_ = 1;
            it++;
            break;
          }
        }
        assert(*it == branch_map_[icfg_index_]);
        vector<branch_id_t> temp_branches_(icfg_[icfg_index_]);
        next_branches_.swap(temp_branches_);
        next_branches_.push_back(icfg_index_);
        new_branches_->push_back(icfg_index_);
      }else{
        assert(next_branches_.size()>0);
        vector<branch_id_t>::const_iterator branch_it;
        for( branch_it = next_branches_.begin(); branch_it != next_branches_.end(); branch_it ++){
          if(*it == branch_map_[*branch_it]){
            break;
          }
        }
        assert(*it == branch_map_[*branch_it]);
        new_branches_->push_back(*branch_it);
        vector<branch_id_t> temp_branches_(icfg_[*branch_it]);
        
        next_branches_.swap(temp_branches_);
        next_branches_.push_back(*branch_it);
      }
    }else{
      new_branches_->push_back(*it);
    }
  	fprintf(out,"%d(%d) ", (*new_branches_)[it-ex.path().branches().begin()], *it);
  	fprintf(stderr,"%d(%d) ", (*new_branches_)[it-ex.path().branches().begin()], *it);
  }
  fprintf(out,"\n");
  
  //check 
  for(size_t i = 0; i < new_branches_->size(); i++){
    if((*new_branches_)[i]>0){
      if(branch_map_[(*new_branches_)[i]] != ex.path().branches()[i]){
      	fprintf(out,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
  	fprintf(stderr,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
      }
    }else if(ex.path().branches()[i] > 0){
      fprintf(out,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
      fprintf(stderr,"got wrong branch map at %d,old %d,new %d\n",i,ex.path().branches()[i],(*new_branches_)[i]);
    }
  }
}
}  // namespace crest
