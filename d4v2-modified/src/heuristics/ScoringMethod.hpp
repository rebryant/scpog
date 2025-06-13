/*
 * d4
 * Copyright (C) 2020  Univ. Artois & CNRS
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program.  If not, see <http://www.gnu.org/licenses/>.
 */
#pragma once
#include <boost/program_options.hpp>
#include <src/problem/ProblemTypes.hpp>
#include <src/solvers/ActivityManager.hpp>
#include <src/solvers/WrapperSolver.hpp>
#include <src/specs/SpecManager.hpp>
#include <vector>

namespace d4 {
namespace po = boost::program_options;
class ScoringMethod {
 public:
  static ScoringMethod *makeScoringMethod(po::variables_map &vm, SpecManager &p,
                                          ActivityManager &am,
                                          std::ostream &out);
  virtual ~ScoringMethod() { ; }
  virtual double computeScore(Var v) = 0;
  virtual void postProcess(Var v) {}

  Var selectVariable(std::vector<Var> &vars, SpecManager &s,
                     std::vector<bool> &isDecisionVariable);
  Var selectVariableWeighted(std::vector<Var> &vars, SpecManager &s,
			     std::vector<bool> &isDecisionVariable,
			     std::vector<bool> &isWeakVariable, double weakWeight);

};
}  // namespace d4
