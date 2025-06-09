/*========================================================================
  Copyright (c) 2022, 2023 Randal E. Bryant, Carnegie Mellon University
  
  Permission is hereby granted, free of charge, to any person
  obtaining a copy of this software and associated documentation files
  (the "Software"), to deal in the Software without restriction,
  including without limitation the rights to use, copy, modify, merge,
  publish, distribute, sublicense, and/or sell copies of the Software,
  and to permit persons to whom the Software is furnished to do so,
  subject to the following conditions:
  
  The above copyright notice and this permission notice shall be
  included in all copies or substantial portions of the Software.
  
  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
  BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
  ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
  CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.
  ========================================================================*/


// Code to compress clausal representation of formula
// Assumes start with 

#pragma once

#include "clausal.hh"

class Cnf_opt {

 private:

    // Encountered conflict during unit propagation
    bool has_conflict;

    // Variables that cannot be optimized away
    std::unordered_set<int> *keep_variables;
    
    // Unit literals for kept variables (after unit propagation)
    // These are not included in the clauses
    std::vector<int> unit_keep_literals;

    // Non-unit clauses (once unit propagation completed)
    std::vector<Clause *> clauses;
    
    // Mapping from literals to the clauses containing them
    // Use direct pointer to clause, rather than clause Id
    std::unordered_map<int, std::unordered_set<Clause *>*> literal_map;

    // Hash table for clauses.
    // Can lookup clause based on its hash
    // Use multimap to deal with hash collisions
    std::unordered_multimap<unsigned, Clause*> clause_lookup;

 public:
    Cnf_opt(std::unordered_set<int> *keep_variables);

    ~Cnf_opt();

    void clear();

    // Return true if clause actually added.  False if it is a duplicate
    bool add_clause(Clause *cp);
    
    void delete_clause(Clause *cp);

    void show(FILE *outfile);

    void optimize();

 private:
    int is_keep_literal(int lit) { return keep_variables->find(IABS(lit)) != keep_variables->end(); }

    void cause_conflict();

    bool unit_propagate();

    Clause *resolve(int var, Clause *pos_cp, Clause *neg_cp);

    bool ordered_bve(int max_degree, int max_variable);

    // Eliminate null clauses.  Return maximum variable Id encountered
    int compact_clauses();

};
