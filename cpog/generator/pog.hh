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


#pragma once

// Don't want any type to evaluate to 0
typedef enum { POG_NONE, POG_TRUE, POG_FALSE, POG_AND, POG_OR, POG_SKOLEM } pog_type_t;

#include <vector>
#include <unordered_set>
#include <stdio.h>
#include "clausal.hh"
#include "cnf_opt.hh"
#include "writer.hh"


// POG Nodes
class Pog_node {
private:
    // Basic representation
    pog_type_t type;
    // Extension variable for node
    int xvar;

    // Identify children by their representation as literals
    // Can be variable, other Pog node, or the negation of one of these
    // Organize so that literals representing nodes come at end
    // AND node can have any degree >= 2
    // OR  node must have degree 2,
    int degree;
    int *children;

    // Id of first clause in declaration
    int defining_cid;

    // Lemma support
    int indegree;
    Lemma_instance *lemma;

    // Measures for deciding when to justify monolithically
    long tree_size;

public:
    Pog_node();

    Pog_node(pog_type_t ntype);

    Pog_node(pog_type_t ntype, size_t xvar);

    ~Pog_node();

    void set_type(pog_type_t t);
    pog_type_t get_type();
    void set_xvar(int var);
    int get_xvar();
    void set_defining_cid(int cid);
    int get_defining_cid();
    long get_tree_size();
    void set_tree_size(long size);

    // Store name in local buffer.
    const char *name();

    // Set degree and import children
    void add_children(std::vector<int> *cvec);

    void show(FILE *outfile);

    // Access children
    int get_degree();
    int& operator[](int);
    int *get_children();

    // Lemma support
    void increment_indegree();
    // Does this node meet criteria for having a lemma?
    bool want_lemma();
    void add_lemma(Lemma_instance *lemma);
    Lemma_instance *get_lemma();

};

// POG
class Pog {
private:
    // Current CNF + proof generation support
    Cnf_reasoner *cnf;
    // Don't generate proof of mutual exclusion
    bool no_mutex;
    int max_input_var;
    // First extension variable.  Either max_input_var+1  or max_input_var+2
    int start_extension_var;
    std::vector<Pog_node *> nodes;
    // Root literal can refer to either an input variable or the last node
    int root_literal;
    // Ratio of tree size to dag size
    double tree_ratio;

public:
    Pog();

    Pog(Cnf_reasoner *cset, bool no_mutex);

    void clear();

    // Readers
    bool read_pog(FILE *infile);
    bool read_ddnnf(FILE *infile);
    bool read_d4ddnnf(FILE *infile);

    int add_node(Pog_node *np);

    void set_root(int rlit);
    int get_root();

    // Does literal refer to an input variable or a node
    bool is_node(int lit);
    // Does literal refer to a node of specified type
    bool is_node_type(int lit, pog_type_t type);


    // Index POG nodes by their extension variables
    Pog_node * get_node(int var);
    Pog_node * operator[](int);

    int node_count();

    void show(FILE *outfile);

    // Generate proof that formula unsatisfiable
    void justify_unsatisfiable();

    // At each position in POG, generate justification within context
    // Return ID of justifying clause
    // Set splitting_literal to 0 when not argument of OR operation
    int justify(int rlit, int splitting_literal, bool use_lemma);

    // Enumerate clauses in subgraph
    // These get simplified according to unit literals
    // Track which ones have been exported to avoid repetitions when there are shared subgraphs
    void export_subgraph(int rlit, Cnf_reduced *rcnf, std::unordered_set<int> *unit_literals, std::unordered_set<int> &sofar, bool positive_only);

    // Same thing.  Different representation
    void export_subgraph(int rlit, Cnf_opt *opt_cnf, std::unordered_set<int> &sofar, bool positive_only);

    // Justify subgraph using single call to SAT solver.
    // Return ID of justifying clause
    int justify_monolithic(int rlit, int splitting_literal);
    
    bool delete_input_clauses(int unit_cid);

    bool is_projection_literal(int lit) { return data_variables && data_variables->find(IABS(lit)) == data_variables->end(); }

    std::unordered_set<int> *data_variables;

private:
    // Compress and order nodes.
    // If optimize:
    //   Simplify POG by eliminating constants,
    //    eliminating common subnodes, etc.
    //   If data_variables nonempty, prepare for Skolemization:
    //   Allocate mode variable
    //   Generate Skolem nodes from AND nodes
    //   Renumber Ids to be consecutive
    //   Return false if something wrong with original POG
    bool compress(bool optimize);
    void justify_mutex(Pog_node *np, std::vector<int> &hints);
    // Add POG declarations to file
    void concretize();
    // Helper routines
    void topo_order(int rlit, std::vector<int> &rtopo, int *markers);
    // Finding splitting literal for two arguments to OR operation (based on phase of first argument)
    int find_splitting_literal(int rlit1, int rlit2);
    // Recursively descend Pog until find input literal
    int first_literal(int rlit);
    // Create/Apply lemma at node.  Return ID of justifying clause (0 if failed)
    int apply_lemma(Pog_node *rp, int splitting_literal);
    // For generating counterexample when input deletion fails
    bool get_deletion_counterexample(int cid, std::vector<bool> &implies_clause, std::vector<int> &literals);
    bool delete_input_clause(int cid, int unit_cid, Literal_set &lset, std::vector<int> &overcount_literals);
    bool delete_input_clauses_rup(int unit_cid);

};
