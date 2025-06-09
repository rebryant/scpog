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

// SOLVER options

// Cadical.  Generate DRAT
#define CADICAL 1
// Cadical.  Generate LRAT
#define LCADICAL 2
// Cadical.  Generate LRAT and trim with lrat-trim
#define TCADICAL 3
// KISSAT.  Generate DRAT
#define KISSAT  4

#ifndef SOLVER
#define SOLVER TCADICAL
#endif

// Enable/disable more info in file comments
#ifndef DEBUG
#define DEBUG 0
#endif

// Enable/disable consistency checking with two-watch literals
#ifndef TWL_CHECK
#define TWL_CHECK 0
#endif

// optionally disable high verbosity
#ifndef VLEVEL
#define VLEVEL 3
#endif

// Disable code that deleted clauses in reverse order
#define DELETE_FULL 0

// Used to convert literal to variable
#define IABS(x) ((x)<0?-(x):(x))

// Used to convert variable to literal of specified phase
#define MATCH_PHASE(v,p) ((p)<0?-(v):(v))

#include <vector>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <map>
#include <stdio.h>
#include <fstream>
#include <limits>

#include "ilist.h"
#include "writer.hh"

// Pairs of literals for two-watched literals
struct Literal_pair {
    int lit1;
    int lit2;
};

// Representations of clauses and sets of clauses

/* Special value when unit propagation finds a conflict */
#define CONFLICT_LIT INT_MIN


// Clause is a vector of literals, each of which is a negative or positive integer.
// Tautologies are detected and represented as clause of the form -x, x
// When asserting contexts,
//   clauses are maintained so that the first two positions are unsatisfiable, if possible

class Clause {
private:
    ilist contents;
    bool is_tautology;
    bool canonized;
    // When clause created to serve as argument to lemma, it will
    // have an associated literal that will enable (set literal true) / disable (set literal false) the clause
    // Regular input clauses have activating literal = 0
    int activating_literal;

public:

    Clause();

    Clause(int *array, size_t len);

    Clause(FILE *infile, bool from_proof, bool *eof);

    Clause (Clause *np);

    Clause (int lit);

    ~Clause();

    void add(int val);

    size_t length();

    bool tautology();

    int max_variable();

    void swap_literals(int idx1, int idx2);

    void rearrange(Literal_pair &lits);

    void canonize();

    void make_tautology();

    void show(char *fname);

    void show();

    void show(std::ofstream &outstream);

    void show(FILE *outfile);

    // Show clause, but with literal asserted
    void show_reduced(FILE *outfile, int ulit);

    void write(Writer *writer);

    int *data();

    int& operator[](int);

    void set_activating_literal(int alit);

    int get_activating_literal();
    
    // Simplify a clause according to a set of assigned literals
    // Return NULL if clause becomes satisfied
    // Return original if clause unchanged
    // Otherwise, return remaining active literals
    ilist simplify(std::unordered_set<int> &unit_literals);    

    // Compute a hash signature for the clause
    unsigned hash();

    // Compare with other clause for equality
    bool is_equal(Clause *op);

    // Given array mapping (decremented) variable to 0/1
    // determine if clause satisfied
    bool satisfied(char *assignment);

    // Properties
    bool contains(int lit);

    // Build set representation
    void build_set(std::unordered_set<int> &dict);
};

// Representation of a set of literals for efficient containment checking
class Literal_set {
private:
    std::vector<int> last_gen;
    int current_generation;

public:
    Literal_set(int nvar);
    void load_clause(Clause *cp);
    bool contains(int lit);
};

// Base class Cnf is a collection of clauses.  Can read from a DIMACS format CNF file
// Also can read DRAT format proofs
class Cnf {

private:
    
    int max_input_var;
    // Don't set this externally
    bool read_failed;


public:

    bool proof_failed;

    // Basic representation.
    // Should only be accessed by a superclass, but C++ doesn't provide this level of control
    std::vector<Clause *> clauses;

    Cnf();

    // Read clauses DIMACS format CNF file or DRAT file
    Cnf(FILE *infile);

    ~Cnf();

    // Did last read fail?
    bool failed();

    // Generate DIMACS CNF representation to stdout, outfile, or outstream
    void show();
    void show(FILE *outfile);
    void show(std::ofstream &outstream);
    void show(Cnf_writer *cwriter);

    // Return number of (input) clauses
    size_t clause_count();

    // Return ID of maximum (input) variable encountered
    int max_variable();

    // Given array mapping (decremented) variable to 0/1
    // determine if every clause satisfied.
    // If not, return ID of first offending clause.  Otherwise return 0
    int satisfied(char *assignment);

    Clause * get_input_clause(int cid);

    // Access input clause, with id 1 being first input clause
    Clause * operator[](int);    

    // Compute hash of set of clauses
    unsigned hash();

    // Semi-private methods for general CNF
    // Add a new clause
    void add(Clause *clp);

    // Public access to extra information
    // For projected knowledge compilation, all variables that are NOT quantified
    std::unordered_set<int> *data_variables;
    
};

// Special version of CNF that can store a reduced version of some larger CNF file
// where a set of unit literals simplifies clauses.
class Cnf_reduced : public Cnf {

    // Temporary files that have been created during proof generation
    std::vector<const char *> file_names;
    
    // Map from local clause Id back to originating clause Id
    std::unordered_map<int,int> inverse_cid;

    // When empty clause gets added to CNF
    bool unsatisfiable;
    // Id of added empty clause
    int unsatisfiable_id;

    std::vector<Clause *> proof_clauses;
    int emitted_proof_clauses;

    std::vector<Clause *> proof_hints;

public:

    Cnf_reduced();
    
    ~Cnf_reduced();

    const char* get_file_name();

    // Delete intermediate files
    bool delete_files;

    // Add clause.  It will be simplified according to the context
    void add_clause(Clause *np, std::unordered_set<int> &unit_literals, int cid);
    
    // Generate output file.  Overloads one from Cnf
    void show(FILE *outfile);

    // Run SAT solver.
    // Save away generated proof clauses
    // Return true if successful
    bool run_solver();

    // Perform bounded variable elimination.
    // Assume clauses ordered so that can make single pass
    // max_degree indicates maximum allowed clause expansion as m*m-(m+m)
    // Create fresh CNF representation
    // Current implementation does not justify what it's doing
    void ordered_bve(int max_degree, std::unordered_set<int> *keep_variables, Cnf *new_cnf);

    // Read proof clauses + hints in LRAT format.
    // Ignore deletions
    // Return true if successful
    bool load_hinted_proof(FILE *infile);

    // Run SAT solver + checker
    // Save away generated proof clauses + hints
    // Return true if successful
    bool run_hinting_solver();

    // Retrieve next clause in proof.
    // Remap hint clause Ids to ones that match those in the larger proof
    // 
    // Be sure to retrieve the hint before the proof clause
    // start_id should be Id for first clause in proof sequence
    Clause *get_proof_hint(int start_id);

    // Retrieve next clause in proof.  Convert it to one usable by parent solver
    Clause *get_proof_clause(std::vector<int> *prefix);

    int get_proof_size() { return proof_clauses.size(); }
};
 
// Information required to generate and apply lemmas
class Lemma_instance {

public:
    // Is there a splitting variable?
    int splitting_literal;
    // Mapping from lemma argument clause IDs to clauses from which these clauses arise
    std::map<int,int> inverse_cid;
    // Set of additional original clause that duplicate other argument clauses
    std::unordered_set<int> duplicate_cid;
    // Clause ID for lemma proof
    int jid;
    // What is the extension variable for the associated root node
    int xvar;
    // Hash signature based on clause IDs of arguments
    unsigned signature;
    // Allow chaining of lemmas as linked list
    Lemma_instance *next;

    // Methods
    // Assign value of hash signature.  Must do this to compare to other possible lemmas at node
    void sign(int xvar, int splitting_literal);
};

// Data structures to support BCP with two-watched literals

struct Tele {
    int lit;
    int cid;
};

class Watcher {

public:
    Watcher();

    ~Watcher();

    // Add clause to watch list
    void add_clause_id(int cid, int lit);

    // Add to trail
    void add_unit(int lit, int cid);

    // Get next unit from queue.  Return 0 if none
    int get_unit();

    // Get specified watch list
    std::vector<int> *get_list(int lit);

    std::vector<Tele> *get_trail();

    bool is_initialized() { return watch_lists.size() > 0; }

    void clear();

    void checkpoint();

    void restore();

    void watching(int cid, int lit1, int lit2);

    // Reasoner must fix up watched literals within clauses
    std::unordered_map<int,Literal_pair> *get_watched_pairs();

    // Debugging support
    bool is_watching(int cid, int lit);
    bool on_trail(int lit);


private:

    // Represent as dictionary of watch lists
    std::unordered_map<int,std::vector<int>*> watch_lists;
    // Sequence of unit literals
    std::vector<Tele> trail;
    // How many trail elements have been propagated
    int propagate_count;

    // Support to temporarily add new units and propagate them, with ability to restore to previous state
    bool saving;
    // These maps start empty and are updated only the first time a data structure gets changed
    // Sparse map, indexed by literal, from giving lengths of modified watch lists
    std::unordered_map<int,int> save_lengths;
    // Sparse map, indexed by clause ID, identifying watched literals
    std::unordered_map<int,Literal_pair> save_watched_pairs;
    // Length of trail
    int save_unit_count;
    // How many trail elements have been propagated
    int save_propagate_count;
    


};

// Augment clauses with reasoning and proof-generation capabilities 
class Cnf_reasoner : public Cnf {
private:

    // Counter to enable adding more extension variables
    int xvar_count;

    // Augmentation for POG clauses
    // Keep record of all active proof clauses
    std::vector<Clause *>proof_clauses;

    // Additional clauses used to construct proofs of lemmas
    // Each carries an activating literal indicating how to enable that clause within the formula
    // The clause numbers are sparse, and so store as map indexed by clause ID

    // Sparse representation of auxilliary clauses, map from clause ID to clause
    std::unordered_map<int, Clause*> aux_clauses;

    // Mapping from hash of clause contents to its clause ID
    // Use multimap, to deal with hash collisions
    std::unordered_multimap<unsigned,int> aux_clause_lookup;

    bool unsatisfiable;

    // Maintaining context 
    // Literals that have been set during context and should be cleared
    std::vector<int> context_literal_stack;
    // Literals that have been cleared during the context and should be restored
    std::vector<int> context_cleared_literal_stack;
    std::vector<int> context_clause_stack;
    // Mapping from unit literal to asserting clause Id 
    std::unordered_map<int, int> justifying_ids;
    // Unit literals
    std::unordered_set<int> unit_literals;
    // List of assigned literals
    std::vector<int> assigned_literals;
   
    // Ordered sets of non-satisfied clauses in current context
    // Must maintain two sets: current and active.  Swap these on each pass of BCP
    std::set<int> *curr_active_clauses;
    std::set<int> *next_active_clauses;

    // Are hints being added to an assertion?
    bool asserting;
    // Stack of vectors containing deletion information
    // Each entry contains clause ID + hints
    std::vector<std::vector<int>*> deletion_stack;

public:

    // Direct access to writer (Use with caution)
    Pog_writer *pwriter;

    // Read input clauses DIMACS format CNF file
    Cnf_reasoner(FILE *infile);

    // Has empty clause been added to proof?
    bool is_unsatisfiable();

    // Should Skolem clauses be included or virtual?
    bool use_explicit_deletion;
    bool weak_sum;
    // Solver options.
    // Combine justification of multiple literals within conjunction into single proof  Default true.
    bool multi_literal;
    // Use lemmas to represent shared nodes.  Default true.
    bool use_lemmas;
    // Delete intermediate files.  Default true.
    bool delete_files;
    // Use drat-trim when SAT problem has at least specified number of clauses
    int drat_threshold;
    // Limit on number of clauses before aborting (not implemented)
    int clause_limit;
    //  Limit of depth of BCP when looking for conflict.
    int  bcp_limit;
    // Upper threshold on tree size for generating monolithic proof
    int monolithic_threshold;
    // Upper threshold on tree ratio for generating monolothic proof
    double tree_ratio_threshold;
    // Access input, defining, proof, or auxilliary clause, with id 1 being first input clause
    Clause * get_clause(int cid);
    Clause * operator[](int);

    // Get unit literals
    std::unordered_set<int> *get_unit_literals() { return &unit_literals; }

    // POG generation.  Returns false if BCP shows formula is UNSAT
    void enable_pog(Pog_writer *cw);

    // Reset next xvar counter
    void reset_xvar();
    int new_xvar();

    // Add clause as assertion.  Returns clause ID.  If unit clause, then add to set of unit clauses
    int start_assertion(Clause *clp, bool structural);
    void add_hint(int hid);
    void add_hints(Clause *hp);
    void finish_command(bool add_zero);

    // Generate POG operation
    int start_and(int var, ilist args);
    int start_or(int var, ilist args);
    int start_skolem(int var, ilist args);
    // Document operations
    void document_input(int cid);
    void document_and(int cid, int var, ilist args);
    void document_or(int cid, int var, ilist args);
    void document_skolem(int cid, int var, ilist args);

    // Assert literal as unit clause without proof
    int assert_literal(int lit);

    // Support for stack-based context saving
    void new_context();
    void pop_context();
    // Different things to put on the context stack:
    void push_assigned_literal(int lit);
    void push_derived_literal(int lit, int cid);
    void push_clause(int cid, bool force);
    void clear_assigned_literals();
    std::vector<int> *get_assigned_literals();
    std::unordered_map<int, int> *get_justifying_ids();

    // set/get active clauses
    void extract_active_clauses(std::set<int> *save_set);
    void set_active_clauses(std::set<int> *new_set);

    // Partition set of active clauses into subsets having disjoint variables
    void partition_clauses(std::unordered_map<int,int> &var2rvar, std::unordered_map<int,std::set<int>*> &rvar2cset);

    // Extract a reduced representation of the currently active clauses
    Cnf_reduced *extract_cnf();

    // Perform Boolean constraint propagation.
    // Return ID of any generated conflict clause (or 0)
    int bcp(bool bounded);

    // Setup watch pointers and do unit propagation.
    // Return true if get conflict
    bool watches_setup(Watcher &watches);

    // Validate clause by RUP.
    //  If add_clause: Add clause as assertion and return ID of validating clause (or 0 if fail)
    //  Otherwise, just fill in the hints.
    //  Deletion is for an input clause.  

    int rup_validate(Clause *cltp, bool add_clause, Watcher &watches, std::vector<int> &hints);

    // possible modes for attempting literal validation
    typedef enum { 
	MODE_FULL, // do everything
	MODE_BCP,  // use bcp and then stop
	MODE_BBCP, // bounded bcp and then stop
	MODE_SAT   // skip bcp and use sat solver
    } validation_mode_t;


    // justify that literal holds.  return id of justifying clause
    // if full, call sat solver if necessary
    int validate_literal(int lit, validation_mode_t mode);

    // justify that set of literals hold.
    // justifying clauses ids are then loaded into jids vector
    // return true if successful
    bool validate_literals(std::vector<int> &lits, std::vector<int> &jids);

    // delete all but final asserted clause
    void delete_assertions();

    // carefully check status of possible unit literal
    // optionally consider only active clauses
    void check_for_unit(int lit);

    //// lemma support

    // extract information required to define, prove, or apply a lemma
    Lemma_instance *extract_lemma(int xvar, int splitting_literal);

    // set up context for lemma proof
    void setup_proof(Lemma_instance *lemma);

    void restore_from_proof(Lemma_instance *lemma);

    int apply_lemma(Lemma_instance *lemma, Lemma_instance *instance);

    // Monolithic validation: generate proof that input formula --> root literal
    int monolithic_validate_root(int root_literal);


    // Filter out the unit literals that are required for proof, given the main clause and the hint clauses
    void filter_units(Clause *pnp, Clause *php, std::unordered_set<int> &units);

    int get_proof_size() { return proof_clauses.size(); }

    // Include/Exclude clause in BCP
    void activate_clause(int clit);
    void deactivate_clause(int clit);
    void deactivate_all_clauses();


private:

    // Support for BCP
    int bcp_unit_propagate(int cid, bool first_pass,
			   Watcher &watches);

    bool is_active(int cid);

    void check_watch_state(Watcher &watches, bool quiescent);

    // Private methods for proof generation

    // Run SAT solver on reduced set of clauses as part of effort to validate literal lit.
    // Incorporate generated conflict proof into larger proof
    // Identify literals that will become unit and their justifying IDs
    int reduce_run(int lit);

    int add_proof_clause(Clause *clp);
    // Private methods for search support
    int found_conflict(int cid);
    void new_unit(int lit, int cid, bool input);

    // Validate unit when it can be done with just two hints
    int quick_validate_literal(int lit, int cid1, int cid2);

    // Handling of lemma argument clauses

    // Retrieve based on clause ID
    // Return NULL if not found
    Clause *get_aux_clause(int cid);

    // Find existing auxilliary clause or create new one with these literals.
    // Return clause ID
    int find_or_make_aux_clause(ilist lits);

    // Add active clause to lemma.  It will simplify the clause
    // and, if changed, will find/create a synthetic clause to serve as the argument
    void add_lemma_argument(Lemma_instance *lemma, int cid);

    // Debugging support
    // Sanity checks on active clauses
    bool check_active();

    // Supporting monolithic validation
    bool monolithic_load_proof(FILE *lfile, int root_literal);
};

