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

#include <iostream>
#include <ctype.h>
#include <algorithm>
#include <cstring>
#include <map>
#include "clausal.hh"
#include "report.h"
#include "counters.h"

#ifndef LOG
#define LOG 0
#endif

// Put literals in ascending order of the variables
static bool abs_less(int x, int y) {
    return abs(x) < abs(y);
}

// Read characters until find EOL or EOF.
// Return result
static int skip_line(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == '\n')
	    return c;
    }
    return c;
}

// Skip over spaces, newlines, etc., until find something interesting
// Put last character encountered back into stream and return it
static int find_nonspace(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (!isspace(c)) {
	    ungetc(c, infile);
	    break;
	}
    }
    return c;
}

// Skip over comment lines, spaces, newlines, etc., until find something interesting
// Return false if EOF encountered without finding anything
static bool find_token(FILE *infile) {
    int c;
    while ((c = getc(infile)) != EOF) {
	if (c == 'c') {
	    c = skip_line(infile);
	    ungetc(c, infile);
	} else if (!isspace(c)) {
	    ungetc(c, infile);
	    return true;
	}
	// Skip space
    }
    return false;
}

// Read string token:
// Skip over spaces.
// Read contiguous non-space characters and store in dest.
// Set len to number of characters read.
// Return false if EOF encountered without getting string
static bool find_string_token(FILE *infile, char *dest, int maxlen, int *len) {
    int c;
    int rlen = 0;
    while ((c = getc(infile)) != EOF && rlen < maxlen-1) {
	if (isspace(c)) {
	    if (rlen > 0) {
		// Past token
		ungetc(c, infile);
		break;
	    }
	} else {
	    *(dest+rlen) = c;
	    rlen++;
	}
    }
    *(dest+rlen) = '\0';
    *len = rlen;
    return (c != EOF);
}

static int read_variable_list(FILE *infile, std::unordered_set<int> **ptr_variables) {
    if (*ptr_variables == NULL)
	*ptr_variables = new std::unordered_set<int>;
    int var = -1;
    int count = 0;
    while (var != 0) {
	if (fscanf(infile, "%d", &var) != 1) {
	    err(false, "Couldn't read variables\n");
	    break;
	} else if (var != 0) {
	    (*ptr_variables)->insert(var);
	    count++;
	}
    }
    return count;
}

// Process comment, looking additional data variables & weights
// If find declaration of data variables, collect as set
// Otherwise return NULL
static void process_comment(FILE *infile, std::unordered_set<int> **ptr_data_variables) {
    char buf[50];
    int len;
    if (find_string_token(infile, buf, 50, &len) && len == 1 && strncmp(buf, "p", 1) == 0
	&& find_string_token(infile, buf, 50, &len)) {
	if (len == 4 && strncmp(buf, "show", 4) == 0) {
	    int count = read_variable_list(infile, ptr_data_variables);
	    incr_count_by(COUNT_DATA_VAR, count);
	}
    }
    skip_line(infile);
}		

Clause::Clause() { 
    contents = ilist_new(0);
    is_tautology = false;
    canonized = true;
    activating_literal = 0;
}

Clause::~Clause() { 
    ilist_free(contents);
}

Clause::Clause(int *array, size_t len) {
    is_tautology = false;
    canonized = false;
    contents = ilist_new(len);
    for (int i = 0; i < len; i++)
	add(array[i]);
    activating_literal = 0;
}

Clause::Clause(int lit) {
    contents = ilist_new(1);
    add(lit);
    is_tautology = false;
    canonized = true;
    activating_literal = 0;
}

Clause::Clause(Clause *np) {
    is_tautology = false;
    canonized = np->canonized;
    contents = ilist_copy(np->contents);
    activating_literal = np->get_activating_literal();
}

// Must be at line that contains clause
Clause::Clause(FILE *infile, bool from_proof, bool *eof) {
    int rval;
    int lit;
    int c;
    is_tautology = false;
    contents = ilist_new(4);
    *eof = true;

    // Skip blank lines and comments
    while ((c = getc(infile)) != EOF) {
	if (c == 'c')
	    c = skip_line(infile);
	else if (from_proof && c == 'd')
	    c = skip_line(infile);
	else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    break;
	}
    }

    while ((rval = fscanf(infile, "%d", &lit)) == 1) {
	*eof = false;
	if (lit == 0)
	    break;
	else
	    add(lit);
    }
    if (!from_proof)
	canonize();
    activating_literal = 0;
}

void Clause::add(int val) {
    contents = ilist_push(contents, val);
    canonized = false;
}

size_t Clause::length() {
    if (is_tautology)
	return 0;
    return ilist_length(contents);
}

bool Clause::tautology() {
    canonize();
    return is_tautology;
}

int Clause::max_variable() {
    int mvar = 0;
    if (is_tautology)
	return 0;
    for (int i = 0; i < length(); i++) {
	int var = abs(contents[i]);
	mvar = std::max(var, mvar);
    }
    return mvar;
}

int * Clause::data() {
    return contents;
}


int& Clause::operator[](int i) {
    return contents[i];
}

int Clause::get_activating_literal() {
    return activating_literal;
}

void Clause::set_activating_literal(int alit) {
    activating_literal = alit;
}

bool Clause::satisfied(char *assignment) {
    bool found = is_tautology;
    for (int i = 0; !found && i < ilist_length(contents); i++) {
	int lit = contents[i];
	found = (lit < 0 && assignment[-lit-1] == 0) || (lit > 0 && assignment[lit-1] == 1);
    }
    return found;
}

bool Clause::contains(int lit) {
    for (int i = 0; i < ilist_length(contents); i++)
	if (contents[i] == lit)
	    return true;
    return false;
}

void Clause::build_set(std::unordered_set<int> &dict) {
    dict.clear();
    for (int i = 0; i < ilist_length(contents); i++)
	dict.insert(contents[i]);
}

static char buf[10000];

void Clause::canonize() {
    if (canonized)
	return;
    
    std::sort(contents, contents + length(), abs_less);
    int last_lit = 0;
    size_t read_pos = 0;
    size_t write_pos = 0;
    is_tautology = false;
    while(read_pos < length()) {
	int lit = contents[read_pos++];
	if (abs(lit) == abs(last_lit)) {
	    if (lit != last_lit) {
		// Opposite literals encountered
		is_tautology = true;
		break;
	    }
	} else {
	    contents[write_pos++] = lit;
	}
	last_lit = lit;
    }
    if (is_tautology) {
	contents = ilist_resize(contents, 2);
	contents[0] = abs(last_lit);
	contents[1] = -abs(last_lit);
    } else
	contents = ilist_resize(contents, write_pos);
    canonized = true;
}

void Clause::make_tautology() {
    contents = ilist_resize(contents, 2);
    contents[1] = -contents[0];
    is_tautology = true;
    canonized = true;
}

void Clause::swap_literals(int idx1, int idx2) {
    int tmp = contents[idx1];
    contents[idx1] = contents[idx2];
    contents[idx2] = tmp;
    canonized = false;
}


// Permute literals to place specified pair at front
void Clause::rearrange(Literal_pair &lits) {
    int rlit[2] = {lits.lit1, lits.lit2};
    bool found[2] = {false, false};
    for (int i = 0; i < 2; i++) {
	int tlit = rlit[i];
	for (int j = 0; j < ilist_length(contents); j++) {
	    if (contents[j] == tlit) {
		swap_literals(i, j);
		found[i] = true;
		break;
	    }
	}
    }
    if (!found[0] || !found[1]) 
	err(false, "  Rearrange.  Literal %d %sfound.  Literal %d %sfound\n",
	    lits.lit1, found[0] ? "" : "not ", 
	    lits.lit2, found[1] ? "" : "not ");
}

void Clause::show() {
    if (is_tautology) {
	std::cout << "c Tautology" << std::endl;
	std::cout << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	std::cout << contents[i] << ' ';
    std::cout << '0' << std::endl;
}

void Clause::show(std::ofstream &outstream) {
    if (is_tautology) {
	outstream << "c Tautology" << std::endl;
	outstream << "1 -1 0" << std::endl;
	return;
    }
    for (int i = 0; i < length(); i++)
	outstream << contents[i] << ' ';
    outstream << '0' << std::endl;
}

void Clause::show(FILE *outfile) {
    if (is_tautology) {
	fprintf(outfile, "c Tautology\n");
	fprintf(outfile, "1 -1 0\n");
	return;
    }
    for (int i = 0; i < length(); i++)
	fprintf(outfile, "%d ", contents[i]);
    fprintf(outfile, "0\n");
}

void Clause::show_reduced(FILE *outfile, int ulit) {
    // See if clause becomes tautology
    bool tautology = is_tautology;
    for (int i = 0; !tautology && i < length(); i++)
	if (contents[i] == ulit)
	    tautology = true;
    if (tautology)
	fprintf(outfile, "%d %d ", ulit, -ulit);
    else
	for (int i = 0; i < length(); i++) {
	    int lit = contents[i];
	    if (lit != -ulit)
		fprintf(outfile, "%d ", lit);
	}
    fprintf(outfile, "0\n");	
}

void Clause::write(Writer *writer) {
    if (is_tautology) {
	int tclause[2 + ILIST_OVHD];
	ilist ils = ilist_make(tclause, 2);
	ilist_fill2(ils, 1, -1);
	writer->write_list(ils);
	return;
    }
    writer->write_list(contents);
}

ilist Clause::simplify(std::unordered_set<int> &unit_literals) {
    ilist lits = ilist_new(0);
    bool satisfied = false;
    for (int i = 0; i < length(); i++) {
	int lit = contents[i];
	if (unit_literals.find(lit) != unit_literals.end()) {
	    satisfied = true;
	    break;
	} else if (unit_literals.find(-lit) == unit_literals.end())
	    lits = ilist_push(lits, lit);
    }
    if (satisfied)
	return NULL;
    return lits;
}



// Support for computing hash function over clause
// Represent by signature over modular field
static const unsigned hash_modulus = 2147483647U;
static char hash_state[256];

static std::vector<unsigned> var_hash;

#define CHUNK_SIZE 1024

static unsigned next_hash_int(unsigned sofar, int val) {
    if (var_hash.size() == 0) {
	// Initialization
	initstate(1, hash_state, 256);
    }
    unsigned var = IABS(val);
    if (var >= var_hash.size()) {
	// Add more random values
	size_t osize = var_hash.size();
	size_t nsize = osize + (1 + (var - osize)/CHUNK_SIZE) * CHUNK_SIZE;
	var_hash.resize(nsize);
	char *ostate = setstate(hash_state);
	for (unsigned i = osize; i < nsize; i++)
	    var_hash[i] = random() % hash_modulus;
	setstate(ostate);
    }
    unsigned vval = var_hash[var];
    unsigned long  lval = val < 0 ? 1 + hash_modulus - vval : vval;
    return (lval * sofar) % hash_modulus;
}
    
unsigned Clause::hash() {
    canonize();
    unsigned val = 1;
    for (int i = 0; i < length(); i++)
	val = next_hash_int(val, contents[i]);
    return val;
}

bool Clause::is_equal(Clause *op) {
    canonize();
    op->canonize();
    if (length() != op->length())
	return false;
    if (tautology() != op->tautology())
	return false;
    for (int i = 0; i < length(); i++)
	if (contents[i] != (*op)[i])
	    return false;
    return true;
}

Literal_set::Literal_set(int nvar) {
    last_gen.resize(nvar);
    memset(last_gen.data(), 0, nvar * sizeof(int));
    current_generation = 1;
}

void Literal_set::load_clause(Clause *cp) {
    current_generation++;
    for (int i = 0; i < cp->length(); i++) {
	int lit = (*cp)[i];
	if (lit < 0)
	    last_gen[-lit-1] = -current_generation;
	else
	    last_gen[lit-1] = current_generation;
    }
}

bool Literal_set::contains(int lit) {
    if (lit < 0)
	return last_gen[-lit-1] == -current_generation;
    else
	return last_gen[lit-1] == current_generation;
}

Cnf::Cnf() { read_failed = false; proof_failed = false; max_input_var = 0; data_variables = NULL; }

Cnf::Cnf(FILE *infile) { 
    int expectedMax = 0;
    int expectedCount = 0;
    read_failed = false;
    proof_failed = false;
    max_input_var = 0;
    data_variables = NULL;
    bool got_header = false;
    bool no_header = false;
    int c;
    // Look for CNF header
    while ((c = getc(infile)) != EOF) {
	if (isspace(c)) 
	    continue;
	if (c == 'c') 
	    process_comment(infile, &data_variables);
	else if (c == 'd')
	    c = skip_line(infile);
	if (c == 's') {
	    // Failed proof
	    proof_failed = true;
	    return;
	}
	if (c == EOF) {
	    err(false, "Not valid CNF file.  No header line found\n");
	    read_failed = true;
	    return;
	}
	if (c == 'p') {
	    char field[20];
	    if (fscanf(infile, "%s", field) != 1) {
		err(false, "Not valid CNF file.  Invalid header line\n");
		read_failed = true;
		return;
	    }
	    if (strcmp(field, "cnf") != 0) {
		err(false, "Not valid CNF file.  Header line shows type is '%s'\n", field);
		read_failed = true;
		return;
	    }
	    if (fscanf(infile, "%d %d", &expectedMax, &expectedCount) != 2) {
		err(false, "Invalid CNF header\n");
		read_failed = true;
		return;
	    } 
	    c = skip_line(infile);
	    got_header = true;
	    break;
	}
	if (c == EOF) {
	    err(false, "Invalid CNF.  EOF encountered before reading any clauses\n");
	    read_failed = true;
	    return;
	}
	if (isdigit(c) || c == '-') {
	    no_header = true;
	    ungetc(c, infile);
	    break;
	}
    }
    if (!got_header && !no_header) {
	err(false, "Not valid CNF.  No header line found\n");
	read_failed = true;
	return;
    }
    while (1) {
	bool eof = false;

	int c;
	while (!data_variables && (c = find_nonspace(infile)) == 'c') {
	    c = getc(infile);
	    process_comment(infile, &data_variables);
	}
	
	Clause *clp = new Clause(infile, !got_header, &eof);
	if (eof || read_failed)
	    break;
	add(clp);

    }
    if (!no_header && max_input_var > expectedMax) {
	err(false, "Invalid CNF.  Encountered variable %d. Expected max = %d\n",  max_input_var, expectedMax);
	read_failed = true;
	return;
    }
    if (!no_header && clause_count() != expectedCount) {
	err(false, "Read %d clauses.  Expected %d\n", clause_count(), expectedCount);
	read_failed = true;
	return;
    }
    if (!no_header) {
	max_input_var = expectedMax;
	incr_count_by(COUNT_CLAUSE, clause_count());
	incr_count_by(COUNT_VAR, max_input_var);
	
    }
}

// Delete the clauses
Cnf::~Cnf() { 
    for (Clause *np : clauses)
	delete np;
    clauses.clear();
}

bool Cnf::failed() {
    return read_failed;
}

void Cnf::add(Clause *clp) {
    clauses.push_back(clp);
    int mvar = clp->max_variable();
    max_input_var = std::max(max_input_var, mvar);
}

Clause * Cnf::get_input_clause(int cid) {
    int input_count = clauses.size();
    if (cid <= input_count)
	return clauses[cid-1];
    else {
	err(true, "Fatal.  Trying to access clause #%d.  Have %d input clauses\n", cid, input_count);
	exit(1);
    }
}

unsigned Cnf::hash() {
    unsigned sig = 1;
    for (Clause *cp : clauses) {
	sig = next_hash_int(sig, cp->hash());
    }
    return sig;
}

Clause * Cnf::operator[](int cid) {
    return get_input_clause(cid);
}

void Cnf::show() {
    std::cout << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (Clause *cp : clauses)
	cp->show();
}

void Cnf::show(std::ofstream &outstream) {
    outstream << "p cnf " << max_input_var << " " << clause_count() << std::endl;
    for (Clause *cp : clauses)
	cp->show(outstream);
}

void Cnf::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_input_var, (int) clause_count());
    for (Clause *cp : clauses)
	cp->show(outfile);
}

size_t Cnf::clause_count() {
    return clauses.size();
}

int Cnf::max_variable() {
    return max_input_var;
}

int Cnf::satisfied(char *assignment) {
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->satisfied(assignment))
	    return cid;
    }
    return 0;
}


// Support for generating reduced CNF, running through SAT solver, and mapping proof steps back to original
Cnf_reduced::Cnf_reduced() : Cnf() {
    emitted_proof_clauses = 0;
    unsatisfiable = false;
    unsatisfiable_id = 0;
    delete_files = true;
}

Cnf_reduced::~Cnf_reduced() {
    for (Clause *np : proof_clauses) {
	if (np)
	    delete np;
    }
    // Delete the temporary files
    for (const char *fname : file_names) {
	if (delete_files) {
	    if (remove(fname) != 0) 
		report(3, "Warning: Attempt to delete file %s failed.  Error code = %d\n", fname, errno);
	}
	free((void *) fname);
    }
}

const char *Cnf_reduced::get_file_name() {
    if (file_names.size() >= 1)
	return file_names[0];
    else
	return "Unknown";
}

void Cnf_reduced::add_clause(Clause *np, std::unordered_set<int> &unit_literals, int cid) {
    ilist slits = np->simplify(unit_literals);
    if (slits != NULL) {
	Clause *snp = new Clause(slits, ilist_length(slits));
	add(snp);
	int ncid = clause_count();
	inverse_cid[ncid] = cid;
	if (snp->length() == 0) {
	    unsatisfiable = true;
	    unsatisfiable_id = ncid;
	}
    }
}

// Special version of show that includes comments
void Cnf_reduced::show(FILE *outfile) {
    fprintf(outfile, "p cnf %d %d\n", max_variable(), (int) clause_count());
#if DEBUG
    int cid = 0;
#endif
    for (Clause *cp : clauses) {
#if DEBUG
	cid++;
	fprintf(outfile, "c local clause #%d -> global clause #%d\n", cid, inverse_cid.find(cid)->second);
#endif
	cp->show(outfile);
    }
}


bool Cnf_reduced::run_solver() {
    incr_count(COUNT_SAT_CALL);
    char cmd[150];
    if (unsatisfiable) {
	report(3, "Solver.  Reduced CNF contains empty clause.  Clause ID = %d\n", unsatisfiable_id);
	Clause *np = new Clause();
	Clause *hp = new Clause();
	hp->add(unsatisfiable_id);
	proof_clauses.push_back(np);
	proof_hints.push_back(hp);
	return true;
    }

    const char *fname = generate_name("cnf", true);
    FILE *cout = fopen(fname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", fname);
	return false;
    }
    file_names.push_back(fname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), fname);
    
    double start = tod();
#if SOLVER == CADICAL || SOLVER == LCADICAL || SOLVER == TCADICAL
    snprintf(cmd, 150, "cadical --unsat -q --no-binary %s -", fname);
#else
    snprintf(cmd, 150, "kissat --unsat -q --no-binary %s -", fname);
#endif
    FILE *sfile = popen(cmd, "r");
    if (sfile == NULL) {
	err(true, "Couldn't execute command '%s'\n", cmd);
    }
    Cnf pclauses(sfile);
    pclose(sfile);
    incr_timer(TIME_SAT_TOTAL, tod()-start);

#if VLEVEL >= 3    
    report(3, "Read %d proof clauses\n", pclauses.clause_count());
    if (verblevel >= 5)
	pclauses.show();
#endif
    if (pclauses.proof_failed) {
	err(false, "Execution of command '%s' shows formula satisfiable\n", cmd);
	return false;
    }

    if (pclauses.clause_count() == 0) {
	err(true, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }

    Clause *lnp = pclauses[pclauses.clause_count()];
    if (lnp == NULL) {
	err(false, "Invalid final clause after executing command '%s'\n", cmd);
	return false;
    }
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }

    for (int cid = 1; cid <= pclauses.clause_count(); cid++) {
	Clause *pnp = pclauses[cid];
	proof_clauses.push_back(pnp);
	if (pnp->length() == 0)
	    break;
    }
    double micro = (tod() - start) * 1e6;
#if LOG
    log_data("s,%u,%d,%d,%.0f\n", hash(), clause_count(), pclauses.clause_count(), micro);
#endif
    report(3, "File %s.  %d input clauses --> %d proof clauses (%.0f us)\n", fname, clause_count(), proof_clauses.size(), micro);
    incr_histo(HISTO_PROBLEM, clause_count());
    incr_histo(HISTO_PROOF, proof_clauses.size());

    return true;
}

bool Cnf_reduced::run_hinting_solver() {
    incr_count(COUNT_SAT_CALL);
    char cmd[350];

    if (unsatisfiable) {
	report(3, "Hinting solver.  Reduced CNF contains empty clause.  Clause ID = %d\n", unsatisfiable_id);
	Clause *np = new Clause();
	Clause *hp = new Clause();
	hp->add(unsatisfiable_id);
	proof_clauses.push_back(np);
	proof_hints.push_back(hp);
	return true;
    }

    const char *cnfname = generate_name("cnf", true);
    FILE *cout = fopen(cnfname, "w");
    if (cout == NULL) {
	err(false, "Couldn't open temporary CNF file %s\n", cnfname);
	return false;
    }
    file_names.push_back(cnfname);
    show(cout);
    fclose(cout);
    report(3, "Wrote file with %d clauses to %s\n", clause_count(), cnfname);
    
    const char *lratname = generate_name("lrat", false);
    file_names.push_back(lratname);

    double start = tod();
    const char *trimmer = "drat-trim";
#if SOLVER == CADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnfname, cnfname, lratname);
#elif SOLVER == LCADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q --lrat=1 %s %s", cnfname, lratname);
    trimmer="cadical";
#elif SOLVER == TCADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q --lrat=1 %s - | lrat-trim --no-binary -q - %s", cnfname, lratname);
    trimmer = "lrat-trim";
#else
    snprintf(cmd, 350, "kissat --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnfname, cnfname, lratname);
#endif
    int rc = system(cmd);
    incr_timer(TIME_SAT_TOTAL, tod()-start);
    if (rc != 0)
	report(2, "Executing command '%s' yielded return code %d\n", cmd, rc);
    FILE *lfile = fopen(lratname, "r");
    if (!lfile) {
	report(2, "Couldn't open generated LRAT file %s\n", lratname);
	return false;
    }
    if (!load_hinted_proof(lfile)) {
	err(false, "Failed to read generated LRAT file\n", lratname);
	return false;
    }
    fclose(lfile);
    if (proof_clauses.size() == 0) {
	err(false, "Execution of command '%s' yielded no proof clauses\n", cmd);
	return false;
    }
    report(3, "File %s.  Generating lrat with %s.  %d problem clauses.  %d proof clauses\n", cnfname, trimmer, clause_count(), proof_clauses.size()); 
    Clause *lnp = proof_clauses.back();
    if (lnp->length() != 0) {
	err(false, "Execution of command '%s' did not generate empty clause\n", cmd);	
	return false;
    }
    double micro = (tod() - start) * 1e6;
#if LOG
    log_data("t,%u,%d,%d,%.0f\n", hash(), clause_count(), proof_clauses.size(), micro);
#endif
    report(3, "File %s.  %d input clauses --> %d proof clauses (%.0f us)\n", cnfname, clause_count(), proof_clauses.size(), micro);
    incr_histo(HISTO_PROBLEM, clause_count());
    incr_histo(HISTO_PROOF, proof_clauses.size());
    return true;
}

// Perform bounded variable elimination.
// Assume clauses ordered so that can make single pass
// Assume that each clause has at most one candidate variables
// max_degree indicates maximum allowed clause expansion as m*m-(m+m)
// Create fresh CNF representation
// Current implementation does not justify what it's doing
void Cnf_reduced::ordered_bve(int max_degree, std::unordered_set<int> *keep_variables, Cnf *new_cnf) {
    report(2, "BVE.  Max degree = %d Retain %d variables\n", max_degree, (int) keep_variables->size());
    if (verblevel >= 2) {
	report(2, "Initial CNF:\n");
	show(stdout);
    }
    report(2, "Eliminating\n");
    // Mapping from each candidate literal to clauses containing it.  Indexed by var - 1
    std::vector<std::set<int>*> positive_ids;
    std::vector<std::set<int>*> negative_ids;
    positive_ids.resize(max_variable());
    negative_ids.resize(max_variable());
    int candidate_var_count = 0;
    // Build up list of new clauses.   Intialized with copy of all clauses
    // Add and delete them (leaving holes) as do BVE
    std::vector<Clause *> clause_list;
    // Copy all clauses.  Locate positive and negative occurrences of each candidate variable
    for (int lcid = 1; lcid <= clauses.size(); lcid++) {
	Clause *ncp = new Clause(clauses[lcid-1]);
	clause_list.push_back(ncp);
	int len = ncp->length();
	for (int i = 0; i < len; i++) {
	    int lit = (*ncp)[i];
	    int var = IABS(lit);
	    if (keep_variables->find(var) == keep_variables->end()) {
		if (positive_ids[var-1] == NULL) {
		    positive_ids[var-1] = new std::set<int>;
		    negative_ids[var-1] = new std::set<int>;
		    candidate_var_count ++;
		}
		if (lit > 0) 
		    positive_ids[var-1]->insert(lcid);
		else
		    negative_ids[var-1]->insert(lcid);
	    }
	}
    }
    int max_added = max_degree*max_degree - 2*max_degree;
    int elim_var_count = 0;
    report(2, "BVE.  Started with %d clauses\n", (int) clauses.size());

    int evar = 1;
    while (evar <= max_variable()) {
	// Progress through possible elimination variables, but revisit old ones when update references
	int next_evar = evar+1;
	int pos_degree = positive_ids[evar-1] ? positive_ids[evar-1]->size() : 0;
	int neg_degree = negative_ids[evar-1] ? negative_ids[evar-1]->size() : 0;
	int added = pos_degree*neg_degree - (pos_degree+neg_degree);
	if (pos_degree == 0 && neg_degree == 0) {
	    evar = next_evar;
	    continue;
	}

	if (added <= max_added) {
	    report(2, "BVE.  Eliminating variable %d.  Will add %d clauses and delete %d (pos %d, neg %d)\n",
		   evar, pos_degree * neg_degree, pos_degree + neg_degree, pos_degree, neg_degree);
	    elim_var_count++;
	    // Create new clauses
	    std::vector<int> deletion_list;
	    for (int plcid : *positive_ids[evar-1]) {
		deletion_list.push_back(plcid);
		Clause *pos_cp = clause_list[plcid-1];
		for (int nlcid : *negative_ids[evar-1]) {
		    Clause *neg_cp = clause_list[nlcid-1];
		    Clause *ncp = new Clause();
		    for (int i = 0; i < pos_cp->length(); i++) {
			int lit = (*pos_cp)[i];
			if (lit != evar)
			    ncp->add(lit);
		    }
		    for (int i = 0; i < neg_cp->length(); i++) {
			// -evar should occur
			int lit = (*neg_cp)[i];
			if (lit != -evar)
			    ncp->add(lit);
		    }
		    clause_list.push_back(ncp);
		    int lcid = (int) clause_list.size();
		    for (int i = 0; i < ncp->length(); i++) {
			int lit = (*ncp)[i];
			int var = IABS(lit);
			if (keep_variables->find(var) != keep_variables->end())
			    continue;
			if (lit > 0)
			    positive_ids[lit-1]->insert(lcid);
			else
			    negative_ids[-lit-1]->insert(lcid);
		    }
		}
	    }
	    for (int nlcid : *negative_ids[evar-1])
		deletion_list.push_back(nlcid);
	    for (int dlcid : deletion_list) {
		Clause *dcp = clause_list[dlcid-1];
		for (int i = 0; i < dcp->length(); i++) {
		    int lit = (*dcp)[i];
		    int var = IABS(lit);
		    if (keep_variables->find(var) != keep_variables->end())
			continue;
		    if (lit > 0)
			positive_ids[lit-1]->erase(dlcid);
		    else 
			negative_ids[-lit-1]->erase(dlcid);
		}
		delete clause_list[dlcid-1];
		clause_list[dlcid-1] = NULL;
	    }
	} else {
	    report(2, "BVE.  Keeping variable %d\n", evar);
	}
	evar = next_evar;
    }
    // Now load up result with the clauses that weren't deleted
    for (Clause *cp : clause_list) {
	if (cp != NULL)
	    new_cnf->add(cp);
    }
    report(1, "BVE with max degree %d.  Eliminated %d of %d possible variables.  Clause count %d --> %d\n",
	   max_degree, elim_var_count, candidate_var_count, clause_count(), new_cnf->clause_count());
}

// Read proof clauses + hints in LRAT format.
// Ignore deletions
// Return true if successful
bool Cnf_reduced::load_hinted_proof(FILE *infile) {
    int nclause = clause_count();
    std::unordered_map<int,int> lrat2local;
    int next_id = nclause + 1;
    int c;
    while (find_token(infile)) {

	int sid = 0;
	if (fscanf(infile, "%d", &sid) != 1) {
	    err(false, "Couldn't read step Id in LRAT file.  Should be at step #%d\n", next_id);
	    return false;
	}
	if (!find_token(infile)) {
	    err(false, "EOF found while trying to parse proof step #%d\n", next_id);
	}
	int c = getc(infile);
	if (c == EOF) {
	    err(false, "EOF found while trying to parse proof step #%d\n", sid);
	    return false;
	}
	if (c == 'd') {
	    c = skip_line(infile);
	    if (c == EOF) {
		err(false, "EOF found while trying to parse proof step #%d\n", sid);
		return false;
	    }
	    ungetc(c, infile);
	    continue;
	} else
	    ungetc(c, infile);
	// Here's the good stuff
	bool eof;
	Clause *np = new Clause(infile, true, &eof);
	if (np == NULL || eof) {
	    err(false, "Error encountered while trying to read literals from proof step #%d\n", sid);
	    return false;
	}
	Clause *hp = new Clause(infile, true, &eof);
	if (hp == NULL || eof) {
	    err(false, "Error encountered while trying to read hints from proof step #%d\n", sid);
	    return false;
	}
	lrat2local[sid] = next_id;
	// Fix up hints
	for (int i = 0; i < hp->length(); i++) {
	    int hint = (*hp)[i];
	    int nhint = (hint <= nclause) ? hint : lrat2local.find(hint)->second;
	    (*hp)[i] = nhint;
	}
	proof_clauses.push_back(np);
	proof_hints.push_back(hp);
	next_id++;
    }
    return true;
}

// Retrieve hints for next clause in proof.
// Remap hint clause Ids to ones that match those in the larger proof
// start_id should be Id for first clause in proof sequence
Clause * Cnf_reduced::get_proof_hint(int start_id) {
    if (emitted_proof_clauses >= proof_hints.size())
	return NULL;
    Clause *hp = proof_hints[emitted_proof_clauses];
    Clause *nhp = new Clause();
    int ccount = clause_count();
    for (int i = 0; i < hp->length(); i++) {
	int hint = (*hp)[i];
	int nhint = hint <= ccount ? inverse_cid[hint] : start_id + hint - ccount - 1;
	nhp->add(nhint);
    }
    delete hp;
    return nhp;
}

// Retrieve next clause in proof.  Convert it to one usable by parent solver
Clause * Cnf_reduced::get_proof_clause(std::vector<int> *context) {
    if (emitted_proof_clauses >= proof_clauses.size())
	return NULL;
    Clause *np = proof_clauses[emitted_proof_clauses];
    Clause *nnp = new Clause(np);
    for (int lit : *context) 
	nnp->add(-lit);
    delete np;
    proof_clauses[emitted_proof_clauses++] = NULL;
    return nnp;
}


// Watch list support
Watcher::Watcher() {
    clear();
}

Watcher::~Watcher() {
    clear();
}

void Watcher::clear() {
    for (auto iter : watch_lists) {
	std::vector<int>* wlist = iter.second;
	delete wlist;
    }
    watch_lists.clear();
    trail.clear();
    propagate_count = 0;
    saving = false;
    save_unit_count = 0;
    save_propagate_count = 0;
}

void Watcher::add_clause_id(int cid, int lit) {
    std::vector<int> *wlist = get_list(lit);
    // See if this is the first new entry on the list
    if (saving && save_lengths.find(lit) == save_lengths.end()) {
	save_lengths[lit] = wlist->size();
	report(3, "Saving list length %d for watched literal %d\n", wlist->size(), lit);
    }
    wlist->push_back(cid);
}

void Watcher::add_unit(int lit, int cid) {
    report(3, "Adding unit %d (clause #%d) to unit queue\n", lit, cid);
    trail.push_back({lit,cid});
}

int Watcher::get_unit() {
    if (propagate_count >= trail.size())
	return 0;
    return trail[propagate_count++].lit;
}

void Watcher::checkpoint() {
    saving = true;
    save_lengths.clear();
    save_watched_pairs.clear();
    save_unit_count = trail.size();
    save_propagate_count = propagate_count;
}

void Watcher::restore() {
    // Note: Up to other reasoner code to reorder literals within clauses
    report(3, "Restoring watch state\n");
    for (auto iter : save_lengths) {
	int lit = iter.first;
	int len = iter.second;
	std::vector<int> *wlist = get_list(lit);
	wlist->resize(len);
	report(3, "Restoring watch list for literal %d to be of length %d\n", lit, len);
    }
    trail.resize(save_unit_count);
    propagate_count = save_propagate_count;
    save_lengths.clear();
    save_watched_pairs.clear();
    saving = false;
}

void Watcher::watching(int cid, int lit1, int lit2) {
    if (saving && save_watched_pairs.find(cid) == save_watched_pairs.end()) {
	save_watched_pairs[cid] = {lit1, lit2};
    }
}

std::vector<int> *Watcher::get_list(int lit) {
    std::vector<int> *wlist;
    auto finder = watch_lists.find(lit);
    if (finder == watch_lists.end()) {
	wlist = new std::vector<int>;
	watch_lists[lit] = wlist;
    } else 
	wlist = finder->second;
    return wlist;
}

std::vector<Tele> *Watcher::get_trail() {
    return &trail;
}

std::unordered_map<int,Literal_pair> *Watcher::get_watched_pairs() {
    return &save_watched_pairs;
}

bool Watcher::is_watching(int cid, int lit) {
    std::vector<int> *wlist = get_list(lit);
    for (int wcid : *wlist) {
	if (cid == wcid)
	    return true;
    }
    return false;
}

bool Watcher::on_trail(int lit) {
    for (int idx = propagate_count; idx < trail.size(); idx++) {
	int tlit = trail[idx].lit;
	if (tlit == lit)
	    return true;
    }
    return false;
}



// Proof related
Cnf_reasoner::Cnf_reasoner(FILE *infile) : Cnf(infile) { 
    pwriter = NULL;
    asserting = false;
    unsatisfiable = false;
    use_explicit_deletion = false;
    weak_sum = false;
    multi_literal = true;
    use_lemmas = true;
    delete_files = true;
    drat_threshold = 1000;
    monolithic_threshold = 1000*1000;
    tree_ratio_threshold = 5.0;
    clause_limit = INT_MAX;
    bcp_limit = 1;
    xvar_count = max_variable();
}

Clause * Cnf_reasoner::get_clause(int cid) {
    int input_count = clause_count();
    int proof_count = proof_clauses.size();
    if (cid <= input_count)
	return get_input_clause(cid);
    else {
	Clause *np = get_aux_clause(cid);
	if (np != NULL)
	    return np;
	else if (cid <= input_count + proof_count)
	    return proof_clauses[cid - input_count - 1];
	else {
	    err(true, "Fatal.  Trying to access clause #%d.  Have %d input and %d proof clauses\n", cid, input_count, proof_count);
	    exit(1);
	}
    }
}


Clause * Cnf_reasoner::operator[](int cid) {
    return get_clause(cid);
}

bool Cnf_reasoner::is_unsatisfiable() {
    return unsatisfiable;
}

void Cnf_reasoner::activate_clause(int cid) {
    curr_active_clauses->insert(cid);
}

void Cnf_reasoner::deactivate_clause(int cid) {
    curr_active_clauses->erase(cid);
}

void Cnf_reasoner::deactivate_all_clauses() {
    curr_active_clauses->clear();
}

int Cnf_reasoner::add_proof_clause(Clause *clp) {
    int pcid = clause_count() + proof_clauses.size();
    if (pcid == clause_limit) {
	err(true, "Adding clause %ld exceeds limit\n", (long) pcid + 1);
    }
    int cid = pcid + 1;
    proof_clauses.push_back(clp);
    if (clp->length() == 0)
	unsatisfiable = true;
    else if (clp->length() == 1) {
	int lit = (*clp)[0];
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
    }
    return cid;
}

int Cnf_reasoner::start_assertion(Clause *clp, bool structural) {
    int cid = add_proof_clause(clp);
    if (structural)
	pwriter->start_structural_assertion(cid);
    else
	pwriter->start_assertion(cid);
    clp->write(pwriter);
#if DELETE_FULL
    std::vector<int> *dvp = new std::vector<int>();
    dvp->push_back(cid);
    asserting = true;   
    deletion_stack.push_back(dvp);
#endif
    return cid;
}

void Cnf_reasoner::add_hint(int hid) {
    pwriter->add_int(hid);
#if DELETE_FULL
    if (asserting) {
	std::vector<int> *dvp = deletion_stack.back();
	dvp->push_back(hid);
    }
#endif
}

void Cnf_reasoner::add_hints(Clause *hp) {
    for (int i = 0; i < hp->length(); i++) 
	add_hint((*hp)[i]);
}


void Cnf_reasoner::finish_command(bool add_zero) {
    if (add_zero)
	pwriter->finish_line("0");
    else
	pwriter->finish_line("");
    asserting = false;
}

void Cnf_reasoner::document_input(int cid) {
    ilist show = ilist_new(0);
    Clause *cp = get_clause(cid);
    show = ilist_push(show, cid);
    for (int i = 0; i < cp->length(); i++)
	show = ilist_push(show, (*cp)[i]);
    pwriter->comment_list("", show);
    ilist_free(show);
}

int Cnf_reasoner::start_and(int var, ilist args) {
    pwriter->comment("Operation P%d", var);
    Clause *clp = new Clause();
    clp->add(var);
    for (int i = 0; i < ilist_length(args); i++) 
	clp->add(-args[i]);
    int cid = add_proof_clause(clp);
    long ncid = (long) cid + ilist_length(args);
    if (ncid > clause_limit)
	err(true, "Adding operation with %d arguments starting with clause #%d exceeds limit\n", ilist_length(args), cid);
    for (int i = 0; i < ilist_length(args); i++) {
	Clause *aclp = new Clause();
	aclp->add(-var);
	aclp->add(args[i]);
	add_proof_clause(aclp);
    }
    pwriter->start_and(cid, var);
    pwriter->write_list(args);
    incr_count_by(COUNT_DEFINING_CLAUSE, ilist_length(args)+1);
    return cid;
}

void Cnf_reasoner::document_and(int cid, int var, ilist args) {
    if (verblevel < 2) 
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = var;
    for (int i = 0; i < len; i++)
	show[i+2] = -args[i];
    pwriter->comment_list("", show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = -var;
	show[2] = args[i];
	pwriter->comment_list("", show);
    }
    ilist_free(show);
}


int Cnf_reasoner::start_or(int var, ilist args) {
    if (weak_sum)
	pwriter->comment("Operation WS%d", var);
    else
	pwriter->comment("Operation S%d", var);
    int arg1 = args[0];
    int arg2 = args[1];
    Clause *clp = new Clause();
    clp->add(-var); clp->add(arg1); clp->add(arg2);
    int cid = add_proof_clause(clp);
    if (cid + ilist_length(args) > clause_limit)
	err(true, "Adding operation starting with clause #%d exceeds limit\n", cid);
    Clause *aclp1 = new Clause();
    aclp1->add(var); aclp1->add(-arg1);
    add_proof_clause(aclp1);
    Clause *aclp2 = new Clause();
    aclp2->add(var); aclp2->add(-arg2);
    add_proof_clause(aclp2);
    pwriter->start_or(cid, var, weak_sum);
    pwriter->add_int(arg1); pwriter->add_int(arg2);
    incr_count_by(COUNT_DEFINING_CLAUSE, ilist_length(args)+1);
    return cid;
}

void Cnf_reasoner::document_or(int cid, int var, ilist args) {
    if (verblevel < 2)
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    ilist_resize(show, len+2);
    show[0] = cid;
    show[1] = -var;
    for (int i = 0; i < len; i++)
	show[i+2] = args[i];
    pwriter->comment_list("", show);
    show = ilist_resize(show, 3);
    for (int i = 0; i < ilist_length(args); i++) {
	show[0] = cid+i+1;
	show[1] = var;
	show[2] = -args[i];
	pwriter->comment_list("", show);
    }
    ilist_free(show);
}

int Cnf_reasoner::start_skolem(int var, ilist args) {
    pwriter->comment("Operation T%d", var);
    Clause *clp = new Clause();
    clp->add(var);
    int cid = add_proof_clause(clp);
    long ncid = (long) cid;
    if (ncid > clause_limit)
	err(true, "Adding operation starting with clause #%d exceeds limit\n", ilist_length(args), cid);
    incr_count(COUNT_DEFINING_CLAUSE);
    if (use_explicit_deletion) {
	ncid += ilist_length(args);
	if (ncid > clause_limit)
	    err(true, "Adding operation with %d arguments starting with clause #%d exceeds limit\n", ilist_length(args), cid);
	for (int i = 0; i < ilist_length(args); i++) {
	    Clause *aclp = new Clause();
	    aclp->add(-var);
	    aclp->add(args[i]);
	    add_proof_clause(aclp);
	}
	incr_count_by(COUNT_DEFINING_CLAUSE, ilist_length(args));
    } else
	incr_count_by(COUNT_VIRTUAL_CLAUSE, ilist_length(args));
    pwriter->start_skolem(cid, var);
    pwriter->write_list(args);
    return cid;
}

void Cnf_reasoner::document_skolem(int cid, int var, ilist args) {
    if (verblevel < 2) 
	return;
    pwriter->comment("Implicit declarations");
    int len = ilist_length(args);
    ilist show = ilist_new(len+2);
    show = ilist_resize(show, 2);
    show[0] = cid;
    show[1] = var;
    pwriter->comment_list("", show);
    if (use_explicit_deletion) {
	show = ilist_resize(show, 3);
	for (int i = 0; i < ilist_length(args); i++) {
	    show[0] = cid+i+1;
	    show[1] = -var;
	    show[2] = args[i];
	    pwriter->comment_list("", show);
	}
    }
    ilist_free(show);
}

int Cnf_reasoner::assert_literal(int lit) {
    pwriter->comment("Assert %d as unit literal without proof", lit);
    Clause *clp = new Clause();
    clp->add(lit);
    int cid = start_assertion(clp, false);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    return cid;
}


// Got a new unit literal.
void Cnf_reasoner::new_unit(int lit, int cid, bool input) {
    if (input) {
	if (unit_literals.find(-lit) != unit_literals.end()) {
	    found_conflict(cid);
	    return;
	}
	unit_literals.insert(lit);
	justifying_ids[lit] = cid;
	report(3, "Unit literal %d justified by input clause #%d\n", lit, cid);
	return;
    }
    Clause *cp = get_clause(cid);
    int clen = cp->length();
    // Optimization: Don't generate new clause if unit implied by context literals
    bool need_new = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	if (justifying_ids.find(-clit) != justifying_ids.end())
	    need_new = true;
    }
    if (!need_new) {
	push_derived_literal(lit, cid);
	report(3, "Unit literal %d already justified by clause #%d\n", lit, cid);
	return;
    }
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
#if DEBUG
    pwriter->comment("Justified literal %d", lit);
#endif
    int ncid = start_assertion(clp, false);
    if (clp->length() == 1) {
	unit_literals.insert(lit);
    } else {
	push_derived_literal(lit, ncid);
    }
    // Print hints
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    add_hint(fid->second);
	}
    }
    add_hint(cid);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    report(3, "Unit literal %d justified by proof clause #%d\n", lit, ncid);
}

int Cnf_reasoner::quick_validate_literal(int lit, int cid1, int cid2) {
    Clause *clp = new Clause();
    clp->add(lit);
    for (int alit : assigned_literals)
	clp->add(-alit);
    int ncid = start_assertion(clp, false);
    if (clp->length() == 1) {
	unit_literals.insert(lit);
    } else {
	push_derived_literal(lit, ncid);
    }
    add_hint(cid1);
    add_hint(cid2);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    return ncid;
}

int Cnf_reasoner::found_conflict(int cid) {
    Clause *clp = NULL;
    int ncid = 0;
    // Print hints
    Clause *cp = get_clause(cid);
    int clen = cp->length();
    bool found_hint = false;
    for (int idx = 0; idx < clen; idx++) {
	int clit = (*cp)[idx];
	auto fid = justifying_ids.find(-clit);
	if (fid != justifying_ids.end()) {
	    if (!found_hint) {
		found_hint = true;
		clp = new Clause();
		for (int alit : assigned_literals)
		    clp->add(-alit);
#if DEBUG
		pwriter->comment("Conflict clause");
#endif
		ncid = start_assertion(clp, false);
	    }
	    add_hint(fid->second);
	}
    }
    if (!found_hint)
	return cid;
    if (clp->length() == 1) {
	unit_literals.insert((*clp)[0]);
    }
    add_hint(cid);
    finish_command(true);
    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
    report(3, "Conflict on clause #%d generated assertion clause #%d\n", cid, ncid);
    return ncid;
}

void Cnf_reasoner::reset_xvar() {
    xvar_count = max_variable();
}

int Cnf_reasoner::new_xvar() {
    return ++xvar_count;
}

// Enable POG generation
void Cnf_reasoner::enable_pog(Pog_writer *pw) {
    pwriter = pw;
    // Set up active clauses
    curr_active_clauses = new std::set<int>;
    next_active_clauses = new std::set<int>;

    // Scan all clauses.  Find unit clauses.  Register non-tautologies
    int cid = 0;
    for (Clause *cp : clauses) {
	cid++;
	if (cp->tautology())
	    continue;
	else if (cp->length() == 1) {
	    new_unit((*cp)[0], cid, true);
	    continue;
	}
	else
	    activate_clause(cid);
    }
    int ncid = bcp(false);
    if (ncid > 0) 
	pwriter->comment("Formula unsatisfiable (empty clause ID = %d)", ncid);
}

// Check status of two-literal watches.  Look for inconsistency
void Cnf_reasoner::check_watch_state(Watcher &watches, bool quiescent) {
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	int ucount = 0;
	int upos[2] = {0, 0};
	int ulit[2] = {0, 0};
	int satlit = 0;
	for (int idx = 0; idx < cp->length(); idx++) {
	    int clit = (*cp)[idx];
	    if (!watches.on_trail(clit) && unit_literals.find(clit) != unit_literals.end()) {
		satlit = clit;
		ucount = 0;
		break;
	    }
	    if (watches.on_trail(-clit) || unit_literals.find(-clit) == unit_literals.end()) {
		if (ucount < 2) {
		    ulit[ucount] = clit;
		    upos[ucount] = idx;
		}
		ucount++;
	    }
	}
	if (satlit > 0 && verblevel >= 3) {
	    report(3, "Clause #%d (satisfied by literal %d): ", cid, satlit);
	    cp->show(stdout);
	} else if (ucount == 0) {
	    if (verblevel >= 3) {
		report(3, "Clause #%d (conflicted) : ", cid);
		cp->show(stdout);
	    }
	    if (quiescent)
		err(false, "Clause #%d has conflict\n", cid);
	} else if (ucount == 1) {
	    if (verblevel >= 3) {
		report(3, "Clause #%d (unit on literal %d.  Unit position at %d): ", cid, ulit[0], upos[0]+1);
		cp->show(stdout);
	    }
	    // Should be on watch list
	    if (!watches.is_watching(cid, -ulit[0]) && quiescent)
		err(false, "Clause #%d unit on literal %d.  Unit position at %d.  But not on watch list for %d\n",
		    cid, ulit[0], upos[0]+1, -ulit[0]);
	    // Should be on trail
	    if (!watches.on_trail(ulit[0]) && quiescent)
		err(false, "Clause #%d unit on literal %d.  But literal not on trail\n", cid, ulit[0]);
	} else {
	    // Must be part of two-watched literal
	    if (verblevel >= 3) {
		report(3, "Clause #%d (%d unassigned literals)  Lit1 = %d (position %d), Lit2 = %d (position %d): ",
		       cid, ucount, ulit[0], upos[0]+1, ulit[1], upos[1]+1);
		cp->show(stdout);
	    }
	    for (int p = 0; p < 2; p++) {
		if (upos[p] != p && quiescent)
		    err(false, "Clause #%d.  Unassigned literal %d at position %d\n", cid, ulit[p], upos[p]+1);
		// Should be on watch list
		std::vector<int> *wlist = watches.get_list(ulit[p]);
		bool found = false;
		// Should be on watch list
		if (!watches.is_watching(cid, -ulit[p]) && quiescent)
		    err(false, "Clause #%d.  Watching literal %d at clause position %d.  Not on watch list.  %d literals unassigned\n",
			cid, -ulit[p], upos[p]+1, ucount);
	    }
	}
    }
}


// BCP support.  Perform unit propagation
// For given clause, have four possibilities:
// 1. The clause is satisfied.  Return 0
// 2. The clause has >= 2 unassigned literals.  Set up watch pointers.  Return 0
// 3. The clause has 1 unassigned literal.  Add this to unit_literals.  Return literal
// 4. The clause has a conflict.  Return CONFLICT_LIT

// The behavior is a bit different if this is the initial setup (first_pass = true) vs. regular BCP:
// In the first pass, ALL unassigned literals are moved to the beginning, and both watch pointers are assigned
// In other passes, the loop can exit when it's found two unassigned literals, and only the second watch pointer need be assigned
int Cnf_reasoner::bcp_unit_propagate(int cid, bool first_pass, Watcher &watches) {
    Clause *cp  = get_clause(cid);
    if (!cp)
	err(true, "Oops.  Couldn't get clause # %d\n", cid);
    int unassigned_count = 0;
    int watching[2] = {0, 0};
    int ulit = 0;
    if (!first_pass) {
	watching[0] = (*cp)[0];
	watching[1] = (*cp)[1];
    }
    if (cp->length() > 2) {
	// Possibly include this in checkpoint state	
	watches.watching(cid, (*cp)[0], (*cp)[1]);
    }
    for (int idx = 0; idx < cp->length(); idx++) {
	int clit = (*cp)[idx];
	if (unit_literals.find(clit) != unit_literals.end()) {
	    // Clause satisfied
	    report(3, "  Clause #%d satisfied by unit %d\n", cid, clit);
	    return ulit;
	}
	else if (unit_literals.find(-clit) == unit_literals.end()) {
	    // Literal unassigned.  Swap into place for next unassigned literal
	    cp->swap_literals(unassigned_count++, idx);
	    if (!first_pass && unassigned_count >= 2)
		break;
	}
    }
    if (unassigned_count == 0) {
	// Conflict
	report(3, "  Unit propagation got conflict on clause #%d\n", cid);
	return CONFLICT_LIT;
    }
    else if (unassigned_count == 1) {
	// Unit literal
	ulit = (*cp)[0];
	report(3, "  Unit propagation got unit literal %d on clause #%d\n", (*cp)[0], cid);
    } else {
	// Set up watch pointers
	int wlit0 = (*cp)[0];
	int wlit1 = (*cp)[1];
	if (wlit0 != watching[0] && wlit0 != watching[1]) {
	    watches.add_clause_id(cid, -wlit0);
	    report(3, "  Clause #%d put on watch list for literal %d\n", cid, -wlit0);
	}
	if (wlit1 != watching[0] && wlit1 != watching[1]) {
	    watches.add_clause_id(cid, -wlit1);
	    report(3, "  Clause #%d put on watch list for literal %d\n", cid, -wlit1);
	}
    }
    return ulit;
}

// Check that clause is neither satisfied nor falsified
bool Cnf_reasoner::is_active(int cid) {
    int unassigned_count = 0;
    Clause *cp  = get_clause(cid);
    for (int idx = 0; idx < cp->length(); idx++) {
	int clit = (*cp)[idx];
	if (unit_literals.find(clit) != unit_literals.end())
	    // Satisfied
	    return false;
	if (unit_literals.find(-clit) == unit_literals.end())
	    unassigned_count++;
    }
    return unassigned_count > 0;
}

// New BCP code

// Perform Boolean constraint propagation
// Return ID of any generated conflict clause (or 0)
// Update set of active clauses
int Cnf_reasoner::bcp(bool bounded) {
    bool conflict = false;
    int ncid = 0;
    int pcount = 0;
    // Support for two-watched literals in BCP
    // Watch lists.  Map from literal to set of clause Ids 
    Watcher watches;

#if VLEVEL >= 3
    if (verblevel >= 3) {
	report(3, "Starting BCP.  Active clauses:");
	for (int cid : *curr_active_clauses)
	    lprintf(" %d", cid);
	lprintf("\n");
	report(3, "    Unit literals:");
	for (int ulit : unit_literals)
	    lprintf(" %d", ulit);
	lprintf("\n");
    }
#endif

    // Set up watch pointers
    for (int cid : *curr_active_clauses) {
	int ulit = bcp_unit_propagate(cid, true, watches);
	conflict = ulit == CONFLICT_LIT;
	if (conflict) {
	    ncid = found_conflict(cid);
	    break;
	} else if (ulit != 0) {
	    new_unit(ulit, cid, false);
	    watches.add_unit(ulit, cid);
	}
    }

    while (!conflict) {
	int plit = watches.get_unit();
	if (plit == 0)
	    break;

	if (bounded && pcount >= bcp_limit && curr_active_clauses->size() >= drat_threshold) 
	    break;
	pcount++;

	std::vector<int> *wlist = watches.get_list(plit);
#if VLEVEL >= 3
	if (verblevel >= 3) {
	    report(3, "Unit propagating on literal %d.  Watch list:", plit);
	    for (int cid : *wlist)
		lprintf(" %d", cid);
	    lprintf("\n");
	}
#endif
	for (int cid : *wlist) {
	    int ulit = bcp_unit_propagate(cid, false, watches);
	    conflict = ulit == CONFLICT_LIT;
	    if (conflict) {
		ncid = found_conflict(cid);
		break;
	    } else if (ulit != 0) {
		new_unit(ulit, cid, false);
		watches.add_unit(ulit, cid);
	    }
	}
    }
    // Construct new active clause set
    for (int cid : *curr_active_clauses) {
	if (is_active(cid))
	    next_active_clauses->insert(cid);
	else 
	    push_clause(cid, false);
    }
    // Swap active clause sets
    std::set<int> *tmp =  curr_active_clauses;
    curr_active_clauses = next_active_clauses;
    next_active_clauses = tmp;
    next_active_clauses->clear();
#if VLEVEL >= 3
    if (verblevel >= 3) {
	if (ncid == 0) {
	    report(3, "  BCP completed, but didn't find conflict\n");
	} else {
	    report(3, "  BCP completed.  Returning ncid %d.  New active clauses:", ncid);
	    for (int cid : *curr_active_clauses)
		lprintf(" %d", cid);
	    lprintf("\n");
	}
    }
#endif
    return ncid;
}

// New RUP code

// Set up watch pointers and unit propagate assigned literals
// Return true if get conflict
bool Cnf_reasoner::watches_setup(Watcher &watches) {
    bool conflict = false;

    report(3, "Initializing watcher state\n");
    // Initialize with all known units:
    for (int ulit : unit_literals) {
	auto fid = justifying_ids.find(ulit);
	if (fid != justifying_ids.end()) {
	    watches.add_unit(ulit, fid->second);
	    report(3, "Added unit %d with justifying clause #%d to watches\n", ulit, fid->second);
	} else
	    watches.add_unit(ulit, 0);
    }

    report(3, "Initializing watch pointers\n");
    for (int cid : *curr_active_clauses) {
	int ulit = bcp_unit_propagate(cid, true, watches);
	conflict = ulit == CONFLICT_LIT;
	if (conflict) {
	    report(3, "   Conflict encountered with clause #%d while setting up watch pointers\n", cid);
	    break;
	} else if (ulit != 0) {
	    push_derived_literal(ulit, cid);
	    watches.add_unit(ulit, cid);
	    report(3, "   Propagated unit %d with clause #%d while setting up watch pointers\n", ulit, cid);
	}
    }

#if TWL_CHECK
    report(3, "Checking initial watch state\n");
    check_watch_state(watches, false);
#endif

    // Unit propagate initial units
    while (!conflict) {
	int plit = watches.get_unit();
	if (plit == 0)
	    break;
	std::vector<int> *wlist = watches.get_list(plit);
#if VLEVEL >= 3
	if (verblevel >= 3) {
	    report(3, "Unit propagating on literal %d while setting up watch pointers.  Watch list:", plit);
	    for (int cid : *wlist)
		lprintf(" %d", cid);
	    lprintf("\n");
	}
#endif
	for (int cid : *wlist) {
	    int ulit = bcp_unit_propagate(cid, false, watches);
	    conflict = ulit == CONFLICT_LIT;
	    if (conflict) {
		report(3, "   Conflict encountered with clause #%d while setting up watch pointers (unit propagating)\n", cid);
		break;
	    } else if (ulit != 0) {
		push_derived_literal(ulit, cid);
		watches.add_unit(ulit, cid);
		report(3, "   Propagated unit %d with clause #%d while setting up watch pointers\n", ulit, cid);
	    }
	}
    }

#if TWL_CHECK
    report(3, "Checking after initial BCP\n");
    check_watch_state(watches, true);
#endif

    return conflict;
}

// Generate set of hints for clause based on RUP validation
// Optionally Add clause as assertion
// With add_clause = true, return ID of proof clause.  Otherwise return 0
// Does not change the set of active clauses
int Cnf_reasoner::rup_validate(Clause *cltp, bool add_clause, Watcher &watches, std::vector<int> &hints) {

#if VLEVEL >= 3
    if (verblevel >= 3) {
	report(3, "Starting RUP derivation of clause ");
	cltp->show(stdout);
	lprintf("   Unit literals:");
	for (int ulit : unit_literals)
	    lprintf(" %d", ulit);
	lprintf("\n");
    }
#endif

    // Start tracking changes so that can revert back later
    new_context();
    watches.checkpoint();

    // Negate literals in target clause
    int lcount = 0;
    for (int idx = 0; idx < cltp->length(); idx++) {
	int tlit = (*cltp)[idx];
	if (unit_literals.find(-tlit) == unit_literals.end()) {
	    push_assigned_literal(-tlit);
	    watches.add_unit(-tlit, 0);
	    report(3, "  Pushed literal: %d\n", -tlit);
	    lcount++;
	} else
	    report(3, "  Already have literal: %d\n", -tlit);
    }

#if VLEVEL >= 3
    if (verblevel >= 3) {
	if (lcount == 0)
	    report(3, "Starting RUP.  All literals contradicted\n");
	else {
	    report(3, "Starting BCP in RUP validation.  Active clauses:");
	    for (int cid : *curr_active_clauses)
		lprintf(" %d", cid);
	    lprintf("\n  Unit literals:");
	    for (int ulit : unit_literals)
		lprintf(" %d", ulit);
	    lprintf("\n");
	}
    }
#endif

    int ncid = 0;
    bool conflict = false;
    int conflict_cid;

    // Unit propagation
    while (!conflict) {
#if TWL_CHECK
	report(3, "Checking at start of Loop\n");
	check_watch_state(watches, false);
#endif
	int plit = watches.get_unit();
	if (plit == 0)
	    break;
	std::vector<int> *wlist = watches.get_list(plit);
#if VLEVEL >= 3
	if (verblevel >= 3) {
	    report(3, "Unit propagating on literal %d.  Watch list:", plit);
	    for (int cid : *wlist)
		lprintf(" %d", cid);
	    lprintf("\n");
	}
#endif
	for (int cid : *wlist) {
	    int ulit = bcp_unit_propagate(cid, false, watches);
	    conflict = ulit == CONFLICT_LIT;
	    if (conflict) {
		report(3, "   Conflict encountered with clause #%d\n", cid);
		// Hack: Put conflict clause at end of trail to pick up with hint
		watches.add_unit(CONFLICT_LIT, cid);
		conflict_cid = cid;
		break;
	    } else if (ulit != 0) {
		push_derived_literal(ulit, cid);
		watches.add_unit(ulit, cid);
		report(3, "   Propagated unit %d with clause #%d\n", ulit, cid);
	    }
	}
    }

    if (conflict) {
	if (conflict_cid == 0)
	    err(false, "Couldn't find conflict clause during RUP validation\n");
	else
	    report(3, "Conflict clause found.  Constructing hints\n");
	// Construct hints in reverse order
	hints.clear();
	std::unordered_set<int> used_set;
	std::vector<Tele> *trail = watches.get_trail();
	if (conflict_cid > 0)
	    used_set.insert(conflict_cid);
	for (int idx = trail->size()-1; idx >= 0; idx--) {
	    int hid = (*trail)[idx].cid;
	    if (hid == 0)
		continue;
	    if (used_set.find(hid) != used_set.end()) {
		hints.push_back(hid);
		report(4, "  Clause #%d added to hints\n", hid);
		Clause *clp = get_clause(hid);
		for (int idx = 0; idx < clp->length(); idx++) {
		    int lit = (*clp)[idx];
		    auto fid = justifying_ids.find(-lit);
		    if (fid != justifying_ids.end()) {
			int jid = fid->second;
			used_set.insert(jid);
			report(4, "    Literal %d justified by clause #%d\n", -lit, jid);
		    } else
			report(4, "    No justifying clause found for literal %d\n", -lit);
		}
	    } else
		report(4, "  Clause #%d not needed as hint\n", hid);
	}

	if (hints.size() == 0)
	    err(false, "Couldn't generate hints for added clause #%d\n", ncid);


	// Put hints in proper order
	std::reverse(hints.begin(), hints.end());
	if (add_clause) {
	    // Add clause to proof
	    ncid = start_assertion(cltp, false);
	    for (int hid : hints)
		add_hint(hid);
	    finish_command(true);
	    incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
	    activate_clause(ncid);
	    report(3, "  RUP validation completed.  Asserted clause #%d\n", ncid);
	}
    } else {
	err(false, "RUP validation failed\n");
	printf("  Target clause: ");
	cltp->show(stdout);
	printf("  Unit literals: ");
	for (int ulit : unit_literals) 
	    printf(" %d", ulit);
	printf("\n");
	// This checking is part of the post-mortem
	check_watch_state(watches, true);
    }
    // Undo assignments
    // Must fix up literal positions in clauses
    std::unordered_map<int,Literal_pair> *pairs = watches.get_watched_pairs();
    for (auto iter : *pairs) {
	int cid = iter.first;
	Clause *cp = get_clause(cid);
	Literal_pair lits = iter.second;
	report(3, "Resetting clause #%d to have literals %d and %d at beginning\n", cid, lits.lit1, lits.lit2);
	cp->rearrange(lits);
    }
    watches.restore();
    pop_context();
#if TWL_CHECK
    report(3, "Checking after popping context\n");
    check_watch_state(watches, false);
#endif

    // Set up watch pointers for the last added RUP clause
    if (ncid != 0) {
	int ulit = bcp_unit_propagate(ncid, true, watches);
	conflict = ulit == CONFLICT_LIT;
	if (conflict)
	    report(3, "   Conflict encountered with clause #%d generated by RUP step\n", ncid);
	else if (ulit != 0) {
	    push_derived_literal(ulit, ncid);
	    watches.add_unit(ulit, ncid);
	    report(3, "   Propagated unit %d with clause #%d generated by RUP step\n", ulit, ncid);
	}
    }

    return ncid;
}

// Used to mark new layer in context stacks
#define CONTEXT_MARKER 0

void Cnf_reasoner::new_context() {
    context_literal_stack.push_back(CONTEXT_MARKER);
    context_cleared_literal_stack.push_back(CONTEXT_MARKER);
    context_clause_stack.push_back(CONTEXT_MARKER);
    report(4, "New context\n");
}

std::vector<int> *Cnf_reasoner::get_assigned_literals() {
    return &assigned_literals;
}

std::unordered_map<int, int> *Cnf_reasoner::get_justifying_ids() {
    return &justifying_ids;
}

void Cnf_reasoner::push_assigned_literal(int lit) {
    if (unit_literals.find(lit) != unit_literals.end()) {
	err(false, "Attempt to assert literal %d.  But, it is already unit\n", lit);
#if DEBUG
	pwriter->comment("Attempt to assert literal %d.  But, it is already unit", lit);
	pwriter->comment_container("  Current unit literals", unit_literals);
#endif 
    }

    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to assert literal %d.  But, already have %d as unit\n", lit, -lit); {
#if DEBUG
	pwriter->comment("Attempt to assert literal %d.  But, already have %d as unit", lit, -lit);
	pwriter->comment_container("  Current unit literals", unit_literals);
#endif
    }

    report(4, "Asserting literal %d\n", lit);
    unit_literals.insert(lit);
    assigned_literals.push_back(lit);
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_derived_literal(int lit, int cid) {
    if (unit_literals.find(-lit) != unit_literals.end())
	err(false, "Attempt to add unit literal %d.  But, already have derived -%d as unit\n", lit, lit);
    if (unit_literals.find(lit) != unit_literals.end())
	err(false, "Attempt to add unit literal %d.  But, it is already unit\n", lit);
    unit_literals.insert(lit);
    justifying_ids[lit] = cid;
    context_literal_stack.push_back(lit);
}

void Cnf_reasoner::push_clause(int cid, bool force) {
    if (force || cid <= clause_count() || aux_clauses.find(cid) != aux_clauses.end())
	context_clause_stack.push_back(cid);
}

void Cnf_reasoner::pop_context() {
    report(4, "Popping context\n");
    // It's important to first clear the assigned literals
    // and then assign the previously literals.
    // There are cases when both operations are performed for a single
    // literal, and it's important that the net result is to set it to its former value.
    while (true) {
	if (context_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context literal stack\n");
	int lit = context_literal_stack.back(); context_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	unit_literals.erase(lit);
	if (auto fid = justifying_ids.find(lit) == justifying_ids.end()) {
	    report(4, "  Removing assertion of literal %d\n", lit);
	    assigned_literals.pop_back();
	} else {
	    justifying_ids.erase(lit);
	    report(4, "  Removing derivation of literal %d\n", lit);
	}
    }
    while (true) {
	if (context_cleared_literal_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context cleared literal stack\n");
	int lit = context_cleared_literal_stack.back(); context_cleared_literal_stack.pop_back();
	if (lit == CONTEXT_MARKER)
	    break;
	report(4, "Reasserting literal %d\n", lit);
	unit_literals.insert(lit);
	assigned_literals.push_back(lit);
    }
    while (true) {
	if (context_clause_stack.size() == 0)
	    err(true, "Tried to pop beyond base of context clause stack\n");
	int cid = context_clause_stack.back(); context_clause_stack.pop_back();
	if (cid == CONTEXT_MARKER)
	    break;
	activate_clause(cid);
	report(4, "  Reactivating clause #%d\n", cid);
    }
}

void Cnf_reasoner::clear_assigned_literals() {
    while (assigned_literals.size() > 0) {
	int alit = assigned_literals.back(); assigned_literals.pop_back();
	unit_literals.erase(alit);
	context_cleared_literal_stack.push_back(alit);
	report(4, "Cleared assigned literal %d\n", alit);
    }
}


static void copy_set(std::set<int> *dest, std::set<int> *src) {
    dest->clear();
    for (int v : *src)
	dest->insert(v);
}

void Cnf_reasoner::extract_active_clauses(std::set<int> *save_set) {
    copy_set(save_set, curr_active_clauses);
}

void Cnf_reasoner::set_active_clauses(std::set<int> *new_set) {
    copy_set(curr_active_clauses, new_set);
}


// Partition set of active clauses into subsets, each using distinct sets of variables
// Each set denoted by reference variable
// var2rvar provides a mapping from each variable to the containing set's reference variable
// rvar2cset provides a mapping from the reference variable to the set of clauses
void Cnf_reasoner::partition_clauses(std::unordered_map<int,int> &var2rvar,
				     std::unordered_map<int,std::set<int>*> &rvar2cset) {
    // Simplify clauses
    int ccid = bcp(false);
    if (ccid > 0)
	err(true, "BCP generated conflict on clause #%d prior to partitioning\n", ccid);
    // First figure out a partitioning of the variables
    // Map from variable to representative value in its partition
    // Mapping from representative var to set of variables
    var2rvar.clear();
    std::map<int,std::unordered_set<int>*> rvar2vset;
    if (verblevel >= 3) {
	ilist ulist = ilist_new(unit_literals.size());
	for (int lit : unit_literals)
	    ulist = ilist_push(ulist, lit);
	ilist_abs_sort(ulist);
	printf("c  Unit literals:");
	ilist_print(ulist, stdout, " ");
	printf("\n");
	lprintf("c  Active clauses:");
	for (int acid : *curr_active_clauses)
	    lprintf(" %d", acid);
	lprintf("\n");
    }
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	int rvar = 0;
	std::unordered_set<int> *nset = NULL;
	report(3, "Clause #%d.  Setup\n", cid);
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    if (unit_literals.find(-lit) != unit_literals.end())  {
		// Literal currently falsified
		report(3, "    Literal %d.  Skipping\n", lit);
		continue;
	    }
	    if (unit_literals.find(lit) != unit_literals.end())  {
		// Clause satisfied.  This is not expected
		err(true, "Satisfied clause #%d (unit literal %d) found during clause partitionning\n",
		    cid, lit);
		return;
	    }
	    auto fid = var2rvar.find(var);
	    if (fid != var2rvar.end()) {
		if (rvar == 0) {
		    rvar = fid->second;
		    nset = rvar2vset.find(rvar)->second;
		    report(3, "    Variable %d.  Joining partition with rvar %d\n", var, rvar);
		    continue;
		} else {
		    report(3, "    Variable %d.  In different group\n", var);
		    continue;
		}
	    }
	    if (rvar == 0) {
		rvar = var;
		nset = new std::unordered_set<int>;
		rvar2vset[rvar] = nset;
	    }
	    var2rvar[var] = rvar;
	    nset->insert(var);
	    if (rvar == var)
		report(3, "  Setting up partition with rvar %d\n", rvar);
	    else
		report(3, "    Adding variable %d to partition with rvar %d\n", var, rvar);
	}
    }
    // Merge partitions
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	int i1, rvar1;
	std::unordered_set<int>*set1;
	for (i1 = 0; i1 < cp->length(); i1++) {
	    int lit1 = (*cp)[i1];
	    int var1 = IABS(lit1);
	    auto fid1 = var2rvar.find(var1);
	    if (fid1 == var2rvar.end())
		// Inactive variable
		continue;
	    rvar1 = fid1->second;
	    set1 = rvar2vset.find(rvar1)->second;
	    report(3, "Clause #%d, variable %d rvar %d.  Ready for merging\n", cid, var1, rvar1);
	    break;
	}

	for (int i2 = i1+1; i2 < cp->length(); i2++) {
	    int lit2 = (*cp)[i2];
	    int var2 = IABS(lit2);
	    auto fid2 = var2rvar.find(var2);
	    if (fid2 == var2rvar.end())
		// Inactive variable
		continue;
	    int rvar2 = fid2->second;
	    if (rvar1 == rvar2)
		// Already merged
		continue;
	    std::unordered_set<int>*set2 = rvar2vset.find(rvar2)->second;
	    // Merge smaller into larger
	    if (set1->size() >= set2->size()) {
		report(3, "     Variable %d.  Merging variables with rvar = %d into those with rvar = %d (Case 1)\n",
		       var2, rvar2, rvar1);
		for (int mvar : *set2) {
		    set1->insert(mvar);
		    var2rvar[mvar] = rvar1;
		}
		rvar2vset.erase(rvar2);
		delete(set2);
	    } else {
		report(3, "     Variable %d.  Merging variables with rvar = %d into those with rvar = %d (Case 2)\n",
		       var2, rvar1, rvar2);
		for (int mvar : *set1) {
		    set2->insert(mvar);
		    var2rvar[mvar] = rvar2;
		}
		rvar2vset.erase(rvar1);
		delete(set1);
		// rvar2 becomes the new representative
		rvar1 = rvar2;
		set1 = set2;
	    }
	}
    }
    rvar2cset.clear();
    for (auto fid : rvar2vset) {
	int rvar = fid.first;
	// Don't need variable set anymore
	delete fid.second;
	std::set<int> *cset = new std::set<int>;
	rvar2cset[rvar] = cset;
    }
    // Assign clauses to sets
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	for (int i = 0; i < cp->length(); i++) {
	    int lit = (*cp)[i];
	    int var = IABS(lit);
	    auto fid = var2rvar.find(var);
	    if (fid == var2rvar.end())
		continue;
	    int rvar = fid->second;
	    std::set<int> *cset = rvar2cset.find(rvar)->second;
	    cset->insert(cid);
	    break;
	}
    }
}

Cnf_reduced *Cnf_reasoner::extract_cnf() {
    Cnf_reduced *rcp = new Cnf_reduced();
    rcp->delete_files = delete_files;
    for (int cid : *curr_active_clauses) {
	Clause *np = get_clause(cid);	
	rcp->add_clause(np, unit_literals, cid);
    }
    return rcp;
}

// Filter out the unit literals that are required for proof, given the main clause and the hint clauses
void Cnf_reasoner::filter_units(Clause *pnp, Clause *php, std::unordered_set<int> &units) {
    units.clear();
    for (int i = 0; i < pnp->length(); i++) {
	int lit = (*pnp)[i];
	if (unit_literals.find(-lit) != unit_literals.end())
	    units.insert(-lit);
    }
    for (int i = 0; i < php->length(); i++) {
	int cid = (*php)[i];
	Clause *hcp = get_clause(cid);
	for (int hi = 0; hi < hcp->length(); hi++) {
	    int lit = (*hcp)[hi];
	    if (unit_literals.find(-lit) != unit_literals.end())
		units.insert(-lit);
	}
    }
}

// Run SAT solver on reduced set of clauses as part of effort to validate literal lit.
// Incorporate generated conflict proof into larger proof
// Return ID of conflict clause
int Cnf_reasoner::reduce_run(int lit) {
    int ncid = 0;
    Cnf_reduced *rcp = extract_cnf();
    if (rcp->clause_count() == 0) {
	err(false, "CNF reduces to tautology when attempting to validate literal %d\n", lit);
	return 0;
    }
    std::unordered_set<int> real_units;
    if (rcp->clause_count() >= drat_threshold) {
	if (rcp->run_hinting_solver()) {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("Adding %d proof clauses from SAT solver running on file %s to validate literal %d", (int) proof_clauses.size(), fname, lit);
	    int pcount = 0;
	    int start_id = clause_count() + proof_clauses.size() + 1;
	    while (true) {
		Clause *php = rcp->get_proof_hint(start_id);
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = start_assertion(pnp, false);
		// Add extra information about unit literals
		filter_units(pnp, php, real_units);
		for (int ulit : real_units) {
		    auto fid = justifying_ids.find(ulit);
		    if (fid != justifying_ids.end()) {
			int hid = fid->second;
			if (hid != ncid)
			    add_hint(hid);
		    }
		}
		add_hints(php);
		finish_command(true);
		incr_count(COUNT_LITERAL_JUSTIFICATION_CLAUSE);
		delete php;
	    }
	    pwriter->comment("End of proof clauses from SAT solver");
	}
    } else {
	// Want to keep track of range of clauses
	int first_ncid = 0;
	if (rcp->run_solver()) {
	    const char *fname = rcp->get_file_name();
	    report(3, "Adding proof clauses from SAT solver running on file %s to validate literal %d\n", fname, lit);
	    pwriter->comment("Adding proof clauses from SAT solver running on file %s to validate literal %d", fname, lit);
	    int pcount = 0;
	    Watcher watches;
	    std::vector<int> hints;
	    bool fail = false;
	    // Form local context for duration of RUP validation
	    new_context();
#if LOG
	    double start = tod();
#endif
	    // Shouldn't encounter conflict
	    fail = watches_setup(watches);
	    while (!fail) {
		Clause *pnp = rcp->get_proof_clause(&assigned_literals);
		if (pnp == NULL)
		    break;
		pcount++;
		ncid = rup_validate(pnp, true, watches, hints);
		if (first_ncid == 0)
		    first_ncid = ncid;
		fail = ncid == 0;
		if (fail) {
		    err(false, "SAT solver running on file %s failed to validate proof clause #%d/%d while validating literal %d\n",
			fname, pcount, rcp->get_proof_size(), lit);
#if VLEVEL >= 3
		    if (verblevel >= 3) {
			lprintf("Target clause: ");
			pnp->show();
		    }
#endif
		}
	    }
#if LOG
	    double micro = (tod() - start) * 1e6;
	    log_data("r,%u,%d,%d,%.0f\n", rcp->hash(), rcp->clause_count(), pcount, micro);
#endif
	    pop_context();
	    report(3, "Completed adding proof clauses from SAT solver running on file %s to validate literal %d\n", fname, lit);
	    pwriter->comment("End of proof clauses from SAT solver running on file %s", fname);

	    // The clauses used in generating this proof are no longer needed
	    for (int cid = first_ncid; cid <= ncid; cid++)
		deactivate_clause(cid);
	}  else {
	    const char *fname = rcp->get_file_name();
	    pwriter->comment("SAT solver failed running on file %s to validate literal %d", fname, lit);
	}
    }
    delete rcp;
    return ncid;
}

// Justify that literal holds.  Return ID of justifying clause
// Mode specifies different levels of effort
int Cnf_reasoner::validate_literal(int lit, validation_mode_t mode) {
    auto fid = justifying_ids.find(lit);
    if (fid != justifying_ids.end())
	return fid->second;
    if (unit_literals.find(lit) != unit_literals.end())
	return 0;
    int ncid = 0;
    new_context();
    push_assigned_literal(-lit);
    if (mode != MODE_SAT && bcp_limit > 0)
	ncid = bcp(mode == MODE_BBCP);
    if (ncid == 0 && mode != MODE_BCP && mode != MODE_BBCP)
	ncid = reduce_run(lit);
    pop_context();
    if (ncid != 0 && unit_literals.find(lit) == unit_literals.end())
	push_derived_literal(lit, ncid);
    return ncid;
}

// Justify that set of literals hold.
// Justifying clauses IDs are then loaded into jids vector
bool Cnf_reasoner::validate_literals(std::vector<int> &lits, std::vector<int> &jids) {
    jids.resize(lits.size());
    validation_mode_t mode = multi_literal ? MODE_BBCP : MODE_FULL;
    // Which literals can't be handled directly.  Put their negations on list
    ilist args = ilist_new(0);
    // Map them back to positions in lits & jids
    std::unordered_map<int,int> lit2idx;

#if DEBUG
    pwriter->comment_container("Target literals:", lits);
    pwriter->comment_container("Unit literals:", unit_literals);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
#endif

    // First pass: 
    // In standard mode, validate each literal separately
    // In multi_literal mode, look for easy cases.  Defer the rest
    for (int i = 0; i < lits.size(); i++) {
	int lit = lits[i];
	int jid = validate_literal(lit, mode);
	jids[i] = jid;
	if (jid == 0) {
	    args = ilist_push(args, -lit);
	    lit2idx[-lit] = i;
	}
    }

    int nleft = ilist_length(args);

    if (nleft == 0) {
	ilist_free(args);
	return true;
    }

    if (nleft == 1) {
	// Handle as single literal
	int nlit = args[0];
	int  i = lit2idx.find(nlit)->second;
	// Change sign
	jids[i] = validate_literal(-nlit, MODE_FULL);
	bool ok = jids[i] != 0;
	if (!ok) {
	    err(false, "Failed to validate literal %d\n", nlit);
	    lprintf("c  Unit literals:");
	    for (int lit : unit_literals)
		lprintf(" %d", lit);
	    lprintf("\n");
	    lprintf("c  Active clauses:");
	    for (int acid : *curr_active_clauses)
		lprintf(" %d", acid);
	    lprintf("\n");
	}
	ilist_free(args);
	return ok;
    }

    int defining_cid = find_or_make_aux_clause(args);
    ilist_free(args);
    Clause *anp = get_aux_clause(defining_cid);
    int xvar = -anp->get_activating_literal();

    // Activate conjunction definition
    activate_clause(defining_cid);
    pwriter->comment("Handle %d/%d literals with SAT solver to validate extension variable %d", nleft, lits.size(), xvar);
    report(3, "Handle %d/%d literals with SAT solver to validate extension variable %d\n", nleft, lits.size(), xvar);
    int ncid = validate_literal(xvar, MODE_FULL);
    // Literals might have been permuted
    anp->canonize();
    if (ncid > 0) {
	// Final pass: Target units should be unit or provable with BCP
	for (int i = 0; i < nleft; i++) {
	    int nlit = (*anp)[i];
	    int idx = lit2idx.find(nlit)->second;
	    int jid = quick_validate_literal(-nlit, ncid, defining_cid+i+1);
	    jids[idx] = jid;
	}
	pwriter->comment("Justifications of %d literals completed", nleft);
	deactivate_clause(defining_cid);
	return true;
    } else {
	// Try doing the validations individually
	deactivate_clause(defining_cid);
	err(false, "Couldn't validate literal %d representing conjunction of %d literals\n", xvar, nleft);
	return false;
	err(false, "Couldn't validate literal %d representing conjunction of %d literals.  Try validating individually\n", xvar, nleft);
	for (int i = 0; i < nleft; i++) {
	    int nlit = (*anp)[i];
	    int idx = lit2idx.find(nlit)->second;
	    int jid = validate_literal(-nlit, MODE_FULL);
	    if (jid == 0) {
		err(false, "Failed to validate literal %d\n", nlit);
		lprintf("c  Assigned literals:");
		for (int lit : assigned_literals)
		    lprintf(" %d", lit);
		lprintf("\n");
		lprintf("c  Active clauses:");
		for (int acid : *curr_active_clauses)
		    lprintf(" %d", acid);
		lprintf("\n");
		return false;
	    }
	    jids[idx] = jid;
	}
	return true;
    }
}

void Cnf_reasoner::delete_assertions() {
#if DELETE_FULL
    pwriter->comment("Delete all but final asserted clause");
    bool remove = false;
    while (deletion_stack.size() > 0) {
	std::vector<int> *dvp = deletion_stack.back();
	if (remove) {
	    pwriter->clause_deletion(dvp);
	    if (dvp->size() > 0)
		incr_count_by(COUNT_DELETION_HINT, dvp->size() - 1);
	}
	remove = true;
	delete dvp;
	deletion_stack.pop_back();
    }
#endif
}

// Managing set of auxilliary clauses as arguments to lemmas

Clause *Cnf_reasoner::get_aux_clause(int cid) {
    auto fid = aux_clauses.find(cid);
    return fid == aux_clauses.end() ? NULL : fid->second;
}

// Either find an existing auxilliary clause
// or generate one.
// Leaves argument clause untouched.
int Cnf_reasoner::find_or_make_aux_clause(ilist lits) {
    Clause *np = new Clause(lits, ilist_length(lits));
    np->canonize();
    unsigned h = np->hash();
    auto bucket = aux_clause_lookup.equal_range(h);
    for (auto iter = bucket.first; iter != bucket.second; iter++) {
	int xcid = iter->second;
	Clause *xcp = get_aux_clause(xcid);
	if (xcp == NULL)
	    err(false, "Oops.  Lookup table has clause #%d under hash %u, but no such clause exists\n", xcid, h);
	else if (np->is_equal(xcp)) {
#if VLEVEL >= 3
	    if (verblevel >= 3) {
		report(3, "Retrieved existing aux clause #%d.  Hash = %u. ", xcid, h);
		xcp->show();
	    }
#endif
	    delete np;
	    return xcid;
	}
    }
    // Must create new synthetic clause
    int xvar = new_xvar();
    int len = np->length();
    ilist args = ilist_new(len);
    for (int i = 0 ; i < len; i++)
	args = ilist_push(args, -(*np)[i]);
    incr_count(COUNT_AUX_AND);
    incr_count_by(COUNT_DEFINING_AUX_CLAUSE, len+1);
    int defining_cid = start_and(xvar, args);
    finish_command(false);
    document_and(defining_cid, xvar, args);
    Clause *nnp = new Clause(np);
    nnp->set_activating_literal(-xvar);
    aux_clauses[defining_cid] = nnp;
    aux_clause_lookup.insert({h, defining_cid});
#if VLEVEL >= 3
    if (verblevel >= 4) {
	report(4, "Generated new aux clause #%d.  Hash = %u. ", defining_cid, h);
	nnp->show();
    }
#endif
    return defining_cid;
}

// Lemma support
void Lemma_instance::sign(int xv, int split_lit) {
    next = NULL;
    jid = 0;
    xvar = xv;
    splitting_literal = split_lit;
    unsigned sig = 1;
    sig = next_hash_int(sig, split_lit);
    for (auto fid : inverse_cid) {
	int ncid = fid.first;
	sig = next_hash_int(sig, ncid);
    }
    signature = sig;
    jid = 0;
}

// Add active clause to lemma.  It will simplify the clause
// and find/create a synthetic clause to serve as the argument
void Cnf_reasoner::add_lemma_argument(Lemma_instance *lemma, int cid) {
    Clause *np = get_clause(cid);
    ilist slits = np->simplify(unit_literals);
    if (slits == NULL) 
	// Tautology 
	return;
    int ncid = ilist_length(slits) == np->length() ? cid : find_or_make_aux_clause(slits);
    auto fid = lemma->inverse_cid.find(ncid);
    if (fid == lemma->inverse_cid.end()) {
	lemma->inverse_cid[ncid] = cid;
#if DEBUG
	if (ncid == cid)
	    pwriter->comment("  Clause #%d used as direct argument", cid);
	else
	    pwriter->comment("  Clause #%d serves as proxy for clause #%d", ncid, cid);
#endif
    } else if (ncid == cid && fid->second != cid) {
	int ocid = fid->second;
	lemma->duplicate_cid.insert(ocid);
#if DEBUG
	pwriter->comment("  Use clause #%d directly, rather than having it be proxy for clause #%d", cid, ocid);
#endif
	lemma->inverse_cid[ncid] = cid;
    } else {
	lemma->duplicate_cid.insert(cid);
#if DEBUG
	pwriter->comment("  Don't need clause #%d as proxy for clause #%d", ncid, cid);
#endif
    }
    ilist_free(slits);
}

void Cnf_reasoner::check_for_unit(int lit) {
    if (unit_literals.find(lit) != unit_literals.end()) {
	report(1, "Checking literal %d.  Unit\n", lit);
	return;
    }
    if (unit_literals.find(-lit) != unit_literals.end()) {
	report(1, "Checking literal %d.  Falsified\n", lit);
	return;
    }
    bool found = false;
    for (int cid : *curr_active_clauses) {
	Clause *cp = get_clause(cid);
	bool candidate = false;
	int other_count = 0;
	for (int i = 0; i < cp->length(); i++) {
	    int clit = (*cp)[i];
	    if (clit == lit) 
		candidate = true;
	    else  if (unit_literals.find(clit) != unit_literals.end()) {
		// Satisfied clause.  Not yet removed by BCP
		err(false, "Checking literal %d.  Active clause #%d satisifed by unit literal %d\n", lit, cid, clit);
		candidate = false;
		break;
	    } else if (unit_literals.find(-clit) == unit_literals.end())
		other_count++;
	}
	if (candidate && other_count == 0) {
	    found = true;
	    report(1, "Checking literal %d.  Unit in active clause #%d\n", lit, cid);
	}
    }
    if (found)
	return;

    for (int cid = 1; cid < clause_count(); cid++) {
	if (curr_active_clauses->find(cid) != curr_active_clauses->end())
	    continue;
	Clause *cp = get_input_clause(cid);
	bool candidate = false;
	bool satisfied = false;
	int other_count = 0;
	for (int i = 0; i < cp->length(); i++) {
	    int clit = (*cp)[i];
	    if (clit == lit) 
		candidate = true;
	    else  if (unit_literals.find(clit) != unit_literals.end()) {
		satisfied = true;
		break;
	    } else if (unit_literals.find(-clit) == unit_literals.end())
		other_count++;
	}
	if (!satisfied && candidate && other_count == 0) {
	    found = true;
	    report(1, "Checking literal %d.  Unit in inactive clause #%d\n", lit, cid);
	}
    }
    report(1, "Checking literal %d.  Not unit in any active clause or in any inactive input clause\n", lit);
}

Lemma_instance *Cnf_reasoner::extract_lemma(int xvar, int splitting_literal) {
    Lemma_instance *lemma = new Lemma_instance;
#if DEBUG
    pwriter->comment("Identifying arguments for lemma at node N%d", xvar);
#endif
    for (int cid : *curr_active_clauses) {
	add_lemma_argument(lemma, cid);
    }
    lemma->sign(xvar, splitting_literal);
    pwriter->comment("Extracted lemma for node N%d.  Signature %u", xvar, lemma->signature);
    if (lemma->duplicate_cid.size() > 0)
	pwriter->comment_container("  Duplicate clause IDs", lemma->duplicate_cid);
    return lemma;
}

// Set up context for lemma proof
void Cnf_reasoner::setup_proof(Lemma_instance *lemma) {
    new_context();
    clear_assigned_literals();

    report(3, "Proving lemma at N%d\n", lemma->xvar);
#if DEBUG
    int acount = 0;
#endif

    pwriter->comment("Proof of lemma for N%d, signature %u", lemma->xvar, lemma->signature);

    for (auto fid : lemma->inverse_cid) {
	int ncid = fid.first;
	int ocid = fid.second;
	if (ncid != ocid) {
	    deactivate_clause(ocid);
	    activate_clause(ncid);
	}

	Clause *nnp = get_clause(ncid);
	int alit = nnp->get_activating_literal();

	if (alit == 0) {
#if DEBUG
	    acount++;
	    report(3, "  Argument #%d: Clause #%d\n", acount, ncid);
	    pwriter->comment("  Argument #%d: Clause #%d", acount, ncid);
#endif
	} else {
	    push_assigned_literal(alit);
#if DEBUG
	    acount++;
	    report(3, "  Argument #%d: clause #%d.  Activated by literal %d\n", acount, ncid, alit);
	    pwriter->comment("  Argument #%d: clause #%d.  Activated by literal %d", acount, ncid, alit);
#endif
	}
    }
    for (int ocid : lemma->duplicate_cid) {
	deactivate_clause(ocid);
    }
    lemma->jid = 0;
#if DEBUG
    pwriter->comment("Set up to prove lemma for N%d, signature %u", lemma->xvar, lemma->signature);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
    pwriter->comment_container("Unit literals:", unit_literals);
    if (!check_active()) {
	err(false, "Inconsistent reasoner state\n");
    }
#endif
}

    // Restore context from lemma proof
void Cnf_reasoner::restore_from_proof(Lemma_instance *lemma) {
    for (auto fid : lemma->inverse_cid) {
	int ncid = fid.first;
	int ocid = fid.second;
	if (ncid != ocid) {
	    deactivate_clause(ncid);
	    activate_clause(ocid);
	} 
    }
    pop_context();
    for (int ocid : lemma->duplicate_cid) {
	activate_clause(ocid);
	incr_count(COUNT_LEMMA_ARGUMENT_MERGE);
    }
#if DEBUG
    pwriter->comment("Restoring context after proving lemma for N%d, signature %u", lemma->xvar, lemma->signature);
    pwriter->comment_container("Active clauses:", *curr_active_clauses);
    pwriter->comment_container("Unit literals:", unit_literals);
    if (!check_active()) {
	err(false, "Inconsistent reasoner state\n");
    }
#endif

}

int Cnf_reasoner::apply_lemma(Lemma_instance *lemma, Lemma_instance *instance) {
    // Make sure they're compatible
    // Should have identical sets of new clause IDs
    bool ok = true;
    if (lemma->splitting_literal != instance->splitting_literal) {
	err(false, "Attempting to apply lemma for node N%d.  Lemma and instance differ on splitting variables\n", lemma->xvar);
	ok = false;
    }
    for (auto lfid : lemma->inverse_cid) {
	if (!ok)
	    break;
	int ncid = lfid.first;
	if (instance->inverse_cid.find(ncid) == instance->inverse_cid.end()) {
	    err(false, "Attempting to apply lemma for node N%d.  Lemma argument clause #%d not found in instance\n", lemma->xvar, ncid);
	    ok = false;
	}
    }
    for (auto ifid : instance->inverse_cid) {
	if (!ok)
	    break;
	int ncid = ifid.first;
	if (lemma->inverse_cid.find(ncid) == lemma->inverse_cid.end()) {
	    err(false, "Attempting to apply lemma for node N%d.  Instance argument clause #%d not found in lemma\n", lemma->xvar, ncid);
	    ok = false;
	}
    }
    if (!ok)
	return 0;
    // Now justify lemma arguments
    std::vector<int> arg_jids;
    pwriter->comment("Application of lemma for N%d, signature %u", lemma->xvar, lemma->signature);
#if DEBUG
    pwriter->comment_container("Assigned literals:", assigned_literals);
    pwriter->comment_container("Unit literals:", unit_literals);
#endif
    int acount = 0;
    for (auto ifid : instance->inverse_cid) {
	int ocid = ifid.second;
	int ncid = ifid.first;
	if (ocid == ncid) {
	    pwriter->comment("  Arg %d.  Clause #%d used directly", ++acount, ocid);
#if DEBUG
	    // Double check
	    Clause *anp = get_clause(ncid);
	    int alit = anp->get_activating_literal();
	    if (alit != 0 && unit_literals.find(alit) == unit_literals.end()) {
		pwriter->diagnose("Couldn't apply lemma N%d, signature %u", lemma->xvar, lemma->signature);
		pwriter->diagnose("Clause #%d used directly in lemma, but activating literal %d not unit",
				  ncid, alit);
		return 0;
	    }
#endif	  
	    continue;
	}
	Clause *anp = get_clause(ncid);
	int alit = anp->get_activating_literal();
	if (unit_literals.find(alit) != unit_literals.end()) { 
	    pwriter->comment("  Arg %d.  Clause #%d replaced by #%d, which is already unit", ++acount, ocid, ncid);
	    auto fid = justifying_ids.find(alit);
	    if (fid != justifying_ids.end())
		arg_jids.push_back(fid->second);
	} else {
	    Clause *nnp = new Clause();
	    nnp->add(alit);
	    for (int lit : assigned_literals)
		nnp->add(-lit);
	    pwriter->comment("  Arg %d.  Clause #%d replaced by #%d", ++acount, ocid, ncid);
	    int ccid = start_assertion(nnp, false);
	    arg_jids.push_back(ccid);
	    // Add hints from synthetic clause definition
	    for (int offset = 1; offset <= anp->length(); offset++)
		add_hint(ncid+offset);
	    // Add hints based on context
	    Clause *cnp = get_clause(ocid);
	    for (int i = 0; i < cnp->length(); i++) {
		int clit = (*cnp)[i];
		auto fid = justifying_ids.find(-clit);
		if (fid != justifying_ids.end())
		    add_hint(fid->second);
	    }
	    add_hint(ocid);
	    finish_command(true);
	    incr_count(COUNT_LEMMA_APPLICATION_CLAUSE);
	    delete nnp;
	}
    }
    // Finally, assert the root
    Clause *lnp = new Clause();
    lnp->add(lemma->xvar);
    for (int lit : assigned_literals)
	lnp->add(-lit);
    pwriter->comment("Justification of lemma root %d in context", lemma->xvar);
    int jid = start_assertion(lnp, false);
    for (int ajid : arg_jids)
	add_hint(ajid);
    add_hint(lemma->jid);
    finish_command(true);
    incr_count(COUNT_LEMMA_APPLICATION_CLAUSE);
    delete lnp;
    return jid;
}

// Debugging support
bool Cnf_reasoner::check_active() {
    bool ok = true;
#if DEBUG
    for (int cid : *curr_active_clauses) {
	if (cid > clause_count()) {
	    Clause *nnp = get_clause(cid);
	    int alit = nnp->get_activating_literal();
	    if (alit != 0 && unit_literals.find(alit) == unit_literals.end()) {
		pwriter->diagnose("Lost track of activating literal %d for active clause #%d", alit, cid);
		ok = false;
		break;
	    }
	}
    }
#endif
    return ok;
}


int Cnf_reasoner::monolithic_validate_root(int root_literal) {
    const char *cnf_name = "cpog_validation_xxx.cnf";
    const char *lrat_name = "cpog_validation_xxx.lrat";
    char cmd[350];

    FILE *cnf_out = fopen(cnf_name, "w");
    if (!cnf_out) {
	err(true, "Couldn't open temporary file '%s'\n", cnf_name);
    }
    int starting_proof_size = proof_clauses.size();
    int full_clause_count = clause_count() + starting_proof_size;
    // Write Input clauses + initial BCP clauses + defining clauses as CNF
    fprintf(cnf_out, "p cnf %d %d\n", xvar_count, full_clause_count);
    for (int cid = 1; cid <= full_clause_count; cid++) {
	Clause *clp = get_clause(cid);
	clp->show_reduced(cnf_out, -root_literal);
    }
    fclose(cnf_out);
    
    double start = tod();
    const char *trimmer = "";
#if SOLVER == CADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnf_name, cnf_name, lrat_name);
#elif SOLVER == LCADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q --lrat=1 %s %s", cnf_name, lrat_name);
    trimmer="cadical";
#elif SOLVER == TCADICAL
    snprintf(cmd, 350, "cadical --no-binary --unsat -q --lrat=1 %s - | lrat-trim --no-binary -q - %s", cnf_name, lrat_name);
    trimmer="lrat-trim";
#else
    snprintf(cmd, 350, "kissat --no-binary --unsat -q %s - | drat-trim %s -L %s > /dev/null", cnf_name, cnf_name, lrat_name);
#endif
    int rc = system(cmd);
    incr_timer(TIME_SAT_TOTAL, tod()-start);
    if (rc != 0) {
	report(2, "Warning: Executing command '%s' yielded return code %d\n", cmd, rc);
	return 0;
    }
    FILE *lfile = fopen(lrat_name, "r");
    if (!lfile) {
	err(false, "Couldn't open generated LRAT file\n", lrat_name);
	return 0;
    }
    if (!monolithic_load_proof(lfile, root_literal)) {
	err(false, "Failed to read generated LRAT file\n", lrat_name);
	return 0;
    }
    fclose(lfile);
    Clause *lnp = proof_clauses.back();
    if (lnp->length() != 1) {
	err(false, "Execution of command '%s' did not generate unit clause\n", cmd);	
	return false;
    }
    int nclauses = proof_clauses.size() - starting_proof_size;
    report(3, "File %s.  Generating lrat with %s.  %d problem clauses.  %d proof clauses\n", cnf_name, trimmer, full_clause_count, nclauses);
    incr_histo(HISTO_PROBLEM, full_clause_count);
    incr_histo(HISTO_PROOF, nclauses);

    //    if (delete_files) {
    //	remove(cnf_name);
    //	remove(lrat_name);
    //    }
    return clause_count() + proof_clauses.size();
}
 
bool Cnf_reasoner::monolithic_load_proof(FILE *lfile, int root_literal) {
    pwriter->comment("Monolithic proof of root literal %d", root_literal);
    int nclause = clause_count() + proof_clauses.size();
    std::unordered_map<int,int> lrat2local;
    int next_id = nclause + 1;
    while (find_token(lfile)) {
	int sid = 0;
	if (fscanf(lfile, "%d", &sid) != 1) {
	    err(false, "Couldn't read step Id in LRAT file.  Should be at step #%d\n", next_id);
	    return false;
	}
	if (!find_token(lfile)) {
	    err(false, "EOF found while trying to parse proof step #%d\n", next_id);
	}
	int c = getc(lfile);
	if (c == EOF) {
	    err(false, "EOF found while trying to parse proof step #%d\n", sid);
	    return false;
	}
	if (c == 'd') {
	    c = skip_line(lfile);
	    if (c == EOF) {
		err(false, "EOF found while trying to parse proof step #%d\n", sid);
		return false;
	    }
	    ungetc(c, lfile);
	    continue;
	} else
	    ungetc(c, lfile);
	// Here's the good stuff
	bool eof;
	Clause *np = new Clause(lfile, true, &eof);
	if (np == NULL || eof) {
	    err(false, "Error encountered while trying to read literals from proof step #%d\n", sid);
	    return false;
	}
	// Add root literal
	np->add(root_literal);
	Clause *hp = new Clause(lfile, true, &eof);
	if (hp == NULL || eof) {
	    err(false, "Error encountered while trying to read hints from proof step #%d\n", sid);
	    return false;
	}
	lrat2local[sid] = next_id;
	// Fix up hints
	for (int i = 0; i < hp->length(); i++) {
	    int hint = (*hp)[i];
	    int nhint = (hint <= nclause) ? hint : lrat2local.find(hint)->second;
	    (*hp)[i] = nhint;
	}
	start_assertion(np, false);
	add_hints(hp);
	finish_command(true);

	incr_count(COUNT_MONOLITHIC_CLAUSE);
	next_id++;
    }
    return true;
}
