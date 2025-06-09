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


#include <cstdio>
#include <stdlib.h>
#include <string.h>
#include <map>
#include <unordered_map>
#include <ctype.h>
#include <limits.h>
#include "pog.hh"
#include "report.h"
#include "counters.h"

#define TRUE_ID INT_MAX

const char *pog_type_name[6] = { "NONE", "TRUE", "FALSE", "AND", "OR", "SKOLEM" };
const char pog_type_prefix[6] = { '?', 'T', 'F', 'P', 'S', 'T' };
const char pog_type_char[6] = { '\0', 't', 'f', 'a', 'o', 't' };

// Reporting validation progress
// Reporting parameters
#define REPORT_MIN_INTERVAL 1000
#define REPORT_MAX_COUNT 10
// Reporting deletion progress
#define REPORT_MIN_DELETION_INTERVAL 100

// Forward Report status
static int vreport_interval = INT_MAX;
static int vreport_last = 0;
static int vcount = 0;

Pog_node::Pog_node() {
    type = POG_TRUE;
    xvar = 0;
    degree = 0;
    children = NULL;
    indegree = 0;
    lemma = NULL;
    tree_size = 1;
}

Pog_node::Pog_node(pog_type_t ntype) {
    type = ntype;
    xvar = 0;
    degree = 0;
    children = NULL;
    indegree = 0;
    lemma = NULL;
    tree_size = 1;
    if (type == POG_AND || type == POG_TRUE)
	incr_count(COUNT_POG_AND);
    if (type == POG_OR)
	incr_count(COUNT_POG_OR);
    if (type == POG_SKOLEM)
	incr_count(COUNT_POG_SKOLEM);
}

Pog_node::Pog_node(pog_type_t ntype, size_t xv) {
    type = ntype;
    xvar = xv;
    degree = 0;
    children = NULL;
    indegree = 0;
    lemma = NULL;
    tree_size = 1;
    if (type == POG_AND)
	incr_count(COUNT_POG_AND);
    if (type == POG_OR)
	incr_count(COUNT_POG_OR);
    if (type == POG_SKOLEM)
	incr_count(COUNT_POG_SKOLEM);
}

Pog_node::~Pog_node() {
    if (degree > 0) delete children;
    if (type == POG_AND)
	incr_count_by(COUNT_POG_AND, -1);
    if (type == POG_OR)
	incr_count_by(COUNT_POG_OR, -1);
    if (type == POG_SKOLEM)
	incr_count_by(COUNT_POG_SKOLEM, -1);
    while (lemma) {
	Lemma_instance *nlemma = lemma->next;
	delete lemma;
	lemma = nlemma;
    }
}

void Pog_node::set_type(pog_type_t t) {
    type = t;
}


pog_type_t Pog_node::get_type() {
    return type;
}

void Pog_node::set_xvar(int var) {
    xvar = var;
}

int Pog_node::get_xvar() {
    return xvar;
}

void Pog_node::set_defining_cid(int cid) {
    defining_cid = cid;
}

int Pog_node::get_defining_cid() {
    return defining_cid;
}

// Hack to allow multiple names to be used in single printf
#define BCOUNT 5
static char nbuf[BCOUNT][100];

const char *Pog_node::name() {
    static int lastbuf = 0;
    int b = lastbuf;
    lastbuf = (lastbuf+1) % BCOUNT;
    snprintf(nbuf[b], 100, "%c%d_%s", pog_type_prefix[type], xvar, pog_type_name[type]);
    return nbuf[b];
}


void Pog_node::add_children(std::vector<int> *cvec) {
    degree = cvec->size();
    if (degree > 0) {
	children = new int[degree];
	memcpy(children, cvec->data(), degree * sizeof(int));
    }
}

int Pog_node::get_degree() {
    return degree;
}

int *Pog_node::get_children() {
    return children;
}

long Pog_node::get_tree_size() {
    return tree_size;
}

void Pog_node::set_tree_size(long size) {
    tree_size = size;
}

int & Pog_node::operator[](int idx) {
    return children[idx];
}

void Pog_node::show(FILE *outfile) {
    bool first = true;
    fprintf(outfile, "%s(", name());
    for (int i = 0; i < degree; i++) {
	fprintf(outfile, first ? "%d" : ",%d", children[i]);
	first = false;
    }
    fprintf(outfile, ")");
}

void Pog_node::increment_indegree() {
    indegree++;
}

bool Pog_node::want_lemma() {
    return type == POG_OR && indegree >= 2;
}

void Pog_node::add_lemma(Lemma_instance *lem) {
    if (lemma != NULL)
	incr_count(COUNT_LEMMA_DUPLICATES);
    lem->next = lemma;
    lemma = lem;
}

Lemma_instance *Pog_node::get_lemma() {
    return lemma;
}


Pog::Pog() {
    root_literal = 0;
    no_mutex = false;
    cnf = NULL;
    max_input_var = 0;
    start_extension_var = 1;
    tree_ratio = 1.0;
    data_variables = NULL;
}

Pog::Pog(Cnf_reasoner *cset, bool nmutex) {
    root_literal = 0;
    cnf = cset;
    no_mutex = nmutex;
    max_input_var = cset->max_variable();
    data_variables = cset->data_variables;
    start_extension_var = max_input_var+1;
    tree_ratio = 1.0;
}

void Pog::clear() {
    root_literal = 0;
    cnf = NULL;
    max_input_var = 0;
    data_variables = NULL;
    for (Pog_node *np : nodes) {
	delete np;
    }
    nodes.clear();
}


int Pog::add_node(Pog_node *np) {
    nodes.push_back(np);
    int xvar = cnf->new_xvar();
    np->set_xvar(xvar);
    return xvar;
}

void Pog::set_root(int lit) {
    root_literal = lit;
}

int Pog::get_root() {
    return root_literal;
}


bool Pog::is_node(int lit) {
    int var = IABS(lit);
    int offset = var - start_extension_var;
    return offset >= 0 && offset <= (int) nodes.size();
}

Pog_node * Pog::get_node(int id) {
    int idx = id-start_extension_var;
    if (idx < 0 || idx >= nodes.size())
	printf("Can't get node #%d.  Index %d.  Size %d\n",
	       id, idx, (int) nodes.size());
    return nodes[id-start_extension_var];
}

bool Pog::is_node_type(int lit, pog_type_t type) {
    if (!is_node(lit))
	return false;
    int id = IABS(lit);
    Pog_node *np = get_node(id);
    return np->get_type() == type;
}


Pog_node * Pog::operator[](int id) {
    return nodes[id-start_extension_var];
}

int Pog::node_count() {
    return (int) nodes.size();
}

void Pog::show(FILE *outfile) {
    for (Pog_node *np : nodes) {
	np->show(outfile);
	fprintf(outfile, "\n");
    }
    fprintf(outfile, "ROOT %d\n", root_literal);
}

void Pog::topo_order(int rlit, std::vector<int> &rtopo, int *markers) {
    if (is_node(rlit)) {
	int rid = IABS(rlit);
	int idx = rid-start_extension_var;
	if (markers[idx])
	    return;
	markers[idx] = 1;
	Pog_node *np = get_node(rid);
	for (int i = 0; i < np->get_degree(); i++)
	    topo_order((*np)[i], rtopo, markers);
	rtopo.push_back(rid);
    }
}


static void check_literals(std::vector<int> &literals, int id, const char *description, std::unordered_set<int> *data_variables) {
    // Disable
    return;
    /* First, make sure that they're OK */

    std::set<int> lset;
    std::set<int> duplicates;
    std::set<int> opposites;
    std::set<int> data;
    for (int lit : literals) {
	if (lset.find(lit) != lset.end())
	    duplicates.insert(lit);
	if (lset.find(-lit) != lset.end())
	    opposites.insert(IABS(lit));
	lset.insert(lit);
	int var = IABS(lit);
	if (data_variables->find(var) != data_variables->end())
	    data.insert(lit);
    }
    if (duplicates.size() > 0) {
	printf("DUPLICATES.  Node %d.  %s.", id, description);
	for (int lit : duplicates)
	    printf(" %d", lit);
	printf("\n");
    }
    if (opposites.size() > 0) {
	printf("OPPOSITES.  Node %d.  %s.", id, description);
	for (int lit : opposites)
	    printf(" %d", lit);
	printf("\n");
    }
    printf("ARGUMENTS.    Node %d.  %s.", id, description);
    for (int lit : literals)
	printf(" %d", lit);
    printf("\n");
    if (data.size() > 0) {
	printf("DATA.    %s.", description);
	for (int lit : data)
	    printf(" %d", lit);
	printf("\n");

    }
}

// For Skolem node, want all literals unique and not conflicting
// Eliminate duplicates
// Return ID of any conflicting variable
static int check_skolem(std::vector<int> &literals) {
    std::unordered_set<int> lset;
    if (literals.size() <= 1)
	return 0;
    int next_pos = 0;
    for (int i = 0; i < literals.size(); i++) {
	int lit = literals[i];
	if (lset.find(-lit) != lset.end())
	    return IABS(lit);
	if (lset.find(lit) == lset.end()) {
	    lset.insert(lit);
	    literals[next_pos++] = lit;
	}
    }
    literals.resize(next_pos);
    return 0;
}

bool Pog::compress(bool optimize) {
    long clause_count = 0;
    long virtual_clause_count = 0;
    if (root_literal == 0 || IABS(root_literal) == TRUE_ID) {
	for (Pog_node *np : nodes)
	    delete(np);
	nodes.resize(0);
	if (root_literal == TRUE_ID) {
	    // Constant value
	    Pog_node *np = new Pog_node(POG_AND, start_extension_var);
	    clause_count += 1;
	    nodes.push_back(np);
	    root_literal = start_extension_var;
	} else
	    root_literal = 0;
	const char *prefix = optimize ? "Optimized" : "Compressed";
	report(1, "%s POG has %ld nodes, %ld real + %ld virtual defining clauses, root literal %d\n",
	       prefix, (long) nodes.size(), clause_count, virtual_clause_count, root_literal);
	return true;
    }
    // Handle case where root represents input literal
    if (!is_node(root_literal)) {
	for (Pog_node *np : nodes)
	    delete np;
	nodes.resize(0);
	if (!optimize) {
	    // Create product node having root literal as child
	    Pog_node *np = new Pog_node(POG_AND, start_extension_var);
	    std::vector<int> children;
	    children.push_back(root_literal);
	    np->add_children(&children);
	    nodes.push_back(np);
	    clause_count += np->get_degree() + 1;
	    root_literal = start_extension_var;
	    const char *prefix = optimize ? "Optimized" : "Compressed";
	    report(1, "%s POG has %ld nodes, %ld real + %ld virtual defining clauses, root literal %d\n",
		   prefix, (long) nodes.size(), clause_count, virtual_clause_count, root_literal);
	}
	return true;
    }
    std::vector<Pog_node *> new_nodes;

    // Restart numbering of extension variables
    cnf->reset_xvar();
    // Mapping from old id to new literal
    std::vector<int> remap;
    remap.resize(nodes.size(), 0);
    // Order old nodes in reverse topological order
    std::vector<int> rtopo;

    // Get topological ordering of nodes accessible from root
    topo_order(root_literal, rtopo, remap.data());

    report(4, "Compressing POG with %d nodes (%d accessible from root) and root literal %d\n",
	   (int) nodes.size(), (int) rtopo.size(), root_literal);

    // Process nodes in reverse topological order
    // Skip inaccessible nodes and simplify operations
    for (int oid : rtopo) {
	if (!remap[oid-start_extension_var]) {
	    // Not reachable from root
	    report(3, "Old node #%d not reachable\n", oid-start_extension_var);
	    continue;
	}
	Pog_node *np = get_node(oid);
	pog_type_t ntype = np->get_type();
	report(3, "Looking at old node %s at %d\n", np->name(), oid-start_extension_var);
	if (!optimize) {
	    Pog_node *nnp = new Pog_node(ntype, new_nodes.size() + start_extension_var);
	    std::vector<int> nchildren;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		int nchild_lit = child_lit;
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    nchild_lit = MATCH_PHASE(remap[child_id-start_extension_var], child_lit);
		}
		nchildren.push_back(nchild_lit);
	    }
	    nnp->add_children(&nchildren);
	    new_nodes.push_back(nnp);
	    switch (nnp->get_type()) {
	    case POG_AND:
		incr_histo(HISTO_PRODUCT_DEGREE, nnp->get_degree());
		break;
	    case POG_SKOLEM:
		incr_histo(HISTO_SKOLEM_DEGREE, nnp->get_degree());
		break;
	    default:
		break;
	    }
	    remap[oid-start_extension_var] = nnp->get_xvar();
	    report(3, "Uncompressed POG node %s --> Compressed POG node %s\n",
		   np->name(), nnp->name());
	    continue;
	}
	// Optimization code
	if (ntype == POG_TRUE) 
	    remap[oid-start_extension_var] = TRUE_ID;
	else if (ntype == POG_FALSE)
	    remap[oid-start_extension_var] = -TRUE_ID;
	else if (ntype == POG_OR) {
	    if (np->get_degree() == 1) {
		int child_lit = (*np)[0];
		int nchild_lit = child_lit;
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    nchild_lit = MATCH_PHASE(remap[child_id-start_extension_var], child_lit);
		}
		remap[oid-start_extension_var] = nchild_lit;
		report(3, "Unoptimized POG node %s --> Literal %d\n",
		       np->name(), nchild_lit);
		continue;
	    }
	    std::vector<int> nchildren;
	    bool tautology = false;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		int nchild_lit = child_lit;
		if (child_lit == TRUE_ID) {
		    report(3, "Found tautology as argument to sum %s\n", np->name());
		    tautology = true;
		    break;
		}
		if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    nchild_lit = MATCH_PHASE(remap[child_id-start_extension_var], child_lit);
		    if (nchild_lit == TRUE_ID) {
			report(3, "Found tautology as argument to sum %s\n", np->name());
			tautology = true;
			break;
		    }
		}
		nchildren.push_back(nchild_lit);
		for (int j = 0; j < i; j++) 
		    if (nchildren[j] == -nchildren[i]) {
			tautology = true;
			report(3, "Found complements: nchildren[%d] = %d, nchildren[%d] = %d\n",
			       j, nchildren[j], i, nchildren[i]);
		    }
	    }
	    if (tautology) {
		// Tautology
		remap[oid-start_extension_var] = TRUE_ID;
		report(3, "Unoptimized POG node %s --> Tautology (%d)\n",
		       np->name(), TRUE_ID);
		continue;
	    }
	    if (nchildren[0] == -TRUE_ID || nchildren[1] == -TRUE_ID) {
		// If one of the children is false, then replace this node with other child
		int other_lit = nchildren[0] == -TRUE_ID ? nchildren[1] : nchildren[0];
		remap[oid-start_extension_var] = other_lit;
		report(3, "Unoptimized POG node %s --> Literal %d\n",
		       np->name(), other_lit);
		continue;
	    } else {
		Pog_node *nnp = new Pog_node(POG_OR, new_nodes.size() + start_extension_var);
		nnp->add_children(&nchildren);
		new_nodes.push_back(nnp);
		remap[oid-start_extension_var] = nnp->get_xvar();
		report(3, "Unoptimized POG node %s --> Optimized POG node %s\n",
		       np->name(), nnp->name());
	    }
	} else {
	    // AND
	    std::vector<int> nchildren;
	    // When encoding Skolemization, collect literals of non-data variables
	    std::vector<int> schildren;
	    bool zeroed = false;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		if (child_lit == TRUE_ID)
		    // Skip child
		    continue;
		else if (is_node(child_lit)) {
		    int child_id = IABS(child_lit);
		    int nchild_var = remap[child_id-start_extension_var];
		    int nchild_lit = MATCH_PHASE(nchild_var, child_lit);
		    int offset = nchild_var-start_extension_var;
		    Pog_node *cnp = NULL;
		    if (offset >= 0 && offset < (int) new_nodes.size()) {
			cnp = new_nodes[offset];
		    }
		    if (nchild_lit == TRUE_ID)
			// Skip child
			continue;
		    else if (nchild_lit == -TRUE_ID) {
			// Zero node
			remap[oid-start_extension_var] = -TRUE_ID;
			zeroed = true;
			break;
		    } else if (cnp && cnp->get_type() == POG_SKOLEM) {
			// Merge Skolem grandchildren with ones here
			for (int j = 0; j < cnp->get_degree(); j++)
			    schildren.push_back((*cnp)[j]);
		    } else
			nchildren.push_back(nchild_lit);
		} else if (child_lit == TRUE_ID) {
		    // Skip child
		    continue;
		} else {
		    // Input literal
		    if (is_projection_literal(child_lit))
			schildren.push_back(child_lit);
		    else
			nchildren.push_back(child_lit);
 		}
	    }
	    if (zeroed) {
		report(3, "Unoptimized POG node %s --> False\n",
		       np->name());
		continue;
	    }

	    Pog_node *nnp = NULL;
	    int var = check_skolem(schildren);
	    if (var != 0)
		err(true, "Problem creating Skolem node %d.  Argument %d occurs in both true and complemented form\n", 
		    new_nodes.size() + start_extension_var, var);
	    if (nchildren.size() == 0) {
		if (schildren.size() == 0) {
		    remap[oid-start_extension_var] = TRUE_ID;
		} else {
		    nnp = new Pog_node(POG_SKOLEM, new_nodes.size() + start_extension_var);
		    nnp->add_children(&schildren);
		}
	    } else {
		if (schildren.size() == 0) {
		    if (nchildren.size() == 1) {
			remap[oid-start_extension_var] = nchildren[0];
			report(3, "Unoptimized POG node %s --> Single child %d\n", np->name(), nchildren[0]);
		    } else {
			nnp = new Pog_node(POG_AND, new_nodes.size() + start_extension_var);
			nnp->add_children(&nchildren);
		    }
		} else {
		    nnp = new Pog_node(POG_SKOLEM, new_nodes.size() + start_extension_var);
		    nnp->add_children(&schildren);
		    new_nodes.push_back(nnp);
		    report(3, "Unoptimized POG node %s.  Generate Skolem node %s\n",
			   np->name(), nnp->name());
		    // Add Skolem node as child of product node
		    nchildren.push_back(nnp->get_xvar());
		    nnp = new Pog_node(POG_AND, new_nodes.size() + start_extension_var);
		    nnp->add_children(&nchildren);
		}
	    }
	    if (nnp != NULL) {
		new_nodes.push_back(nnp);
		remap[oid-start_extension_var] = nnp->get_xvar();
		report(3, "Unoptimized POG node %s --> Optimized POG node %s\n",
		       np->name(), nnp->name());
	    }
	}
    }
    // Clear out old nodes
    for (Pog_node *np : nodes)
	delete np;
    nodes.resize(0);

    // Figure out root
    int rvar = IABS(root_literal);
    root_literal = MATCH_PHASE(remap[rvar-start_extension_var], root_literal);
    int nrvar = IABS(root_literal);
    if (root_literal == 0) {
	// Already set as unsatisfiable
    } else if (nrvar == TRUE_ID) {
	if (root_literal < 0) {
	    // Unsatisfiable formula.  Root=0
	    root_literal = 0;
	} else {
	    Pog_node *nnp = new Pog_node(POG_TRUE, new_nodes.size());
	    add_node(nnp);
	    root_literal = MATCH_PHASE(start_extension_var, root_literal);
	}
    } else if (IABS(nrvar) >= start_extension_var) {
	// Normal case.  Copy new nodes.  Set their indegrees
	for (Pog_node *np : new_nodes) {
	    add_node(np);
	    if (np->get_type() == POG_SKOLEM) {
		clause_count++;
		virtual_clause_count += np->get_degree();
	    } else
		clause_count += np->get_degree() + 1;
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    Pog_node *cnp = get_node(IABS(clit));
		    cnp->increment_indegree();
		}
	    }
	}
    }
    const char *prefix = optimize ? "Optimized" : "Compressed";
    report(1, "%s POG has %ld nodes, %ld real + %ld virtual defining clauses, root literal %d\n",
	   prefix, (long) nodes.size(), clause_count, virtual_clause_count, root_literal);

    // Set parameters for progress reporting
    vreport_interval = nodes.size() / REPORT_MAX_COUNT;
    if (vreport_interval < REPORT_MIN_INTERVAL)
	vreport_interval = REPORT_MIN_INTERVAL;
    return true;
}

void Pog::concretize() {
#if VLEVEL >= 5
    if (verblevel >= 5) {
	report(5, "Before concretizing:\n");
	show(stdout);
    }
#endif

    if (verblevel >= 2) {
	// Document input clauses
	cnf->pwriter->comment("Input clauses");
	for (int cid = 1; cid <= cnf->clause_count(); cid++)
	    cnf->document_input(cid);
    }

    // Insert declaration of root literal
    cnf->pwriter->declare_root(root_literal);
    // Insert declaration of mode variable

    long last_tree_size = 0;
    long dag_size = 0;

    for (Pog_node *np : nodes) {
	int degree = np->get_degree();
	ilist args = ilist_copy_list(&(*np)[0], degree);
	if (np->get_type() != POG_SKOLEM)
	    dag_size += 1 + degree;
	int xvar = np->get_xvar();
	int defining_cid = 0;
	bool need_zero = false;
	long tsize = degree+1;
	switch (np->get_type()) {
	case POG_TRUE:
	case POG_AND:
	    defining_cid = cnf->start_and(xvar, args);
	    need_zero = false;
	    for (int i = 0; i < np->get_degree(); i++) {
		int child_lit = (*np)[i];
		if (is_node(child_lit)) {
		    Pog_node *cnp = get_node(child_lit);
		    tsize += cnp->get_tree_size();
		}
	    }
	    break;
	case POG_OR:
	    {
		std::vector<int> hints;
		if (!no_mutex)
		    justify_mutex(np, hints);
		need_zero = true;;
		defining_cid = cnf->start_or(xvar, args);
		if (np->get_degree() != 2)
		    err(true, "POG Node %s.  OR node cannot have %d children", np->name(), np->get_degree());
		for (int hid : hints)
		    cnf->add_hint(hid);
		for (int i = 0; i < np->get_degree(); i++) {
		    int child_lit = (*np)[i];
		    if (is_node(child_lit)) {
			Pog_node *cnp = get_node(child_lit);
			tsize += cnp->get_tree_size();
		    }
		}
	    }
	    break;
	case POG_SKOLEM:
	    defining_cid = cnf->start_skolem(xvar, args);
	    tsize = 0;
	    break;
	default:
	    err(true, "POG Node %s.  Can't handle node type with value %d\n", np->name(), (int) np->get_type());
	}
	cnf->finish_command(need_zero);
	np->set_defining_cid(defining_cid);
	np->set_tree_size(tsize);
	last_tree_size = tsize;
	if (np->get_type() == POG_OR)
	    cnf->document_or(defining_cid, xvar, args);
	else if (np->get_type() == POG_SKOLEM)
	    cnf->document_skolem(defining_cid, xvar, args);
	else
	    cnf->document_and(defining_cid, xvar, args);
	ilist_free(args);
	
    }
    if (dag_size > 0) {
	tree_ratio = (double) last_tree_size / dag_size;
	report(1, "POG has DAG size %d and tree size %ld ratio = %.2f\n", dag_size, last_tree_size, tree_ratio);
    }
}


// Try to read single alphabetic character from line
// If not found, then push back unread character and return 0
// If hit EOF, then return this
static int get_token(FILE *infile) {
    int c;
    while (true) {
	c = fgetc(infile);
	if (isalpha(c) || c == EOF)
	    return c;
	else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    return 0;
	}
    }
}

// Read sequence of numbers from line of input
// Consume end of line character
// Return false if non-numeric value encountered
static bool read_numbers(FILE *infile, std::vector<int> &vec, int *rc) {
    vec.resize(0);
    while (true) {
	int c = fgetc(infile);
	int val;
	if (c == '\n' || c == EOF) {
	    *rc = c;
	    return true;
	} else if (isspace(c))
	    continue;
	else {
	    ungetc(c, infile);
	    if (fscanf(infile, "%d", &val) == 1) {
		vec.push_back(val);
	    } else
		return false;
	}
    }
    // Won't hit this
    return false;
}


bool Pog::read_d4ddnnf(FILE *infile) {
    // Mapping from NNF ID to POG Node ID
    std::map<int,int> nnf_idmap;
    // Set of POG nodes that have at least one parent
    std::unordered_set<int> node_with_parent;
    // Vector of arguments for each POG node
    std::vector<std::vector<int> *> arguments;
    // Capture arguments for each line
    std::vector<int> largs;
    int line_number = 0;
    // Statistics
    int nnf_node_count = 0;
    int nnf_explicit_node_count = 0;
    int nnf_edge_count = 0;
    while (true) {
	pog_type_t ntype = POG_NONE;
	line_number++;
	int c = get_token(infile);
	int rc = 0;
	if (c == EOF)
	    break;
	if (c != 0) {
	    for (int t = POG_TRUE; t <= POG_OR; t++)
		if (c == pog_type_char[t])
		    ntype = (pog_type_t) t;
	    if (ntype == POG_NONE)
		err(true, "Line #%d.  Unknown D4 NNF command '%c'\n", line_number, c);
	    nnf_node_count++;
	    nnf_explicit_node_count++;
	    Pog_node *np = new Pog_node(ntype);
	    int pid = add_node(np);
	    arguments.push_back(new std::vector<int>);
	    bool ok = read_numbers(infile, largs, &rc);
	    if (!ok)
		err(true, "Line #%d.  Couldn't parse numbers\n", line_number);
	    else if (largs.size() == 0 && rc == EOF)
		break;
	    else if (largs.size() != 2)
		err(true, "Line #%d.  Expected 2 numbers.  Found %d\n", line_number, largs.size());
	    else if (largs.back() != 0)
		err(true, "Line #%d.  Line not zero-terminated\n", line_number);
	    else
		nnf_idmap[largs[0]] = pid;
	    report(3, "Line #%d.  Created POG node %s number %d from NNF node %d\n",
		   line_number, pog_type_name[ntype], pid, largs[0]); 
	} else {
	    nnf_edge_count++;
	    bool ok = read_numbers(infile, largs, &rc);
	    if (!ok)
		err(true, "Line #%d.  Couldn't parse numbers\n", line_number);
	    else if (largs.size() == 0 && rc == EOF)
		break;
	    else if (largs.size() < 3)
		err(true, "Line #%d.  Expected at least 3 numbers.  Found %d\n", line_number, largs.size());
	    else if (largs.back() != 0)
		err(true, "Line #%d.  Line not zero-terminated\n", line_number);
	    // Find parent
	    auto fid = nnf_idmap.find(largs[0]);
	    if (fid == nnf_idmap.end())
		err(true, "Line #%d.  Invalid NNF node Id %d\n", line_number, largs[0]);
	    int ppid = fid->second;
	    // Find second node
	    fid = nnf_idmap.find(largs[1]);
	    if (fid == nnf_idmap.end())
		err(true, "Line #%d.  Invalid NNF node Id %d\n", line_number, largs[1]);
	    int spid = fid->second;
	    int cpid = spid;
	    if (largs.size() > 3) {
		// Must construct AND node to hold literals
		nnf_node_count++;
		Pog_node *anp = new Pog_node(POG_AND);
		cpid = add_node(anp);
		std::vector<int> *aargs = new std::vector<int>;
		arguments.push_back(aargs);
		for (int i = 2; i < largs.size()-1; i++)
		    aargs->push_back(largs[i]);
		aargs->push_back(spid);
		report(3, "Line #%d. Created POG AND Node %d to hold literals between NNF nodes %d and %d\n",
		       line_number, cpid, largs[0], largs[1]); 
	    }
	    report(3, "Fetching argument %d-%d=%d\n", ppid, start_extension_var, ppid-start_extension_var);
	    std::vector<int> *pargs = arguments[ppid-start_extension_var];
	    pargs->push_back(cpid);
	    node_with_parent.insert(cpid);
	    report(4, "Line #%d.  Adding edge between POG nodes %d and %d\n", line_number, ppid, cpid);
	}
    }
    // Add arguments
    for (int pid = start_extension_var; pid < start_extension_var + nodes.size(); pid++) {
	Pog_node *np = get_node(pid);
	std::vector<int> *args = arguments[pid-start_extension_var];
	np->add_children(args);
	delete args;
    }
    for (auto kv : nnf_idmap) {
	int nid = kv.first;
	int pid = kv.second;
	Pog_node *np = get_node(pid);
	// Check OR nodes
	if (np->get_type() == POG_OR) {
	    int degree = np->get_degree();
	    if (degree == 0 || degree > 2) 
		err(true, "NNF OR node %d.  Invalid degree %d\n", nid, degree);
	    else if (degree == 1  && node_with_parent.find(pid) == node_with_parent.end()) {
		if (root_literal == 0) {
		    root_literal = pid;
		    report(3, "Setting root literal to %d\n", root_literal);
		} else if (IABS(root_literal) != TRUE_ID)
		    report(3, "Ambiguous root literal.  Thought it was %d.  But it might be %d\n", root_literal, pid);
	    }
	} else if (root_literal == 0 && np->get_type() == POG_FALSE)
	    root_literal = -TRUE_ID;
	else if (root_literal == 0 && np->get_type() == POG_TRUE)
	    root_literal = TRUE_ID;
    }
    if (root_literal == 0)
	err(true, "Failed to find root node in NNF file\n");
    report(1, "Read D4 NNF file with %d nodes (%d explicit) and %d edges\n",
	   nnf_node_count, nnf_explicit_node_count, nnf_edge_count);
    if (!compress(true))
	return false;
    if (!compress(false))
	return false;
    concretize();
    return true;
}

// Descend Pog until find input literal
int Pog::first_literal(int rlit) {
    Pog_node *np = NULL;
    while (is_node(rlit)) {
	np = get_node(IABS(rlit));
	rlit = (*np)[0];
    }
    int final_var = IABS(rlit);
    if (final_var >= start_extension_var) {
	if (np == NULL)
	    err(true, "First literal %d invalid.  Given an input argument\n", rlit);
	else
	    err(true, "First literal %d invalid.  Got it from node %s\n", rlit, np->name());
    }
    return rlit;
}

// Descend Pogs until opposite input literals
int Pog::find_splitting_literal(int rlit1, int rlit2) {
    // Construct arrays of literals from the two arguments
    int lcount1 = 1;
    int *lits1 = &rlit1;
    int lcount2 = 1;
    int *lits2 = &rlit2;
    if (is_node_type(rlit1, POG_AND)) {
	Pog_node *np = get_node(IABS(rlit1));
	lcount1 = np->get_degree();
	lits1 = np->get_children();
    }
    if (is_node_type(rlit2, POG_AND)) {
	Pog_node *np = get_node(IABS(rlit2));
	lcount2 = np->get_degree();
	lits2 = np->get_children();
    }
    for (int i1 = 0; i1 < lcount1; i1++) 
	for (int i2 = 0; i2 < lcount2; i2++)
	    if (lits1[i1] == -lits2[i2])
		return lits1[i1];
    // Didn't find one
    return 0;
}


// Prove lemma if needed, and apply to this instance
int Pog::apply_lemma(Pog_node *rp, int splitting_literal) {
    report(3, "Attempting to prove/apply lemma for node %s.\n", rp->name());
    Lemma_instance *instance = cnf->extract_lemma(rp->get_xvar(), splitting_literal);
    // Search for compatible lemma
    Lemma_instance *lemma = rp->get_lemma();
    while (lemma != NULL) {
	if (lemma->signature == instance->signature)
	    break;
	lemma = lemma->next;
    }
    if (lemma == NULL) {
	// The instance becomes the new lemma.  Must prove it
	lemma = instance;
	rp->add_lemma(lemma);
	report(3, "Setting up lemma for node %s.  Signature = %u\n",
	       rp->name(), lemma->signature);
	cnf->setup_proof(lemma);
	if (rp->get_type() != POG_SKOLEM && tree_ratio <= cnf->tree_ratio_threshold && (cnf->monolithic_threshold < 0 || rp->get_tree_size() <= cnf->monolithic_threshold))
	    lemma->jid = justify_monolithic(lemma->xvar, lemma->splitting_literal);
	else
	    lemma->jid = justify(lemma->xvar, lemma->splitting_literal, false);
	if (lemma->jid == 0) {
	    cnf->pwriter->diagnose("Proof of lemma for node %s, signature %u failed", rp->name(), lemma->signature);
	    return 0;
	}
	cnf->pwriter->comment("Created lemma for node %s.  Signature = %u.  Justifying clause = %d",
			      rp->name(), lemma->signature, lemma->jid);
	report(3, "Completed lemma for node %s.  Signature = %u.  Justifying clause = %d\n",
	       rp->name(), lemma->signature, lemma->jid);
	cnf->restore_from_proof(lemma);
	incr_count(COUNT_LEMMA_DEFINITION);
    }
    if (lemma->jid == 0)
	return 0;
    incr_count(COUNT_LEMMA_APPLICATION);
    report(3, "Applying lemma for node %s.  Signature = %u\n", rp->name(), lemma->signature);
    cnf->pwriter->comment("Applying lemma at node %s.  Signature = %u", rp->name(), lemma->signature);
    int jid = cnf->apply_lemma(lemma, instance);
    if (jid == 0)
	cnf->pwriter->diagnose("Application of lemma at node %s, signature %u, failed",
			       rp->name(), lemma->signature);
    else {
    }
    return jid;
}

// Special value used during OR justification
#define TRIVIAL_ARGUMENT -1


// Justify each position in POG within current context
// Return ID of justifying clause
int Pog::justify(int rlit, int splitting_literal, bool use_lemma) {
    int jcid = 0;
    counter_t jtype = COUNT_LITERAL_JUSTIFICATION_CLAUSE;
    if (is_node(rlit)) {
	int rvar = IABS(rlit);
	Pog_node *rnp = get_node(rvar);
	if (rnp->get_type() != POG_SKOLEM && tree_ratio <= cnf->tree_ratio_threshold && (cnf->monolithic_threshold < 0 || rnp->get_tree_size() <= cnf->monolithic_threshold))
	    return justify_monolithic(rlit, splitting_literal);
	if (use_lemma && cnf->use_lemmas && rnp->want_lemma()) {
	    int jid = apply_lemma(rnp, splitting_literal);
	    if (jid == 0)
		cnf->pwriter->diagnose("Failed lemma.  Giving up on validation of node %s", rnp->name());
	    return jid;
	}
	int xvar = rnp->get_xvar();
	Clause *jclause = new Clause();
	jclause->add(xvar);
	for (int alit : *cnf->get_assigned_literals())
	    jclause->add(-alit);
	std::vector<int> hints;
	cnf->new_context();
	bool retry = false;
	const char *reason = NULL;
	switch (rnp->get_type()) {
	case POG_OR:
	    {
		incr_count(COUNT_VISIT_OR);
		int clit[2] = { (*rnp)[0], (*rnp)[1] };
		int jid;
		int lhints[2][2];
		int hcount[2] = {0,0};
		int jcount = 0;
		int splitting_literal = find_splitting_literal(clit[0], clit[1]);
		for (int i = 0; i < 2; i++) {
		    lhints[i][hcount[i]++] = rnp->get_defining_cid()+i+1;
		    jid = justify(clit[i], splitting_literal, true);
		    if (jid == 0) {
			cnf->pwriter->diagnose("Justification of node %s failed.  Couldn't validate %s child %d.  Splitting literal = %d",
					       rnp->name(), i == 0 ? "first" : "second", clit[i], splitting_literal);
			reason = "Failed to justify child of sum node";
			retry = true;
			cnf->pop_context();
			goto try_monolithic;
		    } else if (jid != TRIVIAL_ARGUMENT) {
			jcount++;
			lhints[i][hcount[i]++] = jid;
		    }
		    // Negate for second time around
		    splitting_literal = -splitting_literal;
		}
		if (jcount > 1) {
		    // Must prove in two steps
		    Clause *jclause0 = new Clause();
		    jclause0->add(-splitting_literal);
		    jclause0->add(xvar);
		    for (int alit : *cnf->get_assigned_literals())
			jclause0->add(-alit);
		    cnf->pwriter->comment("Justify node %s", rnp->name());
		    int cid0 = cnf->start_assertion(jclause0, false);
		    for (int h = 0; h < hcount[0]; h++)
			cnf->add_hint(lhints[0][h]);
		    cnf->finish_command(true);
		    incr_count(COUNT_OR_JUSTIFICATION_CLAUSE);
		    incr_count_by(COUNT_ADDITION_HINT, hcount[0]);
		    hints.push_back(cid0);
		    for (int h = 0; h < hcount[1]; h++)
			hints.push_back(lhints[1][h]);
		    incr_count_by(COUNT_ADDITION_HINT, hcount[1]);
		    jtype = COUNT_OR_JUSTIFICATION_CLAUSE;
		} else {
		    // Can do with single proof step
		    incr_count(COUNT_OR_JUSTIFICATION_CLAUSE);
		    for (int i = 0; i < 2; i++) {
			for (int h = 0; h < hcount[i]; h++)
			    hints.push_back(lhints[i][h]);
			incr_count_by(COUNT_ADDITION_HINT, hcount[i]);
		    }
		}
	    }
	    break;

	case POG_AND:
	    {
		incr_count(COUNT_VISIT_AND);
		jtype = COUNT_AND_JUSTIFICATION_CLAUSE;
		int cnext = 0;
		// If parent is OR, will have splitting variable
		if (splitting_literal != 0) {
		    cnf->push_assigned_literal(splitting_literal);
		    jclause->add(-splitting_literal);
		    cnf->pwriter->comment("Justify node %s, assuming literal %d",
					  rnp->name(), splitting_literal);
		    // Assertion may enable BCP, but it shouldn't lead to a conflict
		    if (cnf->bcp(false) > 0) {
			cnf->pwriter->diagnose("BCP encountered conflict when attempting to justify node %s with assigned literal %d\n",
					       rnp->name(), splitting_literal);
			return 0;
		    }
		} else
		    cnf->pwriter->comment("Justify node %s", rnp->name());

		// Bundle up the literals and justify them with single call
		std::vector<int> lits;
		std::vector<int> jids;
		for (; cnext < rnp->get_degree(); cnext++) {
		    int clit = (*rnp)[cnext];
		    if (is_node(clit))
			break;
		    if (clit != splitting_literal)
			lits.push_back(clit);
		}
		if (lits.size() > 0) {
		    report(4, "Justify node %s, starting with %d literals\n", rnp->name(), lits.size());
		    // Hack to detect whether SAT call was made
		    int prev_sat_calls = get_count(COUNT_SAT_CALL);
		    if (!cnf->validate_literals(lits, jids)) {
			cnf->pwriter->diagnose("Was attempting to validate node %s", rnp->name());
			report(1, "  Arguments:");
			for (int i = 0; i < rnp->get_degree(); i++)
			    lprintf(" %d", (*rnp)[i]);
			lprintf("\n");
			cnf->pwriter->diagnose("Justification of node %s failed", rnp->name());
			cnf->pop_context();
			reason = "Failed to validate literal children of product node";
			retry = true;
			goto try_monolithic;
		    }
		    if (get_count(COUNT_SAT_CALL) > prev_sat_calls)
			incr_count(COUNT_VISIT_AND_SAT);
		    for (int jid : jids)
			hints.push_back(jid);
		}

		// Skolem nodes are at end.
		int nonskolem_degree = rnp->get_degree();
		while (nonskolem_degree > 0 && is_node_type((*rnp)[nonskolem_degree-1], POG_SKOLEM))
		    nonskolem_degree--;
		int partition_count = nonskolem_degree-cnext;

		// Deal with the node arguments.  Prepare partitioning data structures
		std::unordered_map<int,int> var2rvar;
		std::unordered_map<int,std::set<int>*> rvar2cset;
		std::set<int> *save_clauses = NULL;
		std::set<int> *pset = NULL;

		bool skolem_ok = true;
		// Process Skolem children
		for (int snext = nonskolem_degree; snext < rnp->get_degree(); snext++) {
		    std::unordered_set<int> *unit_literals = cnf->get_unit_literals();
		    int clit = (*rnp)[snext];
		    Pog_node *snp = get_node(IABS(clit));
		    hints.push_back(snp->get_defining_cid());
		    if (partition_count == 0)
			continue;
		    // Check that these are unit literals
		    for (int i = 0; i < snp->get_degree(); i++) {
			int ulit = (*snp)[i];
			if (unit_literals->find(ulit) == unit_literals->end()) {
			    report(3, "Warning: Skolem node %s (parent %s) has non-unit literal %d\n",
				   snp->name(), rnp->name(), ulit);
			    skolem_ok = false;
			}
		    }
		}

		if (!skolem_ok) {
		    // Attempt to recover from Skolem or partitioning failure via monolithic proof
		    delete jclause;
		    cnf->pop_context();
		    reason = "Found non-unit Skolem node with non-unit literal";
		    retry = true;
		    goto try_monolithic;
		}

		bool partition_ok = true;
		if (partition_ok && partition_count >= 2) {
		    report(3, "Node %s.  Attempting to partition clauses into %d sets\n",
			   rnp->name(), nonskolem_degree-cnext);
		    cnf->partition_clauses(var2rvar, rvar2cset);
		    report(3, "Justifying node %s.  Partitioned clauses into %d sets\n", rnp->name(), rvar2cset.size());
		    partition_ok = rvar2cset.size() == nonskolem_degree-cnext;
		    if (partition_ok) {
			// Check that each argument has a unique partition
			std::unordered_set<int> rvar_used;
			for (int pnext = cnext; partition_ok && pnext < nonskolem_degree; pnext++) {
			    int pclit = (*rnp)[pnext];
			    auto fid = var2rvar.find(IABS(pclit));
			    if (fid == var2rvar.end()) {
				partition_ok = false;
				report(3, "Justifying node %s.  Couldn't find partition for argument #%d.  Literal %d.\n",
				       rnp->name(), pnext, pclit);
			    }
			    else {
				int prvar = fid->second;
				if (rvar_used.find(prvar) != rvar_used.end()) {
				    partition_ok = false;
				    report(3, "Justifying node %s.  Don't have unique partition for argument #%d.  Literal %d.  Reference variable %d\n",
					   rnp->name(), pnext, pclit, prvar);
				}
				else
				    rvar_used.insert(prvar);
			    }
			}
		    } else
			report(3, "Justifying node %s.  Partitioned clauses into %d sets, but there are %d nodes to justify\n",
			       rnp->name(), rvar2cset.size(), nonskolem_degree-cnext);
		}

		if (!partition_ok) {
		    // Attempt to recover from Skolem or partitioning failure via monolithic proof
		    delete jclause;
		    cnf->pop_context();
		    reason = "Couldn't find partitioning";
		    retry = true;
		    goto try_monolithic;
		}

		// Process non-Skolem children
		for (; cnext < nonskolem_degree; cnext++) {
		    int clit = (*rnp)[cnext];
		    if (partition_count > 1) {
			// Use first literal to identify partition
			int llit = first_literal(clit);
			auto fid = var2rvar.find(IABS(llit));
			int rvar = fid->second;
			auto rfid = rvar2cset.find(rvar);
			pset = rfid->second;
			// Restrict clauses to those relevant to this partition
			report(3, "Processing argument #%d of node %s.  First literal %d.  rvar %d.  Reduce from %d to %d active clauses\n", 
			       cnext, rnp->name(), llit, rvar, (int) save_clauses->size(), (int) pset->size());
			cnf->set_active_clauses(pset);
		    } 
		    int jid = justify(clit, 0, true);
		    if (jid == 0) {
			cnf->pwriter->diagnose("Justification of node %s failed.  Argument = %d", rnp->name(), clit);
			if (partition_count > 1)
			    cnf->pwriter->diagnose(" Clauses were split into %d partitions", partition_count);
			cnf->pop_context();
			reason = "Couldn't justify node child of product node";
			retry = true;
			goto try_monolithic;
		    }
		    hints.push_back(jid);
		    if (pset != NULL)
			delete pset;
		}
		hints.push_back(rnp->get_defining_cid());
		if (save_clauses != NULL)
		    cnf->set_active_clauses(save_clauses);
	    }
	    break;

	case POG_SKOLEM:
	    {
		incr_count(COUNT_VISIT_SKOLEM);
		incr_count(COUNT_SKOLEM_JUSTIFICATION_CLAUSE);
		hints.push_back(rnp->get_defining_cid());
	    }
	    break;
	    
	default:
	    err(true, "Unknown POG type %d\n", (int) rnp->get_type());
	}
    try_monolithic:
	if (retry) {
	    cnf->pwriter->diagnose("Structural proof failed at node %s (%s).  Trying monolithic", rnp->name(), reason);
	    int cid = justify_monolithic(rlit, splitting_literal);
	    if (cid > 0)
		cnf->pwriter->diagnose("Monolithic proof succeeded at node %s.  Justifying id = %d", rnp->name(), cid);
	    else
		cnf->pwriter->diagnose("Monolithic proof also failed at node %s", rnp->name());
	    return cid;
	}


	jcid = cnf->start_assertion(jclause, false);
	for (int hint : hints)
	    cnf->add_hint(hint);
	cnf->finish_command(true);
	incr_count_by(COUNT_ADDITION_HINT, hints.size());
	incr_count(jtype);
	cnf->pop_context();
    } else if (splitting_literal != 0) {
	// Special value to let OR verification proceed
	jcid = TRIVIAL_ARGUMENT;
    } else {
	jcid = cnf->validate_literal(rlit, Cnf_reasoner::MODE_FULL);
	if (jcid == 0) {
	    cnf->pwriter->diagnose("Validation of literal %d failed", rlit);
	}
    }
    if (jcid > 0) {
	report(4, "Literal %d in POG justified by clause %d\n", rlit, jcid);
	vcount ++;
	if (rlit == root_literal) {
	    report(1, "Time = %.2f.  Justifications of %d nodes, including root, completed.  %d total clauses\n",
		   get_elapsed(), vcount, jcid - cnf->clause_count());
	} else if (vcount >= vreport_last + vreport_interval) {
	    report(1, "Time = %.2f.  Justifications of %d nodes completed.  %d total clauses.  %d SAT calls\n",
		   get_elapsed(), vcount, jcid - cnf->clause_count(), get_count(COUNT_SAT_CALL));
	    vreport_last = vcount;
	}
    }
    return jcid;
}

// Justify that formula is unsatisfiable
void Pog::justify_unsatisfiable() {
    if (cnf->is_unsatisfiable())
	// Already have empty clause
	return;
    Cnf_reduced *rcnf = cnf->extract_cnf();
    if (!rcnf->run_hinting_solver())
	err(true, "Could not generate proof of unsatisfiability\n");
    cnf->pwriter->comment("Proof of unsatisfiability");
    int start_id = cnf->clause_count() + cnf->get_proof_size() + 1;
    std::unordered_map<int, int> *justifying_ids = cnf->get_justifying_ids();
    std::unordered_set<int> real_units;
    std::vector<int> no_assigned_literals;

    while (true) {
	Clause *php = rcnf->get_proof_hint(start_id);
	Clause *pnp = rcnf->get_proof_clause(&no_assigned_literals);
	if (pnp == NULL)
	    break;
	int jcid = cnf->start_assertion(pnp, false);
	std::unordered_set<int> hints;
	for (int hi = 0; hi < php->length(); hi++)
	    hints.insert((*php)[hi]);
	incr_count_by(COUNT_ADDITION_HINT, php->length());
	// Add extra information about unit literals
	cnf->filter_units(pnp, php, real_units);
	for (int ulit : real_units) {
	    auto fid = justifying_ids->find(ulit);
	    if (fid != justifying_ids->end()) {
		int hid = fid->second;
		if (hid != jcid && hints.find(hid) == hints.end()) {
		    cnf->add_hint(hid);
		    hints.insert(hid);
		}
	    }
	}
	cnf->add_hints(php);
	cnf->finish_command(true);
	incr_count(COUNT_UNSAT_CLAUSE);
	delete php;
    }
    delete rcnf;
}

// Enumerate clauses in subgraph
void Pog::export_subgraph(int rlit, Cnf_reduced *rcnf, std::unordered_set<int> *unit_literals, std::unordered_set<int> &sofar, bool positive_only) {
    int rvar = IABS(rlit);
    if (is_node(rvar) && sofar.find(rvar) == sofar.end()) {
	sofar.insert(rvar);
	Pog_node *np = get_node(rvar);
	if (np->get_type() == POG_SKOLEM) {
	    // Only need to add tautology-generating clause
	    int cid = np->get_defining_cid();
	    // Create unit clause for node root
	    int xvar = np->get_xvar();
	    Clause *cp = new Clause(&xvar, 1);
	    rcnf->add_clause(cp, *unit_literals, cid);
	    delete cp;
	    return;
	}
	// Recursively add children
	for (int i = 0; i < np->get_degree(); i++)
	    export_subgraph((*np)[i], rcnf, unit_literals, sofar, positive_only);
	// Add defining clauses
	int degree = np->get_degree();
	int start_cid = np->get_defining_cid();
	for (int i = 0; i <= degree; i++) {
	    int cid = i + start_cid;
	    Clause *cp = cnf->get_clause(cid);
	    if (positive_only && cp->length() > 0 && (*cp)[0] < 0)
		continue;
	    rcnf->add_clause(cp, *unit_literals, cid);
	}
    }
}

// Enumerate clauses in subgraph
// Same idea.  Different representation.  
void Pog::export_subgraph(int rlit, Cnf_opt *opt_cnf, std::unordered_set<int> &sofar, bool positive_only) {
    int rvar = IABS(rlit);
    if (is_node(rvar) && sofar.find(rvar) == sofar.end()) {
	sofar.insert(rvar);
	Pog_node *np = get_node(rvar);
	if (np->get_type() == POG_SKOLEM) {
	    // Only need to add tautology-generating clause
	    int cid = np->get_defining_cid();
	    // Create unit clause for node root
	    int xvar = np->get_xvar();
	    Clause *cp = new Clause(&xvar, 1);
	    opt_cnf->add_clause(cp);
	    delete cp;
	    return;
	}
	// Recursively add children
	for (int i = 0; i < np->get_degree(); i++)
	    export_subgraph((*np)[i], opt_cnf, sofar, positive_only);
	// Add defining clauses
	int degree = np->get_degree();
	int start_cid = np->get_defining_cid();
	for (int i = 0; i <= degree; i++) {
	    int cid = i + start_cid;
	    Clause *cp = cnf->get_clause(cid);
	    if (positive_only && cp->length() > 0 && (*cp)[0] < 0)
		continue;
	    opt_cnf->add_clause(cp);
	}
    }
}


// Justify subgraph using single call to SAT solver.
// Return ID of justifying clause
int Pog::justify_monolithic(int rlit, int splitting_literal) {
    int jcid = 0;
    if (is_node(rlit)) {
	int rvar = IABS(rlit);
	Pog_node *rnp = get_node(rvar);
	cnf->new_context();
	cnf->push_assigned_literal(-rlit);
	if (splitting_literal != 0)
	    cnf->push_assigned_literal(splitting_literal);
	cnf->pwriter->comment("Preparing CNF to monolithically justify root node %s (tree size %ld)", rnp->name(), rnp->get_tree_size());
	Cnf_reduced *rcp = cnf->extract_cnf();
	int input_clause_count = rcp->clause_count();
	std::unordered_set<int> real_units;
	std::unordered_set<int> sofar;
	export_subgraph(rlit, rcp, cnf->get_unit_literals(), sofar, false);
	if (!rcp->run_hinting_solver()) {
	    report(2, "Warning: justifying subgraph with root %s.  Running SAT solver failed\n", rnp->name());
	    cnf->pop_context();
	    delete rcp;
	    return 0;
	}
	const char *fname = rcp->get_file_name();
	cnf->pwriter->comment("Ran SAT solver on file %s (%d input clauses, %d defining clauses) to monolithically justify root node %s",
			      fname, input_clause_count, rcp->clause_count() - input_clause_count, rnp->name());
	int start_id = cnf->clause_count() + cnf->get_proof_size() + 1;
	std::unordered_map<int, int> *justifying_ids = cnf->get_justifying_ids();
	while (true) {
	    Clause *php = rcp->get_proof_hint(start_id);
	    Clause *pnp = rcp->get_proof_clause(cnf->get_assigned_literals());
	    if (pnp == NULL)
		break;
	    jcid = cnf->start_assertion(pnp, false);
	    // Add extra information about unit literals
	    cnf->filter_units(pnp, php, real_units);
	    for (int ulit : real_units) {
		auto fid = justifying_ids->find(ulit);
		if (fid != justifying_ids->end()) {
		    int hid = fid->second;
		    if (hid != jcid)
			cnf->add_hint(hid);
		}
	    }
	    cnf->add_hints(php);
	    cnf->finish_command(true);
	    incr_count(COUNT_MONOLITHIC_CLAUSE);
	    incr_count_by(COUNT_ADDITION_HINT, php->length());
	    delete php;
	}
	cnf->pop_context();
	cnf->pwriter->comment("End of proof clauses from SAT solver running on file %s to justify root node %s",
			      fname, rnp->name());
	delete rcp;
    } else {
	jcid = cnf->validate_literal(rlit, Cnf_reasoner::MODE_FULL);
	if (jcid == 0) {
	    cnf->pwriter->diagnose("Validation of literal %d failed", rlit);
	    err(true, "Justifying .  Running SAT solver failed\n", rlit);
	}
    }
    if (jcid > 0) {
	report(4, "Subgraph with root literal %d in POG justified by clause %d\n", rlit, jcid);
	vcount ++;
	if (rlit == root_literal) {
	    report(1, "Time = %.2f.  Justifications of %d nodes, including root, completed.  %d total clauses\n",
		   get_elapsed(), vcount, jcid - cnf->clause_count());
	} else if (vcount >= vreport_last + vreport_interval) {
	    report(1, "Time = %.2f.  Justifications of %d nodes completed.  %d total clauses.  %d SAT calls\n",
		   get_elapsed(), vcount, jcid - cnf->clause_count(), get_count(COUNT_SAT_CALL));
	    vreport_last = vcount;
	}
    }
    return jcid;
}

void Pog::justify_mutex(Pog_node *np, std::vector<int> &hints) {
    int clit1 = (*np)[0];
    int clit2 = (*np)[1];
    int splitting_variable = IABS(find_splitting_literal(clit1, clit2));
    if (splitting_variable != 0) {
	for (int i = 0; i < 2; i++) {
	    int clit = (*np)[i];
	    if (is_node(clit)) {
		Pog_node *cnp = get_node(clit);
		for (int ci = 0; ci < cnp->get_degree(); ci++) {
		    int lit = (*cnp)[ci];
		    if (IABS(lit) == splitting_variable) {
			int hid = cnp->get_defining_cid() + 1 + ci;
			hints.push_back(hid);
		    }
		}
	    }
	}
	incr_count_by(COUNT_MUTEX_HINT, hints.size());
	incr_count(COUNT_POG_DECISION_OR);
    } else {
	// Must justify with SAT solver
	Cnf_reduced *rcp = new Cnf_reduced;
	rcp->delete_files = cnf->delete_files;
	std::unordered_set<int> *unit_literals = new std::unordered_set<int>;
	unit_literals->insert(clit1);
	unit_literals->insert(clit2);
	std::vector<int> *prefix = new std::vector<int>;
	prefix->push_back(clit1);
	prefix->push_back(clit2);
	std::unordered_set<int> sofar;
	export_subgraph(clit1, rcp, unit_literals, sofar, false);
	export_subgraph(clit2, rcp, unit_literals, sofar, false);
	if (!rcp->run_hinting_solver())
	    err(true, "Attempting mutex proof for node %s.  Running SAT solver failed\n", np->name());
	const char *fname = rcp->get_file_name();
	cnf->pwriter->comment("Ran SAT solver on file %s (%d defining clauses) to justify mutex for node %s",
			      fname, rcp->clause_count(), np->name());
	int start_id = cnf->clause_count() + cnf->get_proof_size() + 1;
	// Only need to keep final justifying ID
	int jcid;
	while (true) {
	    Clause *php = rcp->get_proof_hint(start_id);
	    Clause *pnp = rcp->get_proof_clause(prefix);
	    if (pnp == NULL)
		break;
	    jcid = cnf->start_assertion(pnp, true);
	    cnf->add_hints(php);
	    cnf->finish_command(true);
	    incr_count(COUNT_MUTEX_CLAUSE);
	    incr_count_by(COUNT_MUTEX_HINT, php->length());
	    delete php;
	}
	hints.push_back(jcid);
	incr_count_by(COUNT_MUTEX_HINT, hints.size());
	cnf->pwriter->comment("End of proof clauses from SAT solver running on file %s to justify mutex for node %s",
			      fname, np->name());
	delete rcp;
	delete unit_literals;
	delete prefix;
    }

}   




// Produce a partial assignment that satisfies the POG but contradicts the clause
// Input includes vector indicating for each node whether it implies the given clause
// Assignment specified by vector recording phase for each assigned literal
// Returns true if successful
bool Pog::get_deletion_counterexample(int cid, std::vector<bool> &implies_clause, std::vector<int> &literals) {
    // Strategy: Want to find an assignment that satisfies the POG but falsifies the input clause
    // For Skolem nodes, assign all of the literals
    // For Or nodes, chose which side to satisfy based on implies_clause flag
    // For And nodes, satisfy all literals and all child nodes
    report(1, "Creating overcount counterexample with clause #%d\n", cid);
    // Mark nodes in subgraph to be covered by counterexample
    std::vector<bool> subgraph_node;
    subgraph_node.resize(nodes.size(), false);
    // Record assignment for each variable as 0 (arbitrary), 1 (positive), or -1 (negative)
    std::vector<int> assignment;
    assignment.resize(max_input_var, 0);
    Clause *cp = cnf->get_input_clause(cid);
    cp->show(stdout);
    bool success = true;
    for (int i = 0; i < cp->length(); i++) {
	int lit = (*cp)[i];
	int var = IABS(lit);
	// Want to contradict clause
	int phase = lit > 0 ? -1 : 1;
	assignment[var-1] = phase;
    }
    subgraph_node[nodes.size()-1] = true;
    for (int nidx = nodes.size()-1; nidx >= 0; nidx--) {
	if (!subgraph_node[nidx])
	    continue;
	Pog_node *np = nodes[nidx];
	bool found = false;
	switch (np->get_type()) {
	case POG_AND:
	case POG_SKOLEM:
	    // Must satisfy all children
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while generating counterexample\n", clit);
		    int idx = clit-start_extension_var;
		    if (implies_clause[idx]) {
			err(false, "Couldn't generate counterexample.  Operand %d to Pog node %s falsified by clause\n",
			    i+1, np->name());
			success = false;
		    }
		    subgraph_node[clit-start_extension_var] = true;
		} else {
		    int var = IABS(clit);
		    int phase = clit > 0 ? 1 : -1;
		    int ophase = assignment[var-1];
		    if (ophase != 0 && ophase != phase) {
			// Failure
			err(false, "Couldn't generate counterexample at Pog node %s. Child literal %d gave conflict to partial assignment\n",
			    np->name(), clit);
			success = false;
		    }
		    assignment[var-1] = phase;
		}
	    }
	    break;
	case POG_OR:
	    // Choose first child for which implication did not hold
	    found = false;
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while generating counterexample\n", clit);
		    int cidx = clit-start_extension_var;
		    if (!implies_clause[cidx]) {
			subgraph_node[cidx] = true;
			found = true;
			Pog_node *cnp = nodes[cidx];
			break;
		    }
		} else {
		    // See if value has been or can be assigned
		    int var = IABS(clit);
		    int phase = clit > 0 ? 1 : -1;
		    bool was_set = true;
		    if (assignment[var-1] == 0) {
			assignment[var-1] = phase;
			was_set = false;
		    }
		    if (assignment[var-1] == phase) {
			// This branch satisfied by assignment
			found = true;
			break;
		    }
		}
	    }
	    if (!found) {
		// Failure
		err(false, "Couldn't generate counterexample at Pog node %s. Couldn't satisfy either child\n",
		    np->name());
		return false;
	    }
	    break;
	default:
	    err(true, "Unknown POG type %d for node %s\n", (int) np->get_type(), np->name());
	}
    }
    // Now convert to list of literals
    literals.clear();
    for (int var = 1; var <= max_input_var; var++) {
	int phase = assignment[var-1];
	if (phase != 0)
	    literals.push_back(phase * var);
    }
    return success;
}

// Objective: Prove that Pog cannot evalute to true for any input that doesn't satisfy the clause
// I.e., that pog node logically implies clause
// Return true if successful.
// If fail, convert overcount_literals into vector of literals that satisfies the POG but not the clause
bool Pog::delete_input_clause(int cid, int unit_cid, Literal_set &lset, std::vector<int> &overcount_literals) {
    Clause *cp = cnf->get_input_clause(cid);
    // Convert to set representation
    lset.load_clause(cp);
    // Label each node by whether or not it is guaranteed to negated by the negated clause
    std::vector<bool> implies_clause;
    implies_clause.resize(nodes.size(), false);
    // Vector starting with clause ID and then having hints for deletion
    std::vector<int> *dvp = new std::vector<int>;
    dvp->push_back(cid);
    if (cp->tautology()) {
	cnf->pwriter->clause_deletion(dvp);
	if (dvp->size() > 0)
	    incr_count_by(COUNT_DELETION_HINT, dvp->size() - 1);
	delete dvp;
	return true;
    }
    dvp->push_back(unit_cid);
    for (int nidx = 0; nidx < nodes.size(); nidx++) {
	Pog_node *np = nodes[nidx];
	bool implies = false;
	switch (np->get_type()) {
	case POG_AND:
	case POG_SKOLEM:
	    implies = false;
	    // Must have at least one child imply the clause
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while deleting clause %d\n", clit, cid);
		    implies = implies_clause[clit-start_extension_var];
		    if (implies) {
			dvp->push_back(np->get_defining_cid()+i+1);
			break;
		    }
		} else {
		    implies = lset.contains(clit);
		    if (implies) {
			dvp->push_back(np->get_defining_cid()+i+1);
			break;
		    }
		}
	    }
	    break;
	case POG_OR:
	    // Must have all children implying the clause
	    implies = true;
	    for (int i = 0; i < np->get_degree(); i++) {
		int clit = (*np)[i];
		if (is_node(clit)) {
		    if (clit <= 0)
			err(true, "Encountered invalid Pog identifier %d while deleting clause %d\n", clit, cid);
		    implies &= implies_clause[clit-start_extension_var];
		    if (!implies)
			break;
		} else
		    implies &= lset.contains(clit);
		    if (!implies)
			break;
	    }
	    if (implies) {
		dvp->push_back(np->get_defining_cid());
	    }
	    break;
	default:
	    err(true, "Unknown POG type %d for node %s\n", (int) np->get_type(), np->name());
	}
	implies_clause[nidx] = implies;	    
    }
    bool proved = implies_clause[nodes.size()-1];
    if (proved) {
	cnf->pwriter->clause_deletion(dvp);
	if (dvp->size() > 0)
	    incr_count_by(COUNT_DELETION_HINT, dvp->size() - 1);
    } else {
	if (!get_deletion_counterexample(cid, implies_clause, overcount_literals))
	    err(false, "Error attempting to delete clause.  Prover failed to generate proof, but also couldn't generate counterexample\n");
    }
    delete dvp;
    return proved;
}

#define LPL 25

static void print_solution(std::vector<int> &literals) {
    int sidx;
    report(1, "Printing counterexample with %d literals\n", literals.size());
    for (sidx = 0; sidx + LPL < literals.size(); sidx += LPL) {
	lprintf("s");
	for (int i = sidx; i < sidx+LPL; i++)
	    lprintf(" %d", literals[i]);
	lprintf("\n");
    }
    lprintf("s");
    for (int i = sidx; i < literals.size(); i++)
	lprintf(" %d", literals[i]);
    lprintf(" 0\n");
}

static void eliminate_nondata(std::vector<int> &literals, std::unordered_set<int> *data_variables) {
    int found_count = 0;
    for (int i = 0; i < literals.size(); i++) {
	int lit = literals[i];
	int var = IABS(lit);
	if (data_variables->find(var) != data_variables->end())
	    literals[found_count++] = lit;
    }
    literals.resize(found_count);
}


bool Pog::delete_input_clauses(int unit_cid) {
    //    2023-07-16.  Found that using RUP validation is MUCH slower
    //    return delete_input_clauses_rup(unit_cid);

    int dreport_interval = cnf->clause_count() / REPORT_MAX_COUNT;
    if (dreport_interval < REPORT_MIN_DELETION_INTERVAL)
    	dreport_interval = REPORT_MIN_INTERVAL;
    int dreport_last = 0;

    cnf->pwriter->comment("Delete input clauses");
    Literal_set lset(cnf->max_variable());
    std::vector<int> overcount_literals;
    bool overcount = false;
    for (int cid = 1; !overcount && cid <= cnf->clause_count(); cid++) {
	bool deleted = delete_input_clause(cid, unit_cid, lset, overcount_literals);
	if (!deleted) {
	    if (overcount_literals.size() > 0) {
		report(1, "OVERCOUNT.  Generating partial assignment that contradicts clause %d\n", cid);
		print_solution(overcount_literals);
		if (data_variables != NULL) {
		    eliminate_nondata(overcount_literals, data_variables);
		    report(1, "\n");
		    report(1, "Data variable assignment:\n");
		    print_solution(overcount_literals);
		}
	    } else {
		report(1, "OVERCOUNT.  Can't justify\n");
	    }
	    report(1, "Skipping remaining deletions\n", cid);
	    overcount = true;
	}
	if (cid >= dreport_interval + dreport_last) {
	    report(1, "Elapsed = %.2f.  %d input clauses deleted\n", get_elapsed(), cid);
	    dreport_last = cid;
	}
    }
    return !overcount;
}

bool Pog::delete_input_clauses_rup(int unit_cid) {
    cnf->pwriter->comment("Delete input clauses using reverse unit propagation");
    report(3, "Delete input clauses using reverse unit propagation\n");
    // Shift to perform BCP only on POG clauses
    Watcher watches;
    cnf->deactivate_all_clauses();

    // Add justifying clause
    cnf->activate_clause(unit_cid);
    // Add defining clauses
    for (Pog_node *np : nodes) {
	int degree = np->get_degree();
	int start_cid = np->get_defining_cid();
	for (int ci = 0; ci <= np->get_degree(); ci++) 
	    cnf->activate_clause(start_cid + ci);
    }
    cnf->watches_setup(watches);
    // Delete each input clause
    std::vector<int> hints;
    std::vector<int> dvec;
    int input_clause_count = cnf->clause_count();
    for (int cid = 1; cid <= input_clause_count; cid++) {
	report(3, "Deleting input clause #%d\n", cid);
	hints.clear();
	Clause *icp  = cnf->get_clause(cid);
	cnf->rup_validate(icp, false, watches, hints);
	dvec.clear();
	dvec.push_back(cid);
	for (int hint : hints)
	    dvec.push_back(hint);
	cnf->pwriter->clause_deletion(&dvec);
	if (dvec.size() > 0)
	    incr_count_by(COUNT_DELETION_HINT, dvec.size() - 1);
    }
    return true;
}    

