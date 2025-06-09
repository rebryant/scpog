#include "report.h"
#include "cnf_opt.hh"

#define OPT_VLEVEL 5

Cnf_opt::Cnf_opt(std::unordered_set<int> *_keep_variables) {
    has_conflict = false;
    keep_variables = _keep_variables;
}

Cnf_opt::~Cnf_opt() {
    clear();
}

void Cnf_opt::clear() {
    for (auto iter : literal_map) {
	delete iter.second;
    }
    literal_map.clear();
    clause_lookup.clear();
    for (Clause *np : clauses) {
	if (np != NULL)
	    delete np;
    }
    clauses.clear();
    unit_keep_literals.clear();
    has_conflict = false;
}


// Return true if clause actually added.  False if it is a duplicate
bool Cnf_opt::add_clause(Clause *cp) {
    Clause *ncp = new Clause(cp);
    if (ncp->tautology())
	return false;
    // See if its unique
    unsigned h = ncp->hash();
    auto bucket = clause_lookup.equal_range(h);
    for (auto iter = bucket.first; iter != bucket.second; iter++) {
	Clause *ecp = iter->second;
	if (ncp->is_equal(ecp)) {
	    if (verblevel >= OPT_VLEVEL) {
		report(OPT_VLEVEL, "OPT: Not adding redundant clause: ");
		ncp->show(stdout);
	    }
	    // Skip clause
	    return false;
	}
    }
    for (int i = 0; i < ncp->length(); i++) {
	int lit = (*ncp)[i];
	if (literal_map.find(lit) == literal_map.end()) {
	    literal_map[lit] = new std::unordered_set<Clause *>;
	    literal_map[-lit] = new std::unordered_set<Clause *>;
	    report(5, "OPT: Created literal maps for %d and %d\n", lit, -lit);
	}
	literal_map[lit]->insert(ncp);
    }
    clauses.push_back(ncp);
    clause_lookup.insert({h,ncp});
    report(OPT_VLEVEL, "OPT: Added clause: ");
    if (verblevel >= OPT_VLEVEL)
	ncp->show(stdout);
    return true;
}
   
void Cnf_opt::delete_clause(Clause *cp) {
    for (int i = 0; i < cp->length(); i++) {
	int lit = (*cp)[i];
	literal_map[lit]->erase(cp);
    }
    unsigned h = cp->hash();
    auto bucket = clause_lookup.equal_range(h);
    for (auto iter = bucket.first; iter != bucket.second; iter++) {
	if (iter->second == cp) {
	    clause_lookup.erase(iter);
	    if (verblevel >= OPT_VLEVEL) {
		report(OPT_VLEVEL, "OPT: Deleting clause ");
		cp->show();
	    }
	    break;
	}
    }
    cp->make_tautology();
}

Clause *Cnf_opt::resolve(int var, Clause *pos_cp, Clause *neg_cp) {
    Clause *ncp = new Clause();
    for (int i = 0; i < pos_cp->length(); i++) {
	int lit = (*pos_cp)[i];
	if (lit == var)
	    continue;
	ncp->add(lit);
    }
    for (int i = 0; i < neg_cp->length(); i++) {
	int lit = (*neg_cp)[i];
	if (lit == -var)
	    continue;
	ncp->add(lit);
    }
    return ncp;
}

void Cnf_opt::show(FILE *outfile) {
    int max_variable = compact_clauses();
    for (int lit : unit_keep_literals) {
	int var = IABS(lit);
	max_variable = std::max(max_variable, var);
    }
    fprintf(outfile, "p cnf %d %d\n", max_variable, (int) (unit_keep_literals.size() + clauses.size()));
    for (int lit : unit_keep_literals) 
	fprintf(outfile, "%d 0\n", lit);
    for (Clause *cp : clauses)
	cp->show(outfile);
}

void Cnf_opt::cause_conflict() {
    clear();
    has_conflict = true;
    Clause *cp = new Clause();
    add_clause(cp);
    delete cp;
}

void Cnf_opt::optimize() {
    int max_variable = compact_clauses();
    report(1, "OPT: Starting with %d clauses\n", (int) clauses.size());
    bool propagated = unit_propagate();
    bool eliminated = ordered_bve(2, max_variable);
    int propagate_count = 1;
    int eliminate_count = 1;
    while (propagated || eliminated) {
	propagated = false;
	if (eliminated) {
	    propagated = unit_propagate();
	    propagate_count++;
	}
	eliminated = false;
	if (propagated) {
	    eliminated = ordered_bve(2, max_variable);
	    eliminate_count++;
	}
    }
    compact_clauses();
    report(1, "OPT: Performed %d unit propagation %d variable elimination passes.  Final clause count = %d unit + %d non-unit\n",
	   propagate_count, eliminate_count, (int) unit_keep_literals.size(), (int) clauses.size());
}

bool Cnf_opt::ordered_bve(int max_degree, int max_variable) {
    if (has_conflict)
	return false;
    report(2, "BVE.  Max degree = %d.  Retain %d variables\n", max_degree, (int) keep_variables->size());
    if (verblevel >= OPT_VLEVEL) {
	report(OPT_VLEVEL, "Initial CNF:\n");
	show(stdout);
    }
    int max_added = max_degree*max_degree - 2*max_degree;
    int elim_var_count = 0;
    int added_clause_count = 0;
    int duplicate_clause_count = 0;
    int deleted_clause_count = 0;
    int revisit_count = 0;
    int evar = 1;
    while (evar <= max_variable) {
	int next_evar = evar + 1;
	if (is_keep_literal(evar)) {
	    evar = next_evar;
	    continue;
	}
	int pos_degree = 0;
	if (literal_map.find(evar) != literal_map.end())
	    pos_degree = literal_map[evar]->size();
	int neg_degree = 0;
	if (literal_map.find(-evar) != literal_map.end())
	    neg_degree = literal_map[-evar]->size();
	if (pos_degree == 0 && neg_degree == 0) {
	    evar = next_evar;
	    continue;
	}
	int added = pos_degree*neg_degree - (pos_degree+neg_degree);
	if (added <= max_added) {
	    report(OPT_VLEVEL, "BVE.  Eliminating variable %d.  Will add %d clauses and delete %d (pos %d, neg %d)\n",
		   evar, pos_degree * neg_degree, pos_degree + neg_degree, pos_degree, neg_degree);
	    elim_var_count++;
	    std::vector<Clause *> deletion_list;
	    for (Clause *pos_cp : *literal_map[evar]) {
		deletion_list.push_back(pos_cp);
		for (Clause *neg_cp : *literal_map[-evar]) {
		    Clause *np = resolve(evar, pos_cp, neg_cp);
		    if (add_clause(np))
			added_clause_count++;
		    else
			duplicate_clause_count++;
		}
	    }
	    for (Clause *neg_cp : *literal_map[-evar]) {
		for (int i = 0; i < neg_cp->length(); i++) {
		    int lit = (*neg_cp)[i];
		    if (lit > 0 && lit < next_evar && !is_keep_literal(lit)) {
			report(OPT_VLEVEL, "BVE.  Resetting elimination variable to %d\n", lit);
			revisit_count++;
			next_evar = lit;
		    }
		}
		deletion_list.push_back(neg_cp);
	    }
	    for (Clause *cp : deletion_list) {
		delete_clause(cp);
		deleted_clause_count ++;
	    }
	} else {
	    report(OPT_VLEVEL, "BVE.  Keeping variable %d\n", evar);
	}
	evar = next_evar;
    }
    report(1, "BVE: Max degree %d.  Eliminated %d variables.  Added %d and deleted %d clauses.  %d duplicates rejected.  %d revists\n",
	   max_degree, elim_var_count, added_clause_count, deleted_clause_count, duplicate_clause_count, revisit_count);
    return elim_var_count > 0;
}

bool Cnf_opt::unit_propagate() {
    if (has_conflict)
	return false;
    report(OPT_VLEVEL, "UPROP: Starting unit propagation\n");
    int added_clause_count = 0;
    int duplicate_clause_count = 0;
    int deleted_clause_count = 0;
    std::vector<int> unit_literals;
    std::unordered_set<int> unit_set;
    int prop_count = 0;
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (!cp->tautology() && cp->length() == 1) {
	    int lit = (*cp)[0];
	    if (unit_set.find(-lit) != unit_set.end()) {
		cause_conflict();
		report(OPT_VLEVEL, "UPROP: Found conflicting unit clauses for variable %d\n", IABS(lit));
		return false;
	    }
	    unit_literals.push_back(lit);
	    unit_set.insert(lit);
	    report(OPT_VLEVEL, "UPROP: Found unit literal %d in clause %d\n", (*cp)[0], cid);
	    delete_clause(cp);
	}
    }
    int old_size = (int) unit_literals.size();
    report(OPT_VLEVEL, "UPROP: Starting unit propagation.  Initially have %d unit clauses\n", (int) unit_literals.size());
    if (verblevel >= OPT_VLEVEL) {
	report(OPT_VLEVEL, "UPROP: Initial cnf:\n");
	show(stdout);
    }

    while (prop_count < unit_literals.size()) {
	int ulit = unit_literals[prop_count++];
	report(OPT_VLEVEL, "UPROP: Propagating %d\n", ulit);
	std::vector<Clause *> deletion_list;
	for (Clause *cp : *literal_map[ulit]) 
	    deletion_list.push_back(cp);

	report(OPT_VLEVEL, "UPROP: Looking for clauses containing %d\n", -ulit);
	for (Clause *cp : *literal_map[-ulit]) {
	    if (verblevel >= OPT_VLEVEL) {
		printf("c UPROP: Processing: ");
		cp->show();
	    }
	    Clause *ncp = new Clause();
	    for (int i = 0; i < cp->length(); i++) {
		int lit = (*cp)[i];
		if (lit != -ulit)
		    ncp->add(lit);
	    }
	    deletion_list.push_back(cp);
	    if (verblevel >= OPT_VLEVEL) {
		printf("c UPROP: Created: ");
		ncp->show();
	    }
	    if (ncp->length() == 0) {
		report(OPT_VLEVEL, "UPROP: Conflict detected while propagating %d\n", ulit);
		cause_conflict();
		delete ncp;
		return false;
	    } else if (ncp->length() == 1) {
		int lit = (*ncp)[0];
		unit_literals.push_back(lit);
		unit_set.insert(lit);
		if (unit_set.find(-lit) != unit_set.end()) {
		    report(OPT_VLEVEL, "UPROP: Conflict detected for variable %d\n", IABS(ulit));
		    cause_conflict();
		    return false;
		}
		report(OPT_VLEVEL, "UPROP: Adding unit %d\n", lit);
		delete ncp;
	    } else {
		report(OPT_VLEVEL, "UPROP: Adding new clause\n");
		if (add_clause(ncp))
		    added_clause_count++;
		else
		    duplicate_clause_count++;
	    }
	}
	deleted_clause_count += deletion_list.size();
	for (Clause *cp : deletion_list)
	    delete_clause(cp);
    }
    for (int ulit : unit_literals) {
	if (is_keep_literal(ulit))
	    unit_keep_literals.push_back(ulit);
    }
    int dsize = unit_literals.size() - old_size;
    report(1, "UPROP: Added %d units.  Added %d and deleted %d clauses.  %d duplicates rejected\n",
	   dsize, added_clause_count, deleted_clause_count, duplicate_clause_count);
    return dsize > 0;
}

int Cnf_opt::compact_clauses() {
    int nsize = 0;
    int max_variable = 0;
    for (int cid = 1; cid <= clauses.size(); cid++) {
	Clause *cp = clauses[cid-1];
	if (cp->tautology()) {
	    delete cp;
	    continue;
	}
	max_variable = std::max(max_variable, cp->max_variable());
	clauses[nsize++] = cp;
    }
    report(OPT_VLEVEL, "OPT: Resizing clauses %d --> %d\n", (int) clauses.size(), nsize);
    clauses.resize(nsize);
    return max_variable;
}

