/*************************
Copyright 2007 Jinbo Huang

This file is part of Tinisat.

Tinisat is free software; you can redistribute it 
and/or modify it under the terms of the GNU General 
Public License as published by the Free Software 
Foundation; either version 2 of the License, or
(at your option) any later version.

Tinisat is distributed in the hope that it will be
useful, but WITHOUT ANY WARRANTY; without even the
implied warranty of MERCHANTABILITY or FITNESS FOR 
A PARTICULAR PURPOSE. See the GNU General Public 
License for more details.

You should have received a copy of the GNU General
Public License along with Tinisat; if not, write to
the Free Software Foundation, Inc., 51 Franklin St, 
Fifth Floor, Boston, MA  02110-1301  USA
*************************/

#ifndef _CNF_MANAGER
#define _CNF_MANAGER
#include <vector>
#include <deque>
#include "Cnf.h"
using namespace std;

#define _NEGA 0		// variable values are negative
#define _POSI 1		// positive, or

#define SIGN(lit) 	(((lit) > 0)?_POSI:_NEGA)
#define VAR(lit)	(abs(lit))
#define NEG(lit)	(-(lit))

#define FREE(lit) 	(!assigned[VAR(lit)])
#define SET(lit)	(assigned[VAR(lit)] && truthVal[VAR(lit)] == SIGN(lit))
#define RESOLVED(lit)	(assigned[VAR(lit)] && truthVal[VAR(lit)] == SIGN(NEG(lit)))
#define IMPLIST(lit) 	(vars[VAR(lit)].imp[SIGN(lit)]) 
#define WATCHLIST(lit) 	(watched[(VAR(lit)*2 + SIGN(lit))])
#define ADD_TO_WATCHLIST(lit, p) 	(((vector<int *> &)watched[(VAR(lit)*2 + SIGN(lit))]).push_back((p)))
#define ACTIVITY(var,pos) (activity[(var)*2+(pos)])
#define SCORE(var)	(ACTIVITY(var,0)+ACTIVITY(var,1))

struct Variable{
	int *imp[2];			// implication lists for binary clauses
};

class CnfManager{
protected:
	unsigned vc; 			// variable count 
	Variable *vars; 		// array of variables

	// the following arrays contain one entry per variable
	bool* mark;            // used in 1-UIP derivation
	bool* phase;           // suggested phase for decision
	bool* assigned;        // variable value is assigned
	bool* truthVal;        // assigned truth value
	unsigned* dLevel;	   // decision level where var is set
	int **antecedent;      // antecedent clause if implied
	unsigned *activity;    // scores for literals
	vector<int *> *watched;  // watch lists for other clauses

	unsigned *varOrder;		// variables ordered by score
	unsigned *varPosition;		// variable position in varOrder
	unsigned nextVar;		// starting point in varOrder

	int *litPool; 			// array of literals as in clauses
	unsigned litPoolSize; 		// literal pool size
	unsigned litPoolSizeOrig; 	// original clauses only
	unsigned litPoolCapacity;	// capacity of current litPool
	vector<int *> litPools;		// all litPools created
	vector<int *> clauses;		// array of conflict clauses 
	int nextClause; 		// starting point to look for unsatisfied conflict clause	

	int *stackTop; 			// decision/implication stack
	unsigned aLevel;		// assertion level
	unsigned currentDLevel; 		// decision level
	unsigned nDecisions; 		// num of decisions
	unsigned nConflicts;		// num of conflicts
	unsigned nRestarts;		// num of restarts
	deque<int> conflictLits;	// stores conflict literals
	deque<int> tmpConflictLits;	// ditto, temporary
	int *conflictClause;		// points to learned clause in litPool 

	void setLiteral(int lit, int *ante);	// set value, ante, level 
	bool assertLiteral(int lit, int *ante);	// set literal and perform unit propagation
	bool assertUnitClauses();		// assert initial unit clauses
	bool decide(int lit);			// increment dLevel and call assertLitreal
	void learnClause(int *firstLit);	// store learned clause in conflictLits and call addClause
	void addClause();			// add conflictLits to litPool and set up watches
	bool assertCL();			// assert literal implied by conflict clause
	void backtrack(unsigned level);		// undo assignments in levels > level 
	void scoreDecay();			// divide scores by constant
	void updateScores(int *first);		// update variable scores and positions
public:
	CnfManager(){};
	CnfManager(Cnf &cnf);
	~CnfManager();
};

inline bool CnfManager::assertCL(){
	return assertLiteral(*conflictClause, conflictClause + 1);
}

inline bool CnfManager::decide(int lit){
	nDecisions++; currentDLevel++;
	return assertLiteral(lit, NULL);
}

inline void CnfManager::backtrack(unsigned bLevel){
	for(unsigned var; dLevel[var = VAR(*(stackTop - 1))] > bLevel;){
		if(dLevel[var] < currentDLevel) phase[var] = truthVal[var];
		assigned[var] = false;
		if(varPosition[var] < nextVar) nextVar = varPosition[var];
		stackTop--;
	}
	currentDLevel = bLevel;
}

inline void CnfManager::scoreDecay(){
	// this may slightly disturb var order
	// e.g., (7 + 7) => (3 + 3) whereas (6 + 8) => (3 + 4)
	for(unsigned i = 1; i <= vc; i++){
		ACTIVITY(i, 0) >>= 1;
		ACTIVITY(i, 1) >>= 1;
	}
}
#endif
