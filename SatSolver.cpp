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

#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <algorithm>
#include <functional>
#include "SatSolver.h"

#define HALFLIFE 128
#define _DT 32		// RSAT phase selection threshold 

struct compScores: public binary_function<unsigned, unsigned, bool>{
	unsigned *activity;
	compScores(unsigned *myActivity) : activity(myActivity) {}
	bool operator()(unsigned a, unsigned b) const{ 
		return SCORE(a) > SCORE(b); 
	}
};

SatSolver::SatSolver(Cnf &cnf): CnfManager(cnf){
	// initialize parameters 
	nextRestart = luby.next() * (lubyUnit = 512);
	nextDecay = HALFLIFE;

	// assertUnitClauses has failed
	if(currentDLevel == 0) return;

	// assert pure literals
	for(int i = 1; i <= (int) vc; i++) if(!assigned[i]){
		if(ACTIVITY(i, _POSI) == 0 && ACTIVITY(i, _NEGA) > 0)
			// ante is NULL, as opposed to empty clause for implied literals
			assertLiteral(-i, NULL);	
		else if(ACTIVITY(i, _NEGA) == 0 && ACTIVITY(i, _POSI) > 0)
			assertLiteral(i, NULL);
	}

	// initialize varOrder
	nVars = 0; for(unsigned i = 1; i <= vc; i++) 
		if(!assigned[i] && SCORE(i) > 0){
			varOrder[nVars++] = i;
			phase[i] = (ACTIVITY(i, _POSI) > ACTIVITY(i, _NEGA))?_POSI:_NEGA;
		}
	sort(varOrder, varOrder + nVars, compScores(activity));
	for(unsigned i = 0; i < nVars; i++) varPosition[varOrder[i]] = i; 
	nextVar = 0; 
	nextClause = clauses.size() - 1; 
}

int SatSolver::selectLiteral(){
	unsigned x = 0;
	
	// pick best var in unsatisfied conflict clause nearest to top of stack
	// but only search 256 clauses
	int lastClause = nextClause > 256 ? (nextClause - 256) : 0;
	for(int i = nextClause; i >= lastClause; i--){
		int *p = clauses[nextClause = i];

		// skip satisfied clauses
		bool sat = false; 
		for(; (*p); p++) if(SET(*p)){ sat = true; break; }
		if(sat) continue;

		// traverse again, find best variable of clause
		int score = -1;
		for(p = clauses[i]; (*p); p++) if(FREE(*p) && ((int) SCORE(VAR(*p))) > score){
			x = VAR(*p); score = SCORE(x);
		}

		// RSAT phase selection
		int d = ACTIVITY(x, _POSI) - ACTIVITY(x, _NEGA);
		if(d > _DT) return x; else if(-d > _DT) return -x;
		else return (phase[x] == _POSI)?(x):-(int)(x);
	}

	// fall back to VSIDS 
	for(unsigned i = nextVar; i < nVars; i++){
		if(!assigned[varOrder[i]]){
			x = varOrder[i];
			nextVar = i + 1;

			// RSAT phase selection
			int d = ACTIVITY(x, _POSI) - ACTIVITY(x, _NEGA);
			if(d > _DT) return x; else if(-d > _DT) return -x;
			else return (phase[x] == _POSI)?(x):-(int)(x);
		}
	}
	return 0;
}

bool SatSolver::run(){
	if(currentDLevel == 0) return false; 		// assertUnitClauses has failed
	for(int lit; (lit = selectLiteral());){ // pick decision literal
		if(!decide(lit)) do{ 		// decision/conflict
			// conflict has occurred in dLevel 1, unsat 
			if(aLevel == 0) return false;

			// score decay
			if(nConflicts == nextDecay){
				nextDecay += HALFLIFE;
				scoreDecay();
			}

			// rewind to top of clause stack
			nextClause = clauses.size() - 1; 

			// restart at dLevel 1 
			if(nConflicts == nextRestart){
				nRestarts++;
				nextRestart += luby.next() * lubyUnit;
				backtrack(1);
				if(currentDLevel != aLevel) break;

			// partial restart at aLevel 
			}else backtrack(aLevel);
		}while(!assertCL());		// assert conflict literal
	}
	if(!verifySolution()){ printf("s UNKOWN\n"); exit(0); }
	return true;	
}

bool SatSolver::verifySolution(){
	int lit, *pool = litPools[0];
	for(unsigned i = 0; i < litPoolSizeOrig;){
		bool satisfied = false;
		while((lit = pool[i++])) if(SET(lit)){
			satisfied = true;
			while(pool[i++]);
			break;
		}
		if(!satisfied) return false;
	}
	return true;
}

void SatSolver::printSolution(FILE *ofp){
	for(unsigned i = 1; i <= vc; i++)
		if(assigned[i] && truthVal[i]) fprintf(ofp, "%d ", i);
		else if(assigned[i] && !truthVal[i]) fprintf(ofp, "-%d ", i);
	fprintf(ofp, "0\n");
}

void SatSolver::printStats(){
	printf("c %d decisions, %d conflicts, %d restarts\n", nDecisions, nConflicts, nRestarts);
}
