/****************************************************************************/
/* Generic procedures for the WPDS library.				    */

#include "wpdsInt.h"

void wInit ()
{
	wIdentInit();
}

void wFinish ()
{
	wIdentFinish();
}

void *nullfn(void *a, void *b) { return NULL; }
int   eqfn(void *a, void *b)   { return a == b; }
void *null()			       { return NULL; }

wSemiring* nulsr()
{
	wSemiring* s = malloc(sizeof(wSemiring));
	s->extend = &nullfn;
	s->combine = &nullfn;
    s->diff = NULL; 
	s->one = &null; 
	s->zero = &null; 
	s->quasione = NULL;
	s->eq = &eqfn;
	s->ref = NULL;
	s->deref = NULL;
	return s;
}


/****************************************************************************/
/* Convenient procedures for pre* / post* given a weighted PDS and FA.	    */

wFA* wReach (wPDS *pds, wFA *fa, char mode, char trace)
{
	wSat *prcs = wSatCreate(pds->sr,mode,trace);
	wRule *pt;
	wTrans *t;

	for (pt = pds->rules; pt; pt = pt->next)
		wSatAugRule(prcs,pt->from_state,pt->from_stack,
			pt->to_state,pt->to_stack1,pt->to_stack2,pt->label,pt);

	for (t = fa->transitions; t; t = t->next)
		 wSatAddTrans(prcs,t->from,t->name,t->to,t->label);

	while ((t = wSatPopTrans(prcs)))
		wSatAugTrans(prcs,t);

	return wSatDelete(prcs);
}

wFA* wPrestar (wPDS *pds, wFA *fa, char trace)
{
	return wReach(pds,fa,SAT_PRE,trace);
}

wFA* wPoststar (wPDS *pds, wFA *fa, char trace)
{
	return wReach(pds,fa,SAT_POST,trace);
}
