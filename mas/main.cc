// This is a prototype implementation of the learning module of L-PANTS
// Tab size: 2
// Author: Robert White (Shuai Wang)
// Institute: ILLC, UvA
#include <iostream>
#include <stdio.h>
#include <time.h> 
#include <stdlib.h> 
#include <string>
#include <list>
#include <algorithm>
#include <cmath> 
#include <exception>
#include "smodels.h"
#include "api.h"
#include "atomrule.h"
#include <ctime>
#include <bdd.h>


using namespace std;

typedef list<int> condition;
typedef list<int> world;

// the name attribute is not used in these test
struct action {
	string name;
	condition pre;
  condition post;
} ;

struct safe_action
{
	string name;
	bdd pre;
	condition post;
};

// In this project we consider only events of one action. Mixed events will be considered later
struct event
{
	condition before;
	action action;
	condition after;
};

typedef list<event> stream;
typedef condition answer;
typedef list<answer> epistemicmodel;


// this function takes a domain n and return a list of literals less of length 
// less than n.
// the size of precondition and post-condition are both of size s

bool abs_compare (int x, int y){
	if (abs (x) > abs (y)) return false;
		else return true;
};

// get a list of random numbers from 0 to n without repetition (not even the its negation)
condition get_pre_condition (int n, int s) { 
	condition l;
	// get a random length < n
	while ((int)l.size() != s) {
		int v = (rand() % n) +1;
		int sign = (rand() % 2) * 2 -1;
		list<int>::iterator pos1 = find(l.begin(), l.end(), v); 
		list<int>::iterator pos2 = find(l.begin(), l.end(), v * (-1));
		if (pos1 == l.end() && pos2 == l.end()){
			l.push_back(v * sign);
			// cout << "the number is: " << v * sign << endl;;
		}
	}//end for	
  l.sort(abs_compare);
	return l;
};

// a before-world is implemented the same as a precondition.
world get_before_world (int domain){
	return (get_pre_condition(domain, domain));

}

condition get_post_condition (int n, int active, condition pre){
	// we consider restricted precondition only.
	// 
	condition l;
	// flip over the pre condition first
	for (std::list<int>::iterator it = pre.begin(); it != pre.end(); it++){
		l.push_back(*it *(-1));
	}
	
	while ((int)l.size() != active) {
		int v = (rand() % n) +1;
		int sign = (rand() % 2) * 2 -1;
		list<int>::iterator pos1 = find(l.begin(), l.end(), v); 
		list<int>::iterator pos2 = find(l.begin(), l.end(), v * (-1));
		//make sure also this number doesn't occure in the precondition
		list<int>::iterator pos = find(pre.begin(), pre.end(), v*sign);
		if (pos1 == l.end() && pos2 == l.end() && pos == pre.end()){
			l.push_back(v * sign);
			// cout << "the number is: " << v * sign << endl;;
		}
	}//end for	
  l.sort(abs_compare);
	return l;
};

action get_precondition_free_action (int domain, int size){
	action a;
	// condition precondition;
	// a.pre = precondition; // only declare, do nothing else.
	a.post = get_pre_condition(domain, size);
	return a;
}

void print_condition(condition c){
	list<int>::iterator i;
	for(i = c.begin(); i != c.end(); i++) cout << *i << " ";
	cout<<endl;
};

void print_action(action a){
	cout<<"\tThe pre-codition is: ";
	print_condition(a.pre);
	cout<<"\tThe post-condition is: ";
	print_condition(a.post);
	cout<<"\n";
};

void print_safe_action (safe_action a){
	cout << "The pre-codition in ROBDD is:" << endl;
	cout << bddtable << a.pre << endl;
	cout<<"\tThe post-condition is: ";
	print_condition(a.post);
}

void print_world(world w){
	print_condition(w);
	cout<<endl;
};

// test if the world satisfies the precondition of the action
// that is to say, all the literals are in the world w.
// So the intersection of them is the same as the precondition.
bool action_validity (action a, world w) {
	bool result = true;
	if (a.pre.begin() == a.pre.end()) return true; // precondition free action.
	for (std::list<int>::iterator it = a.pre.begin(); result && it != a.pre.end(); it++){
		list<int>::iterator pos1 = find(w.begin(), w.end(), *it); 
		if (pos1 == w.end()) result = false; // some precondition is not satisfied.
	}
	return result;
};

// The postcondition of an action will be included in an action after it got performed
world perform_action (action a, world w) {
	// since this is a simple implementation, the validity is expected to be checked
	world after;

	for (std::list<int>::iterator it = w.begin(); it != w.end(); it++){
		list<int>::iterator pos1 = find(a.post.begin(), a.post.end(), *it); 
		list<int>::iterator pos2 = find(a.post.begin(), a.post.end(), *it * (-1)); 
		if (pos1 != a.post.end()) 
			after.push_back(*it); // some post-condition is not satisfied.
		else if (pos2 != a.post.end())
			after.push_back(*it * (-1));
		else after.push_back(*it);
	}
	return after;
};

// the precondition of the action is included in the generated world
world generate_world_from_action(action a, int size){
	
	world after;
	for (int index = 1; index <= size; index ++){
		//generate a literal 
		int l = index * ((rand() % 2) * 2 - 1);
		list<int>::iterator pos1 = find(a.pre.begin(), a.pre.end(), l);
		list<int>::iterator pos2 = find(a.pre.begin(), a.pre.end(), l*(-1));
		if (pos1 != a.pre.end()){ // this generated literal is in precondition
			after.push_back(l);
		} else if (pos2 != a.pre.end()){ // the literal is not in, but its negation is.
			after.push_back(l*(-1));
		} else {
			after.push_back(l); // neither of them, 
		}
	}
	
	return after;
};


// get an action with precondition
action get_full_action (int domain, int active, int demand){
	if (active < demand) cout << "Demand too stict" <<endl;
	action a;
	condition precondition;
	precondition = get_pre_condition(domain, demand);
	a.pre = precondition;
	condition postcondition;
	postcondition = get_post_condition (domain, active, a.pre);
	a.post = postcondition;
	return a;
}

//print the before world and the after world
void print_before_after (world before, world after){
	cout<<"The world before is: ";
	print_world(before);
	cout<<"Thwe world after is: ";
	print_world(after);

}

//test if there is only one model using Smodel as an ASP solver.
bool only_one_model (Smodels* smodels){
	if (smodels->model ()){
		if (not smodels->model())
			return true;
	}
	return false;
}

int count_models (Smodels* smodels){
  // Compute all stable models.
  int model_counter = 0;
  while (smodels->model ()){  // Returns 0 when there are no more models
  	model_counter ++;
    // smodels->printAnswer ();  // Prints the answer
  }
  // smodels->revert ();  // Forget everything that happened after init ().
	return model_counter;
}

int count_and_print (Smodels* smodels){
  // Compute all stable models.
  int model_counter = 0;
  while (smodels->model ()){  // Returns 0 when there are no more models
  	model_counter ++;
    smodels->printAnswer ();  // Prints the answer
  }
  // smodels->revert ();  // Forget everything that happened after init ().
	return model_counter;
}


//add constrants to the solver by encoding the worlds
void encode_worlds(Api *api, world w_before, world w_after){
	for(list<int>::iterator i = w_before.begin(); i != w_before.end(); i++){
		list<int>::iterator pos2 = find(w_after.begin(), w_after.end(), (*i * (-1))); //if it's negation there 
		if (pos2 != w_after.end()){
		// 	if it's negation is there.
			char s[10];
			Atom *c;
			if (*i > 0){
			  sprintf(s, "%d", *i);
				strcat(s, "-");
			} else {
				sprintf(s, "%d", *i *(-1));
				strcat(s, "+");
			}
			c = api->get_atom (s);
			api->set_compute (c, true);
		}

		for(list<int>::iterator i = w_after.begin(); i != w_after.end(); i++){
			char s[10];
			Atom *c;
			if (*i > 0){
			  sprintf(s, "%d", *i);
				strcat(s, "-");
			} else {
				sprintf(s, "%d", *i *(-1));
				strcat(s, "+");
			}
			c = api->get_atom (s);
			api->set_compute (c, false);		
		}
	}
}

// encode each proposition
void encode_propositions (Api *api, int i){

  Atom *ap = api->new_atom ();
  Atom *an = api->new_atom ();
  Atom *ax = api->new_atom ();
	
	char s0[10];
	char s1[10];
	char s2[10];

  sprintf(s0, "%d", i);
  sprintf(s1, "%d", i);
  sprintf(s2, "%d", i);
	
	strcat(s0, "+");
	strcat(s1, "-");
	strcat(s2, "x");

  api->set_name (ap, s0); 
  api->set_name (an, s1);
  api->set_name (ax, s2);


  api->begin_rule (BASICRULE);
  api->add_head (ap);
  api->add_body (an, false);  // Add "-b" to the body.
  api->add_body (ax, false);
  api->end_rule ();

  api->begin_rule (BASICRULE);
  api->add_head (ap);
  api->add_body (ax, false);  // Add "-b" to the body.
  api->add_body (an, false);
  api->end_rule ();

  api->begin_rule (BASICRULE);
  api->add_head (an);
  api->add_body (ap, false);  // Add "-b" to the body.
  api->add_body (ax, false);
  api->end_rule ();

  api->begin_rule (BASICRULE);
  api->add_head (an);
  api->add_body (ax, false);  // Add "-b" to the body.
  api->add_body (ap, false);
  api->end_rule ();

  api->begin_rule (BASICRULE);
  api->add_head (ax);
  api->add_body (ap, false);  // Add "-b" to the body.
  api->add_body (an, false);
  api->end_rule ();

  api->begin_rule (BASICRULE);
  api->add_head (ax);
  api->add_body (an, false);  // Add "-b" to the body.
  api->add_body (ap, false);
  api->end_rule ();


  api->begin_rule (CHOICERULE);
  api->add_head (an);
  api->add_head(ax);
  api->add_head(ap);
  api->add_body(an, false);
  api->add_body(ap, false); 
  api->add_body(ax, false);
  api->set_atleast_body(2);
  api->end_rule();

}


// initialise the domain
void setup_prop_vars(Api *api, int domain){
	for (int i = 1; i <= domain; i ++)
	encode_propositions(api, i);
  api->done ();  // After this you shouldn't change the rules.
}

// the precondition-free action learning function
int action_learning (int domain, action act)
{
  Smodels smodels;
  Api api (&smodels.program);
  api.remember ();
  setup_prop_vars (&api, domain);
  smodels.init (); 

  int smodel_size = 0;
  int count = 0;
	while (smodel_size != 1){
		world w_before = get_before_world(domain);
		world w_after = perform_action(act, w_before);
		encode_worlds(&api, w_before, w_after);
		smodels.revert (); 
		if (only_one_model(&smodels)) smodel_size = 1;
		count ++;
	}
	smodels.revert();
	action learnt;  

  if (smodels.model ())  // There is a model.
  {
  	// for each number, we get positive/negative, then unknown.
  	for (int index = 1; index <= domain; index++){
  		char sp[10];
  		char sn[10];
			Atom *ap;
			Atom *an;

		  sprintf(sp, "%d", index);
		  sprintf(sn, "%d", index);
			strcat(sp, "+");
			strcat(sn, "-");

			ap = api.get_atom (sp);
			an = api.get_atom (sn);

			if (ap->Bpos) learnt.post.push_back(index);
			if (an->Bpos) learnt.post.push_back(index * (-1));
  	}
  }
  // cout<<"The action learnt is:"<<endl;
  // print_action(learnt);

  // cout<<"The original action is:"<<endl;
  // print_action(act);

	list<int>::iterator i = learnt.post.begin();
	list<int>::iterator j = act.post.begin();

	while (i != learnt.post.end()){
		if (*i != *j)
			cout << "Error!" <<endl;
		i++;
		j++;
	}

	if (j != act.post.end()) cout << "Error!" <<endl;

  return count;
}



// ----------------<  Evaluation 1  >--------------

struct effe_section
{
	int domain;
	int section_min;
	int section_max;
	double average_time;
	double iterations;
	/* data */
};


effe_section effeciency_section_test(int domain, int min, int max, int repeat){


	double iteration_acc = 0.0;
 	double time_acc = 0.0;

  for (int i = 0; i < repeat; i ++){
		int active = 0;
  	while (active <= min || active > max){
			active = (rand() % domain) + 1;
		}

		action act = get_precondition_free_action(domain, active); 
  	

  	clock_t start;
    double duration;
    start = clock();

    int count = action_learning(domain, act);
    duration = (clock() - start ) / (double) CLOCKS_PER_SEC;
    // cout<<"duration is: " << duration << endl;
    time_acc += duration;
    iteration_acc = iteration_acc + count; 
  }

  effe_section e;
  e.domain = domain;
  e.section_max = max;
  e.average_time = time_acc / repeat;
  e.iterations = iteration_acc / repeat;
  return e;
}



list<effe_section> eval1_sections (int domain, int step, int repeat){
	// list<effe_section> result = effeciency_all_sections (range, step, repeat);
	list<effe_section> result;

	cout.setf(ios::fixed,ios::floatfield);
  cout.precision(3);

	for (int i = step; i <= domain; i += step){
		effe_section e = effeciency_section_test(domain, i-step, i, repeat);
		result.push_back(e);
	}

	return result;
}

void eval1(int total){
	int sections = 10;
	int repeat  = 20;
	list<list<effe_section> > all;
	for (int i = total/sections; i <= total ; i += total/sections){
		cout<< " ------ " << "the domain is:" << i <<" divided into 10 sections (repeats 20 times each) ------ " <<endl; 
		all.push_back(eval1_sections (i, i/sections, repeat));
	}

// -- print the average time for each domain 
	cout << "The average time / iteration for each section of each domain: " <<endl;
	list<list<effe_section> >::iterator index;
	index = all.begin();
	while  (index != all.end()){
		list<effe_section>::iterator i;
		i = (*index).begin();
		cout << i->domain; 
		for(; i != (*index).end(); i++){
			// cout<< " & "<< i->average_time << "/" << i->iterations;
			printf (" & %.3f/%.1f", i->average_time, i->iterations );
		}
		cout <<" \\\\ \\hline" <<endl;
		index ++;
	}
	cout << "The average time for each domain: " <<endl;
	//print the average time for each domain
	index = all.begin();
	while  (index != all.end()){
		list<effe_section>::iterator i;
		i = (*index).begin();
		cout << "(" << i->domain; 
		double average_time = 0;
		for(; i != (*index).end(); i++){
			average_time += i->average_time;
		}
		average_time = average_time / sections;
		cout << " , " << average_time << ") " <<endl;
		index ++;
	}

	cout << "The average iteration for each domain: " <<endl;
	//print the average time for each domain
	index = all.begin();
	while  (index != all.end()){
		list<effe_section>::iterator i;
		i = (*index).begin();
		cout << "(" << i->domain; 
		double average_iter = 0.0;
		for(; i != (*index).end(); i++){
			average_iter += i->iterations;
		}
		average_iter = average_iter / sections;
		// cout << " , " << average_iter << ") " <<endl;
		printf (" , %.1f)\n", average_iter);
		index ++;
	}


}


// ---------------------- Action Learning with Pre-condition -----------

struct conditional_effe_section
{
	int domain;
	int demand;
	int section_min;
	int section_max;
	double average_time;
	double iterations;
};



void vset_bdd_gbchandler(int pre, bddGbcStat *s) {
  // cout<<"test"<<endl;
  // we don't output anything for garbage collection
}

//simply to change the name of this function :)
void print_bdd(bdd b){
	bdd_printtable(b);
}


bdd encode_world_bdd (condition c){
  bdd b;
  bdd init = bddtrue;
	for (std::list<int>::iterator it = c.begin(); it != c.end(); it++){	
	  if (*it < 0){
	  	// cout<<"what?"<<endl;
	  	b = bdd_nithvar(*it * (-1));
	  	init = init & (b);
	  	
	  }else{
	  	b = bdd_ithvar(*it);
	  	init = init & (b);
	  }
	}
	// bdd_done();
	return init;
}


// the learning function of action learning with precondition
int full_action_learning (int domain, action act)
{
	Smodels smodels;
  Api api (&smodels.program);

  api.remember ();
	setup_prop_vars (&api, domain);
  smodels.init (); 

	int smodel_size = 0;
	int count = 0;
	safe_action a;
	a.pre = bddfalse;

	while (smodel_size != 1){
		action tmp;
		tmp.post = act.pre;
		world w_before = perform_action(tmp, get_before_world(domain));

		if (action_validity(act, w_before)){
			world w_after = perform_action(act, w_before);
			encode_worlds(&api, w_before, w_after);
			smodels.revert (); 
			if (only_one_model(&smodels)) smodel_size = 1;	
			bdd w = encode_world_bdd(w_before);
			bdd  p = (a.pre) | w; 
			a.pre = p;
			// cout<<"update BDD"<<endl;
			// print_bdd(a.pre);
		}
		count ++;
	}

	smodels.revert();

  if (smodels.model ())  // There is a model.
  {
  	// for each number, we get positive/negative, then unknown.
  	for (int index = 1; index <= domain; index++){
  		char sp[10];
  		char sn[10];
			Atom *ap;
			Atom *an;

		  sprintf(sp, "%d", index);
		  sprintf(sn, "%d", index);
			strcat(sp, "+");
			strcat(sn, "-");

			ap = api.get_atom (sp);
			an = api.get_atom (sn);

			if (ap->Bpos) a.post.push_back(index);
			if (an->Bpos) a.post.push_back(index * (-1));

  	}
  }
 
  // learning completed
  // cout<<"The precondition is:" <<endl;
  // print_bdd(a.pre);
  // cout<<"The postcondition is:"<<endl;
  // print_condition(a.post);

	// a very simple validation funciton
  list<int>::iterator i = a.post.begin();
	list<int>::iterator j = act.post.begin();

	while (i != a.post.end()){
		if (*i != *j)
			cout << "Error!" <<endl;
		i++;
		j++;
	}

	if (j != act.post.end()) cout << "Error!" <<endl;

  return count;
}


// ----------------<  Evaluation 2  >--------------

conditional_effe_section effeciency_section_active_conditional (int domain, int min, int max, int repeat){

	double iteration_acc = 0;
 	double time_acc = 0.0;

  for (int i = 0; i < repeat; i ++){
		int active = 0;
		// if min == max then ....
		if (min == max) active = min;
		else {
			while (active <= min || active > max){
				active = (rand() % domain) + 1;
			}
		}

		int demand = (rand() % active) + 1;

		action act = get_full_action(domain, active, demand);

  	clock_t start;
    double duration;
    start = clock();

    int count = full_action_learning(domain, act);
    duration = (clock() - start ) / (double) CLOCKS_PER_SEC;

    time_acc = time_acc + duration;
    iteration_acc = iteration_acc + count; 
  }

  conditional_effe_section e;
  e.domain = domain;
  // e.demand = demand;
  e.section_min = min;
  e.section_max = max;
  e.average_time = time_acc / repeat;
  e.iterations = iteration_acc / repeat;
  return e;
}

// active power oriented testing

list<conditional_effe_section> eval2_sections (int domain, int step, int repeat){
	// list<effe_section> result = effeciency_all_sections (range, step, repeat);
	list<conditional_effe_section> result;

	cout.setf(ios::fixed,ios::floatfield);
  cout.precision(3);

	for (int i = step; i <= domain; i += step){
		conditional_effe_section e = effeciency_section_active_conditional(domain, i-step, i, repeat);
		result.push_back(e);
	}

	return result;
}

void eval2(int total){

	bdd_init (total, total);
	bdd_setvarnum (total*(total * (5/100 +1)));
	bdd_gbc_hook(vset_bdd_gbchandler);


	int sections = 10;
	int repeat  = 20;
	list<list<conditional_effe_section> > all;
	for (int i = total/sections; i <= total ; i += total/sections){
		cout<< " ------ " << "the domain is:" << i <<" divided into 10 sections (repeats 20 times each) ------ " <<endl; 
		all.push_back(eval2_sections (i, i/sections, repeat));
	}

// -- print the average time for each domain 
	cout << "The average time / iteration for each section of each domain: " <<endl;
	list<list<conditional_effe_section> >::iterator index;
	index = all.begin();
	while  (index != all.end()){
		list<conditional_effe_section>::iterator i;
		i = (*index).begin();
		cout << i->domain; 
		for(; i != (*index).end(); i++){
			// cout<< " & "<< i->average_time << "/" << i->iterations;
			printf (" & %.3f/%.1f", i->average_time, i->iterations );
		}
		cout <<" \\\\ \\hline" <<endl;
		index ++;
	}
	cout << "The average time for each domain: " <<endl;
	//print the average time for each domain
	index = all.begin();
	while  (index != all.end()){
		list<conditional_effe_section>::iterator i;
		i = (*index).begin();
		cout << "(" << i->domain; 
		double average_time = 0;
		for(; i != (*index).end(); i++){
			average_time += i->average_time;
		}
		average_time = average_time / sections;
		// cout << " , " << average_time << ") " <<endl;
		printf(" , %.3f) \n", average_time);
		index ++;
	}

	cout << "The average iteration for each domain: " <<endl;
	//print the average time for each domain
	index = all.begin();
	while  (index != all.end()){
		list<conditional_effe_section>::iterator i;
		i = (*index).begin();
		cout << "(" << i->domain; 
		double average_iter = 0.0;
		for(; i != (*index).end(); i++){
			average_iter += i->iterations;
		}
		average_iter = average_iter / sections;
		// cout << " , " << average_iter << ") " <<endl;
		printf(" , %.1f)\n", average_iter);
		index ++;
	}


}


//---------demand-oriented testings------
// this test is about fixing a demand and see how the effeciency change as we increase the active power 
conditional_effe_section effeciency_section_demand_conditional (int domain, int demand, int min, int max, int repeat){


	double  iteration_acc = 0.0;
 	double time_acc = 0.0;

  for (int i = 0; i < repeat; i ++){
		int active = 0;
		// if min == max then ....
		if (min == max) active = min;
		else {
			while (active <= min || active > max){
				active = (rand() % domain) + 1;
			}		
		}
  
		action act = get_full_action(domain, active, demand);

  	clock_t start;
    double duration;
    start = clock();

    int count = full_action_learning(domain, act);
    duration = (clock() - start ) / (double) CLOCKS_PER_SEC;

    time_acc = time_acc + duration;
    iteration_acc = iteration_acc + count; 
  }

  conditional_effe_section e;
  e.domain = domain;
  e.demand = demand;
  e.section_min = min;
  e.section_max = max;
  e.average_time = time_acc / repeat;
  e.iterations = iteration_acc / repeat;
  return e;
}

void test_demand_and_print (int domain, int step, int repeat){

	list<conditional_effe_section> result;
	for (int demand = step; demand <= domain; demand += step){
		for (int max = demand ; max <= domain; max += step){
				conditional_effe_section e;
			if (max == demand) 
				e = effeciency_section_demand_conditional(domain, demand, max, max, repeat);
			else 
				e = effeciency_section_demand_conditional(domain, demand, max - step, max, repeat);

		result.push_back(e);
		}
	}

	list<conditional_effe_section>::iterator i;
	for(i = result.begin(); i != result.end(); i++){
		cout<< "The domain is: " << i->domain
		<< "\tThe demand is: " << i->demand 
		<< "\tthe (postcondition) range is:" << i->section_min
		<< "\t to \t" << i->section_max;
		printf ("\tThe average time: %.3f ", i->average_time);
		// << "\tThe average time: " << i->average_time ;
		printf ("\tThe average N.iter: %.1f\n", i->iterations);
		// << "\tThe average N.iteration: " << i->iterations <<endl;
	}
	cout<<endl;
}

void test_demand(){
	// test with a fixed deman (the colorful fig)
	test_demand_and_print(100, 10, 20);
}




int main (int argc, char * argv[]) {

	if (argc == 1) cout <<"See the README file for instructiions." <<endl;
	
	int eval = atoi(argv[1]);
	// enter evaluation one: action learning without precondition
	if (eval == 1){
		int total = atoi(argv[2]);
		eval1(total);
	}else if (eval == 2){
		// evaluation two: conitional action learning
		int total = atoi(argv[2]);
		eval2(total);
	}else if (eval == 3){
		test_demand();
	}else {
		cout <<"there is not such a evaluation to be performed." <<endl;
	}
	
  return 0;
};

