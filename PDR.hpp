#pragma once

#include <fstream>
#include <vector>
#include <iostream>
#include <chrono>
#include <map>
#include <set>
#include <string>
#include "aig.hpp"
#include "basic.hpp"
#include "sat_solver.hpp"
using namespace std;

#ifndef TIMESTAMP
#define TIMESTAMP
    extern unsigned long long state_count;
#endif

// save information for debug
class Variable{ 
public:
    int dimacs_var; // the index in variables set;
    string name;    // the name of this variable
    Variable(int dimacs_index, string name){
        this->dimacs_var = dimacs_index;
        this->name = name;
    }
    Variable(int dimacs_index, char type, int type_index, bool prime){
        this->dimacs_var = dimacs_index;
        assert(type=='i' || type=='o' || type=='l' || type == 'a');
        stringstream ss;
        ss << type;
        ss << type_index;
        if(prime)
            ss << "'";
        ss >> name;
}
};

class And{
public:
    int o, i1, i2;
    And(int o, int i1, int i2):o(o),i1(i1),i2(i2){}
};


// Cone: constraints, bad, latches
// Real_Init: latches_default /\ constraints
// Real_Bad: bad \/ not constraints
// State: inputs + latches (must meet constraints)
// Obligation: State + frame_k
// Cubes: only latches
// Frame: Cubes
// F0(I), F1, F2, F3, ..., Foo(blocked by all)
// Ri = Fi + ... + Foo

// Invaints:
// R0 = I; Ri -> Ri+1; Ri -> -Bad

class State{
public:
    vector<int> latches, inputs;
    State * next = nullptr;
    unsigned long long index;
    int failed;
    int failed_depth;
    State(){
        state_count++;
        index =  state_count;
        failed = 0;
        failed_depth = 0;
    }
    State(vector<int> l, vector<int> i):latches(l),inputs(i){
        state_count++;
        index =  state_count;
        failed = 0;
        failed_depth = 0;
    }
    void clear(){latches.clear(); inputs.clear(); next = nullptr;}
};

class Obligation{
public:
    State *state = nullptr;
    int frame_k;
    int depth;
    Obligation(State *s, int k, int d):state(s),frame_k(k),depth(d){}
    bool operator<(const Obligation &b) const{
        if (frame_k < b.frame_k) return true;       // prefer lower levels (required)
        if (frame_k > b.frame_k) return false;
        if (depth > b.depth) return true;           // prefer shallower (heuristic)
        if (depth < b.depth) return false;
        // if (depth < b.depth) return true;           // prefer shallower (heuristic)
        // if (depth > b.depth) return false;
        //return ((state) < ((b.state)));
        return ((state->index) < ((b.state)->index));
    }
};

class Lit_CMP{
public:
    bool operator()(const int &a, const int &b) const{
        if(abs(a) == abs(b))
            return a < b;
        else
            return abs(a) < abs(b);
    }
};
class heuristic_Lit_CMP{
public:
    vector<float> counts;
    bool operator()(const int &a, const int &b) const{
        if (abs(b) > counts.size()-1){
            cout << "heuristic bug found";
            return false;
        } 
        if (abs(a) > counts.size()-1){
            cout << "heuristic bug found";
            return true;
        } 
        return (counts[abs(a)] < counts[abs(b)]);
    }
};

typedef vector<int> Cube; // the lits in the cube must be sorted

class Cube_CMP{
public:
    bool operator()(const Cube &a, const Cube &b) const{
        if(a.size() != b.size())
            return a.size() < b.size();
        else{
            for(int i=0; i<a.size(); ++i){
                if(a[i] != b[i])
                    return a[i] < b[i];
            }
        }
        return false;
    }
};


class Frame{
public:
    set<Cube, Cube_CMP> cubes;
    set<Cube, Cube_CMP> succ_push; //pp
    SATSolver *solver = nullptr;
    Frame(){
        this->solver = new CaDiCaL();
        // this->solver = new minisatCore();
        cubes.clear();
        succ_push.clear(); //pp
    }
};


class PDR
{
    Aiger *aiger;
    
    // the interal data structure for Aiger (in CNF dimacs format).
    int nInputs, nLatches, nAnds;
    vector<Variable> variables;
    vector<And> ands;
    vector<int> nexts;
    vector<int> constraints, constraints_prime;
    vector<int> init_state; set<int> set_init_state;
    int bad, bad_prime;
    const int unprimed_first_dimacs = 2;
    int primed_first_dimacs;
    int property_index;
    bool use_acc, use_pc;
    map<int, int> map_to_prime, map_to_unprime; // used for mapping ands
    
    // for IC3
    minisatSimp *satelite = nullptr;
    CaDiCaL *lift = nullptr;
    CaDiCaL *init = nullptr;
    // minisatCore *lift = nullptr;
    // minisatCore *init = nullptr;

    State *cex_state_idx = nullptr;
    bool find_cex = false;
    vector<State *> states, cex_states;

    int nSafe, nUnsafe, nSkip, nPush, nUnpush, nCore, nCorelen, nCube, nCubelen;

public:
    // Frame & Cubes
    vector<Frame> frames;
    set<Obligation> obligation_queue;
    Cube core;
    bool top_frame_cannot_reach_bad;

    // Parameters & statistics
    std::chrono::_V2::steady_clock::time_point start_time;
    const int option_mic_tries = 3;
    const int option_ctg_tries = 3;
    const int option_ctg_max_depth = 1;
    const int option_max_joins = 1<<20;
    int nQuery, nCTI, nCTG, nmic, nCoreReduced, nAbortJoin, nAbortMic;

    heuristic_Lit_CMP* heuristic_lit_cmp = nullptr;
    int earliest_strengthened_frame;

    // for incremental check
    bool first_incremental_check;

    PDR(Aiger *aiger, int index, bool acc, bool pc): aiger(aiger), property_index(index), use_acc(acc), use_pc(pc){
        start_time = std::chrono::steady_clock::now();
        first_incremental_check = 1;
        nSafe = nUnsafe = nSkip = nPush = nUnpush = nCore = nCorelen = nCube = nCubelen = 0;
    }
    ~PDR(){
        if(satelite != nullptr) delete satelite;
        if(lift != nullptr) delete lift;
        if(init != nullptr) delete init;
    }

    // Aiger
    void simplify_aiger();
    void initialize(); 
    void translate_to_dimacs();

    // auxiliary functions
    int prime_var(int var);
    int prime_lit(int lit);


    // Main IC3/PDR framework
    bool is_init(vector<int> &latches);
    bool is_inductive(SATSolver *solver, int fi, const Cube &cube, bool gen_core = false, bool reverse_assumption = true);
    void new_frame();
    bool rec_block_cube();
    bool rec_block_cube2();
    bool propagate();    
    bool get_pre_of_bad(State *s);
    void extract_state_from_sat(SATSolver *sat, State *s, State *succ);
    void mic(Cube &cube, int k, int depth);
    bool CTG_down(Cube &cube, int k, int depth, set<int> &required);
    void generalize(Cube &cube, int level);
    bool check_BMC0();
    bool check_BMC1();
    bool check();
    int incremental_check();
    int incremental_check2();
    

    void encode_init_condition(SATSolver *s);   // I
    void encode_bad_state(SATSolver *s);        // Bad cone, used for test SAT?[I/\-B]
    void encode_translation(SATSolver *s);      // Latches' Cone + Bad' cone, -Bad must hold
    

    void clear_po();
    void add_cube(Cube &cube, int k, bool to_all=true, bool ispropagate = false);
    int  depth(){return frames.size() - 2;}
    bool cube_is_null(Cube &c){return c.size() == 0;}
    bool state_is_null(State *s){return s->latches.size() == 0;}
    double get_runtime();


    // log
    void show_aag();
    void show_state(State *s);
    void show_witness();
    void log_witness();
    void show_PO();
    void show_variables();
    void show_lit(int l) const;
    void show_litvec(vector<int> &lv) const;
    void show_frames();


    //heuristic function
    void initialize_heuristic();
    void updateLitOrder(Cube &cube, int level);

};

