#include "PDR.hpp"
#include "BMC.hpp"
#include "BMPDR.hpp"
#include "aig.hpp"
#include "basic.hpp"
#include <iostream>
#include <string>
#include <chrono>
using namespace std;
using namespace std::chrono;

int main(int argc, char **argv){
    auto t_begin = system_clock::now();

    cout<<"c USAGE: ./modelchecker <aig-file> [<option>|<property ID>]* "<<endl;
    Aiger *aiger = load_aiger_from_file(string(argv[1]));
    int property_index = 0;
    bool sc = 0, acc = 0;
    for (int i = 2; i < argc; ++i){
        if (string(argv[i]) == "-sc")
            sc = 1;
        else if (string(argv[i]) == "-acc")  
            acc = 1;
        else 
            property_index = (unsigned) atoi(argv[i]);
    }
    int nframes = 999;
    PDR pdr(aiger, property_index, sc, acc);
    bool res = pdr.check();   
    cout << res << endl;

    //bmc_mixed_pdr
    // BMC bmc(aiger, property_index, 999);   
    // PDR pdr(aiger, property_index, sc, acc);    
    // BMPDR bmpdr(&bmc, &pdr);
    // int res = bmpdr.check();
    // cout << res << endl;
    
    // bmc
    // BMC bmc(aiger, property_index, nframes);
    // bmc.initialize();
    // int res_bmc = bmc.check(); 
    // cout << res_bmc << endl;
   
    delete aiger;
    auto t_end = system_clock::now();
    auto duration = duration_cast<microseconds>(t_end - t_begin);
    double time_in_sec = double(duration.count()) * microseconds::period::num / microseconds::period::den;
    cout<<"c time = "<<time_in_sec<<endl;
    return 1;
}