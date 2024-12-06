#include <vector>
#include <cassert>
#include <cstdlib>
#include <iostream>

using namespace std;

class MemPool
{   
public:
    long long block_size;
    vector<void*> free_vec;
    void init(long long ibs){
        block_size = ibs;
    }

    void* alloc(){
        if(!free_vec.empty()){
            void* ret = free_vec.back();
            free_vec.pop_back();
            assert(ret != NULL);
            return ret;
        }
        else{
            void* ret = malloc((long long)block_size);
            assert(ret!=NULL);
            return ret;
        }
    }

    void free(void* p){
        assert(p!=NULL);
        free_vec.push_back(p);
    }
};