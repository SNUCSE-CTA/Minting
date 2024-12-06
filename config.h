typedef long long weight_type;
typedef unsigned short degree_type;

typedef int number_type;
#define EDGE_LABEL
// Constants
const int BITS_PER_LABEL = 4; // the maximum number of labels per label that we count as NLF

const int Start = 0;
const int LoadNumVertex = 1;
const int LoadVertex = 2;
const int LoadNumEdge = 3;
const int LoadEdge = 4;
const int GFU_FORMAT = 5;
const int IGRAPH_FORMAT = 6;
const int CFL_FORMAT = 7;
const int MAX_NUM_VERTEX = 257;
const int MAX_QUERY_DEGREE = 100;
const int MAX_NUM_LABEL = 48000;
const int UINT64_SIZE = sizeof(uint64_t) * 8;
const bool useFailingSet = true;
int NLFSize = -1;
int nUniqueLabel = 0;
int nUniqueEdgeLabel = 0;
const double filter_th = 1.5f;




