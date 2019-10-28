//Winamax Golf Coding challenge
//naive solution

//still working on a much cleverer solution that treats the problem
//as a Maximum flow problem, specifically a new subclass of that problem
//called Policy Compliant Maximum Flow which was the subject of a research
//paper released earlier this year.

#include <stdio.h>
#include <iostream>
#include <string>
#include <vector>
#include <algorithm>
#include <map>
#include <queue>
#include <cassert>
#include <cstring>

#define DEBUG 0
#define DEBUGMATRIX 1
#define DEBUGSHOTMATRIX 0
#define DEBUGEACHPATH 1
#define DEBUGITERATIONS 1

using namespace std;

enum NodeType {
    Empty,
    Water,
    Ball,
    Hole
};

enum Direction{
    N,
    E,
    W,
    S,
    Internal,
    NONE
};

typedef struct {
    int cap=0;
    vector<pair<int,int>> allowedshots;
    bool phantom =false;
    int p_sc;
    int p_csc;
} GraphNode;

class GridProblem {
    
private:
    int height;
    int width;
    char ** inputData;
    vector< pair<int,map<int,int> > > ballPaths;
    vector<int> holeIds;
    vector<int> ballIds;
    long graphsize;
    
    const int sourceid = 0;
    const int sinkid = 1;
    
public:
    GridProblem(int h, int w, string * input) {
    height = h;
        width = w;
        inputData = new char*[height];
        assert(input!=NULL);
        
        map<int,int> ballids;
        for(int i=0; i<h; i++) {
            inputData[i] = new char[width];
            for(int j=0; j<w; j++) {
                inputData[i][j] = input[i].at(j);
                if(isdigit(inputData[i][j])) {
                    char arr[2];
                    arr[0] = inputData[i][j];
                    arr[1]=0;
                    int sc = atoi(arr);
                    ballids[i*width+j] = sc;
                }
                else if(inputData[i][j]=='H') {
                    holeIds.push_back(i*width+j);
                }
            }
        }
        
        //Step 1: Find possible paths from Balls to Holes
        //This step only looks at Nodes that are accesible by using jumps of shotcount graphsize
        // and therefore does not include the nodes that are travelled over but not stopped at
        map<int, vector<vector<int>>> mp;
        for(auto p: ballids) {
            int sc = p.second;
            int id = p.first;
            ballPaths.clear();
            map<int,int> parent;
            FindPaths(sc, id, parent, NONE);
            vector<vector<int>> data;
            for(auto pair : ballPaths) {
                int id_iter = pair.first;
                vector<int> temp;
                while(id_iter!=-1) {
                    temp.insert(temp.begin(), id_iter);
                    id_iter = pair.second[id_iter];
                }
                data.push_back(temp);
            }
            mp.insert(make_pair(id, data));
        }
    
        //Step 2: Fill in the found paths with the intervening nodes.
        //check and exclude paths which cross other balls and holes
        //and ensure uniqueness of the path
        map<int, vector<vector<int>> > mp2;
        for(auto ballpaths: mp) {
            vector<vector<int>> paths;
            for(auto path: ballpaths.second) {
                int prev = ballpaths.first;
                vector<int> newpath;
                map<int,int> idmap;
                bool reject = false;
                for(auto id: path) {
                    if(id== prev) {
                        continue;
                    }
                    int y= id/width;
                    int x= id%width;
                    
                    int yprev = prev/width;
                    int xprev = prev%width;
                    
                    int dx = x-xprev;
                    int dy = y-yprev;
                    enum Direction d;
                    int dist = 0;
                    if(dx >0) {
                        d=E;
                        dist = dx;
                        dx=1;
                    }
                    else if(dx<0) {
                        d=W;
                        dist = -dx;
                        dx=-1;
                    }
                    else if(dy>0) {
                        d=S;
                        dist = dy;
                        dy=1;
                    }
                    else if(dy <0) {
                        d=N;
                        dist = -dy;
                        dy=-1;
                    }
                    
                    if(newpath.size() ==0) {
                        newpath.push_back(prev);
                    }
                    while(dist!=0) {
                        xprev+=dx;
                        yprev+=dy;
                        int nid = yprev*width+xprev;
                        if(isdigit(inputData[yprev][xprev])|| (inputData[yprev][xprev]=='H'&& dist!=1) ) {
                        	reject=true;
                        	break;
                    	}
                    	if(idmap.count(nid)>0) {
                        	reject = true;
                        	break;
                    	}
                        newpath.push_back(nid);
                        idmap[nid] = 1;
                        dist--;
                    }
                    if(reject)
                        break;
                    prev=id;
                    
                }
                if(!reject)
                	paths.push_back(newpath);
            }
            mp2.insert(make_pair(ballpaths.first, paths));
        }
        
        
        
        //Step 3: find which paths are compatible and incompatible by
        //inserting all paths into a new graph and checking which other paths
        //the inserted path conflicts with
        
        //Count the number of nodes required for Adjacency Representation
        int pathcount = 0;
        map<int, int> idcount;
        for(auto pair: mp2) {
            for(auto path: pair.second) {
                for(auto id: path) {
                    int i = 1;
                    if(idcount.count(id)==1) {
                        i=idcount[id]+1;
                    }
                    idcount[id]=i;
                }
                pathcount++;
            }
        }
        
        //create helper structures for paths
        map<pair<int, int>, vector<int> > mp3;
        map<pair<int,int>, int> pairToId;
        map<int, pair<int,int>> idToPair;
        int pcount = 0;
        for(auto pair:mp2) {
            for(int i=0; i<pair.second.size(); i++) {
                vector<int> v(pathcount, 0);
                mp3[make_pair(pair.first, i)] = v;
                pairToId[make_pair(pair.first, i)] = pcount;
                idToPair[pcount++] =make_pair(pair.first, i);
            }
        }
        
        graphsize = (2*idcount.size()) + 2; //include source and sink;
        GraphNode ** graph = new GraphNode*[graphsize];
        for(int i=0; i<graphsize; i++) {
            graph[i] = new GraphNode[graphsize];
            memset(graph[i], 0, sizeof(GraphNode)*graphsize);
        }
        
        map<int,int> newToOldId;
        map<int, int> oldToNewId;
    
        map<int, vector<pair<int,int>> > pathsUsingId;
        vector<int> nholeIds;
        
        int count = 2;
        
        //create new graph by inserting each path
        for(auto pair: mp2) {
            int ballid = pair.first;
            int shotcount  = ballids[ballid];
            int curshots = shotcount*2 +1; //add 1 for first iteration
            vector<vector<int>> paths = pair.second;
            graph[sourceid][count].cap=1;
            newToOldId[count] = ballid;
            ballIds.push_back(count);
            oldToNewId[ballid] = count++;
            graph[count-1][count].cap = 1;
            //perhaps this should be a map instead of vector
            graph[count-1][count].allowedshots.push_back(make_pair(shotcount, curshots--));
            int resetsc = shotcount;
            int resetcur = curshots;
            int balloutid = count++;
    
            for(int i=0; i<paths.size(); i++) {
                auto path = paths[i];
                shotcount  = resetsc;
                curshots = resetcur;
                int previd = balloutid;
                for(auto curId : path) {
                    if(curId ==ballid) {
                        continue;
                    }
                    int nid;
                    //Check if already added or not
                    if(oldToNewId.count(curId)==1) {
                        nid = oldToNewId[curId];
                        for(auto pair:pathsUsingId[nid] ) {
                            mp3[pair][pairToId[make_pair(ballid,i)]] = 1;
                            mp3[make_pair(ballid,i)][pairToId[pair]] = 1;
                        }
                        pathsUsingId[nid].push_back(make_pair(ballid, i));
                    }
                    else {
                        nid = count;
                        newToOldId[count] = curId;
                        oldToNewId[curId] = count++;
                        graph[nid][nid+1].cap=1;
                        count++;
                        vector<std::pair<int,int>> v;
                        v.push_back(make_pair(ballid,i));
                        pathsUsingId[nid] = v;
                    }
                    
                    
                    graph[previd][nid].cap = 1;
                    
                    if(curshots==0) {
                        shotcount--;
                        curshots = 2*shotcount;
                    }
                    graph[previd][nid].allowedshots.push_back(make_pair(shotcount, curshots--));
                    
                    graph[nid][nid+1].allowedshots.push_back(make_pair(shotcount, curshots--));;
                    
                    previd = nid+1;
                }
                
            }
        }
        
        //map ballids to original id
        int ballcount = ballIds.size();
        map<int,int> ballmap;
        map<int,int> rballmap;
        for(int i=0; i<ballIds.size(); i++) {
            ballmap[newToOldId[ballIds[i]]] = i;
            rballmap[i]=newToOldId[ballIds[i]];
        }
    
    	//find which paths are usable in a potential solution
    	//by checking if that path is compatible with at least 1 path
    	//for every other ball 
        map<int, vector<int> > winningpaths;
        vector<int> pathcompat(pcount, 1);
        for(auto entry: mp3) {
            auto pair  =  entry.first;
            vector<int> compatiblePaths = entry.second;
            int ballCompat[ballcount];
            memset(ballCompat, 0, sizeof(ballCompat));
            int c_count = 0;
            for(int i=0; i<compatiblePaths.size(); i++) {
                std::pair<int,int> p = idToPair[i];
                if(compatiblePaths[i]==0 && ballCompat[ballmap[p.first]]==0) {
                    ballCompat[ballmap[p.first]] = 1;
                    c_count++;
                }
            }
            if(c_count==ballcount) {  //found a path that is compatible with all other balls
                //need to find N vectors that share the same N compatible paths
                winningpaths[pairToId[pair]] = compatiblePaths;
            }
            else {
                winningpaths[pairToId[pair]] = vector<int>();
            }
        }
        
        vector<vector<int>> paths;
    
        //Step 4: Attempt all possible combinations of paths to find a solution
    	//the process is made much quicker since we already know which paths
    	//are compatible with each other
    	
        int remainingpaths = ballcount;
        int ccount = 0;
        int last = 0;
        vector<int> ballPid;
        vector<int> usedholes;
        vector<pair<int,int>> revert;
        for(int i=0; i<=ballcount; i++) {
            int ballid = rballmap[i];
            if(ccount==remainingpaths) {
                for(int k=0; k<ballPid.size(); k++) {
                    paths.push_back(mp2[rballmap[k]][ballPid[k]]);
                }
                break;
            }
            vector<vector<int>> bpaths = mp2[ballid];
            int j = last;
            for(; j<bpaths.size(); j++) {
                bool compat = true;
                int hole= bpaths[j].back();
                int id = pairToId[make_pair(rballmap[i],j)];
                if(winningpaths[id].size()==0)
                    continue;
                if(find(usedholes.begin(), usedholes.end(), hole)!=usedholes.end()) {
                    continue;
                }
                else {
                    int c=0;
                    for(auto k: ballPid) {
                        int nid = pairToId[make_pair(rballmap[c++], k)];
                        if(winningpaths[id][nid]!=0) {
                            compat=false;
                            break;
                        }
                    }
                    
                    if(compat==true) {
                        last=0;
                        ballPid.push_back(j);
                        usedholes.push_back(hole);
                        revert.push_back(make_pair(rballmap[i], j));
                        ccount++;
                        break;
                    }
                }
            }
            if(j==bpaths.size()) {
                pair<int,int> pare = revert.back();
                last = pare.second+1;
                revert.pop_back();
                ballPid.pop_back();
                usedholes.pop_back();
                i-=2;
                ccount--;
            }
        }
    
    	//Step 5: put the solution in the required format and print it out
        
        char outputData[height][width];
        memset(outputData, '.', height*width);
        for(auto path: paths) {
            if(DEBUG && DEBUGEACHPATH) {
                for(int i=0; i<height; i++) {
                    for(int j=0; j<width; j++) {
                        cout << outputData[i][j];
                    }
                    cout << endl;
                }
                cout <<endl;
            }
            assert(path.size() >= 2);
            
            int previd = path[0]; //start from ballid
            for(int i=1; i<path.size(); i++) {
                int prevy = (previd)/width;
                int prevx = (previd)%width;
                
                int id = path[i];
                int y =(id)/width;
                int x = (id)%width;
                
                
                if(y>prevy) { //south
                    outputData[prevy][prevx] = 'v';
                }
                else if(y<prevy) { //NORTH
                    outputData[prevy][prevx] = '^';
                }
                else if(x>prevx) { //east
                    outputData[prevy][prevx] = '>';
                }
                else if(x<prevx) { //west
                    outputData[prevy][prevx] = '<';
                }
                
                previd = id;
            }
        }
        
        for(int i=0; i<height; i++) {
            for(int j=0; j<width; j++) {
                cout << outputData[i][j];
            }
            cout << endl;
        }
    }
    void FindPaths(int shotcount, int id, map<int,int> parent, enum Direction incomingDir, int prevId = -1) {
	int y = id/width;
	    int x = id %width;
	    if(inputData[y][x] == 'H') {
	        parent[id] = prevId;
	        ballPaths.push_back(make_pair(id, parent));
	        return;
	    }
	    if(shotcount==0) {
	        return;
	    }
	    if(parent.count(id)==1) {
	        return;
	    }
	    int newid = -1;
	    if(y-shotcount>=0) { //North
	        if(incomingDir!=S) {
	            char c =inputData[y-shotcount][x];
	            if(c=='.' || c=='H') {
	                parent[id] = prevId;
	                newid = (y-shotcount)*width + x;
	                FindPaths(shotcount-1, newid, parent, N, id);
	                parent.erase(id);
	            }
	        }
	    }
	    if(y+shotcount<height) { //south;
	        if(incomingDir!=N) {
	            char c =inputData[y+shotcount][x];
	            if(c=='.' || c=='H') {
	                parent[id] = prevId;
	                newid = (y+shotcount)*width + x;
	                FindPaths(shotcount-1, newid, parent, S, id);
	                parent.erase(id);
	            }
	        }
	    }
	    if(x-shotcount>=0) {   //west
	        if(incomingDir!=E) {
	            char c =inputData[y][x-shotcount];
	            if(c=='.' || c=='H') {
	                parent[id] = prevId;
	                newid = (y)*width + x-shotcount;
	                FindPaths(shotcount-1, newid, parent, W, id);
	                parent.erase(id);
	            }
	        }
	        
	    }
	    if(x+shotcount<width) { //east
	        if(incomingDir!=W) {
	            char c =inputData[y][x+shotcount];
	            if(c=='.' || c=='H') {
	                parent[id] = prevId;
	                newid = (y)*width + x+shotcount;
	                FindPaths(shotcount-1, newid, parent, E, id);
	                parent.erase(id);
	            }
	        }
	        
	    }    
    }    
};


int main(int argc, const char * argv[]) {
    //setup and parse input
    int width;
    int height;
    cin >> width >> height; cin.ignore();
    string tmp[height];
    for (int i = 0; i < height; i++) {
        string row;
        cin >> row; cin.ignore();
        tmp[i]=row;
    }
    
    //create gridgraph class using input data
    
    GridProblem gp(height,width, tmp);
    //solution is printed automatically
    return 0;
}

