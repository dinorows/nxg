from flask import Flask, request, jsonify, render_template
import requests
import json as j
import networkx as nx
import math as m
from itertools import product
from random import choice, sample
import sys 
import time
import datetime

# neo/CYPHER
from py2neo import Graph, Node, Relationship

# janus/GREMLIN
from gremlin_python import statics
from gremlin_python.structure.graph import Graph as jGraph
from gremlin_python.process.graph_traversal import __
from gremlin_python.driver.driver_remote_connection import DriverRemoteConnection


### This module creates a local shard and exposes a BFS capability on it (CLIENT role).
### It also allows the caller to create a fleet of local shards and run a DBFS on them
### (SERVER role). It also allows the caller to create a fleet of remote shards and run
### a DBFS on them (MASTER-SERVER role). MIT license, dino@mitre.org 2020.
###
### The graph shard is based on networkx, but was extended to neo4j and janusgraph by
### cloning the networkx shards. Similar cloning can be undertaken for any other graph
### engine (e.g. redisgraph), specifically any containerized graph engine. 
### The shards are based on docker containers, but could be run as a kubernetes 
### cluster of pods. 
###
### This effort showcases that most of the DBFS effort is in the overhead communicating 
### between shards (so called "cross-cuts"), so that when sharding is required due to the
### size of the graph, it makes no difference whatsoever which graph engine one picks for 
### one's shards wrt. performance. It's just a matter of which API and graph engine DSL is
### more convenient.
###
### This effort also compares BFS performance between Neo and Janus (i.e. CYPHER vs. GREMLIN).
### However, because BFS is still an active area of research for both of these graph engines,
### I had to write my own vanilla BFS, which is highly unoptimized, and so it's a first cut
### benchmark. I believe a more serious effort is due to better benchmark CYPHER vs. GREMLIN.
###
### My personal experience has been that both of these DSLs are very advanced in their features,
### but GREMLIN inherits a bit of the traditional Apache complexity and overall laziness in
### developing specialized language extensions. So it works very well in groovy, the de-facto
### language for Apache TinkerPop, but it lacks specialized primitives in say, python. If all
### the user wants is a command console, I would say both languages are equally capable albeit
### GREMLIN is more complex. If the user wants language extensions, I would say CYPHER is more
### capable.
###
### General usage:
###
### Running as a local client (create a single networkX local shard):
### http://localhost:5000/testHealth
### http://localhost:5000/create-graph-shard?id=0&nodes=200&edges=0.08
### http://localhost:5000/edges?id=0
### http://localhost:5000/most-distant-internal-nodes?id=0&how-many=16
### http://localhost:5000/add-edge-external?info=197,30,0.5,0.5,1,10,198,31,0.6,0.6,2,11,199,32,0.7,0.7,3,12
### http://localhost:5000/nodes-with-attribute?id=0&attribute=remote
### http://localhost:5000/bfs-trees-with-remote-nodes-from-center-node
### http://localhost:5000/bfs-trees-with-remote-nodes?sources=6,9,131,44,79
### -phost:container
### docker run -p7474:7474 -p7687:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -it -p 8182:8182 janusgraph/janusgraph
### http://localhost:5000/clone-shard-to-neo?neo-ip=192.168.99.100&neo-port=7474&shard=0&verbose=1
### http://localhost:5000/bfs-trees-with-remote-nodes-neo?neo-ip=192.168.99.100&neo-port=7474&sources=6,9,131,44,79&verbose=1
### http://localhost:5000/clone-shard-to-janus?janus-ip=192.168.99.100&janus-port=8182&shard=0&verbose=1
### http://localhost:5000/bfs-trees-with-remote-nodes-janus?janus-ip=192.168.99.100&janus-port=8182&sources=6,9,131,44,79&verbose=1
###
###
### Containerization:
### start docker toolbox, docker-machine ip
### docker login -u=dinorows -p=<my-DOCKER-PASSWORD>
### docker build -t dinorows/nxg .
### docker push dinorows/nxg
### docker pull dinorows/nxg
### Run container, listen on port 5050 on host, 5000 in container:
### docker run -d -p 5050:5000 dinorows/nxg
### For easier debugging (can see print commands):
### docker run --rm -p 5050:5000 dinorows/nxg
###
###
### Running as a CLIENT demo, containerized (create a single networkX graph shard on a container):
### docker run --rm -p 5049:5000 dinorows/nxg
### http://192.168.99.100:5049/testHealth
### http://192.168.99.100:5049/create-graph-shard?id=0&nodes=200&edges=0.08
### http://192.168.99.100:5049/edges?id=0
### http://192.168.99.100:5049/most-distant-internal-nodes?id=0&how-many=16
### http://192.168.99.100:5049/add-edge-external?info=197,30,0.5,0.5,1,10,198,31,0.6,0.6,2,11,199,32,0.7,0.7,3,12
### http://192.168.99.100:5049/nodes-with-attribute?id=0&attribute=remote
### http://192.168.99.100:5049/bfs-trees-with-remote-nodes-from-center-node
### http://192.168.99.100:5049/bfs-trees-with-remote-nodes?sources=6,9,131,44,79
### http://192.168.99.100:5049/clone-shard-to-neo?neo-ip=192.168.99.100&neo-port=7474&shard=0&verbose=1
### http://192.168.99.100:5049/bfs-trees-with-remote-nodes-neo?neo-ip=192.168.99.100&neo-port=7474&sources=6,9,131,44,79&verbose=1
### http://192.168.99.100:5049/clone-shard-to-janus?janus-ip=192.168.99.100&janus-port=8182&shard=0&verbose=1
### http://192.168.99.100:5049/bfs-trees-with-remote-nodes-janus?janus-ip=192.168.99.100&janus-port=8182&sources=6,9,131,44,79&verbose=1
###
###
### Running as a SERVER demo (create a local multi-shard networkX graph and do a DBFS):
### http://localhost:5000/role
### http://localhost:5000/create-shards?shards=4&nodes=200&edges=0.08&farnodes=16
### http://localhost:5000/do-dbfs?shard=0&verbose=0
### http://localhost:5000/do-dbfs?shard=1&verbose=0
### http://localhost:5000/do-dbfs?shard=2&verbose=0
### http://localhost:5000/do-dbfs?shard=3&verbose=0
### < 0.01 second
### PICK TO BEGIN THE DBFS ON THE SHARD THAT EXHIBITS CROSS-CUTS ABOVE
### May have to run:
### docker system prune --volumes
### ESPECIALLY IF YOU GET THE FOLLOWING RUNTIME ERROR:
### gremlin_python.driver.protocol.GremlinServerError: 499: The traversal source [g] for alias [g] is not configured on the server.
### docker run --rm -p8182:8182 janusgraph/janusgraph:latest
### docker run --rm -p8183:8182 janusgraph/janusgraph:latest
### docker run --rm -p8184:8182 janusgraph/janusgraph:latest
### docker run --rm -p8185:8182 janusgraph/janusgraph:latest
### note -d and -it options, instead of --rm which allows me to stop container with CTRL-Z
### http://localhost:5000/clone-shards-to-janus?janus-ip=192.168.99.100&janus-start-port=8182&how-many-shards=4&verbose=0
### http://localhost:5000/do-ddbfs-on-janus-shards?shard=0&verbose=0
### ~30 seconds
### docker run -p7474:7474 -p7687:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -p7475:7474 -p7688:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -p7476:7474 -p7689:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -p7477:7474 -p7690:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### note -d option.
### http://localhost:5000/clone-shards-to-neo?neo-ip=192.168.99.100&neo-start-port=7474&how-many-shards=4&verbose=0
### http://localhost:5000/do-ddbfs-on-neo-shards?shard=0&verbose=0
### ~25 seconds
###
###
### Running as a SERVER demo, containerized (create a local sharded networkX graph in a container and do a DBFS):
### docker run -d -p7474:7474 -p7687:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -d -p7475:7474 -p7688:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -d -p7476:7474 -p7689:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run -d -p7477:7474 -p7690:7687 --env NEO4J_AUTH=neo4j/test neo4j:latest
### docker run --rm -p 5050:5000 dinorows/nxg to see calls
### docker run --it -p 5050:5000 dinorows/nxg to see verbose status
### http://192.168.99.100:5050/create-shards?shards=4&nodes=200&edges=0.08&farnodes=16
### http://192.168.99.100:5050/do-dbfs?shard=0&verbose=0
### ~0.01 second
### http://192.168.99.100:5050/clone-shards-to-neo?neo-ip=192.168.99.100&neo-start-port=7474&how-many-shards=4&verbose=0
### http://192.168.99.100:5050/do-ddbfs-on-neo-shards?shard=0&verbose=0
### ~33 seconds
###
###
### Running as a MASTER-SERVER demo (create a multi-container sharded graph and do a DBFS):
### First, create 4 containers:
### docker run -d -p 5050:5000 dinorows/nxg
### docker run -d -p 5051:5000 dinorows/nxg
### docker run -d -p 5052:5000 dinorows/nxg
### docker run -d -p 5053:5000 dinorows/nxg
### note -=rm option instead of -d for better debugging!
### docker container ls
### Then run a local MASTER-SERVER, create shards on the containers, then do a DBFS
### python nx_g_shard.py
### http://localhost:5000/role
### http://localhost:5000/create-remote-shards?shards=4&nodes=200&edges=0.08&farnodes=16&shards-ip=192.168.99.100&shard-ports-start-at=5050&verbose=0
### http://localhost:5000/do-ddbfs?shard=0&verbose=0
### ~.1 second for shard exhibiting cross-cuts.
###
###
### NOTE: LIMITS ON THE NUMBER OF CONTAINERS
### Docker creates or uses a number of resources to run a container, on top of what you run inside the container.
###
### Attaches a virtual ethernet adaptor to the docker0 bridge (1023 max per bridge)
### Mounts an AUFS and shm file system (1048576 mounts max per fs type)
### Create's an AUFS layer on top of the image (127 layers max)
### Forks 1 extra docker-containerd-shim management process (~3MB per container on avg and sysctl kernel.pid_max)
### Docker API/daemon internal data to manage container. (~400k per container)
### Creates kernel cgroups and name spaces
### Opens file descriptors (~15 + 1 per running container at startup. ulimit -n and sysctl fs.file-max )
###
### Docker options
### Port mapping -p will run a extra process per port number on the host (~4.5MB per port on avg pre 1.12, ~300k per port > 1.12 and also sysctl kernel.pid_max)
### --net=none and --net=host would remove the networking overheads.
###
### Container services
### The overall limits will normally be decided by what you run inside the containers rather than dockers overhead 
### (unless you are doing something esoteric, like testing how many containers you can run :)
### If you are running apps in a virtual machine (node,ruby,python,java) memory usage is likely to become your main issue.
### IO across a 1000 processes would cause a lot of IO contention.
### 1000 processes trying to run at the same time would cause a lot of context switching (see vm apps above for garbage collection)
### If you create network connections from a 1000 containers the hosts network layer will get a workout.
### It's not much different to tuning a linux host to run a 1000 processes, just some additional Docker overheads to include.
###
### Example
### 1023 Docker busybox images running nc -l -p 80 -e echo host uses up about 1GB of kernel memory and 3.5GB of system memory.
### 1023 plain nc -l -p 80 -e echo host processes running on a host uses about 75MB of kernel memory and 125MB of system memory
### Starting 1023 containers serially took ~8 minutes.
### Killing 1023 containers serially took ~6 minutes
###
### From a post on the mailing list, at about 1000 containers you start running into Linux networking issues.
### The reason is: This is the kernel, specifically net/bridge/br_private.h BR_PORT_BITS cannot be extended because 
### of spanning tree requirements.


#############################################################
### Shard class, remote: The external surface for a remote
### fleet of shards. Each remote shard is of class dShard.
###
### We are a MASTER SERVER. The calling client is instructing
### us to create remote shards, inquire upon the remote 
### shards' distant nodes, add external edges, and do a BFS  
### on any remote shards. 
###
### We do not create any local shards. All requests go to
### remote shards. 
###
### The default shard is a networkX graph shard. There is
### another class below for a neo4j shard, and another one
### yet for a janus shard.
#############################################################
def myints(seq):
    return list(map(lambda e: int(e), seq))
def myjson(j):
    # replace () and {} with [], and wrap with [] if not already, as otherwise invalid JSON
    t = j.replace('(', '[')
    t = t.replace(')', ']')
    t = t.replace('{', '[')
    t = t.replace('}', ']')
    if not '[' == t[0]:
        t = '[' + t + ']'
    return t
		
class dShard:
    # The constructor stores ip and port for the remote node,
    # creates a remote shard, and grows it. All other methods 
    # reference the ip and port saved in the dShard object to
    # make a remote call
    def __init__(self, guid, ip, port, nodes, p, verbose):
        self.guid_internal = guid
        self.ip = ip
        self.port = port
		
        # e.g. http://192.168.99.100:5060/create-graph-shard?id=0&nodes=200&edges=0.08
        response = requests.get(
          "http://" + ip + ":" + str(port) + 
          "/create-graph-shard?id=" + str(guid) + 
          "&nodes=" + str(nodes) +
          "&edges=" + str(p)
        )
        responsetext = myjson(response.text)
		
        if verbose:
            if total_recall:
                sys.stderr.write("Created shard with edges and center: " + responsetext + " at port " + str(port))
            else:
                print("Created shard with edges and center: " + responsetext + " at port " + str(port))
				
        currdt = datetime.datetime.now()
        self.when = "Remote shard " + str(guid) + " with number of edges and center node: " + responsetext + ", created " + currdt.strftime("%Y-%m-%d %H:%M:%S")

        #print("$$$$$$$$$$$$$ ~dk debugging:")
        #print(responsetext)

        edges_and_center = j.loads(responsetext)
        edges_and_center = list(map(lambda e: int(e), edges_and_center))
		
        #print(str(int(edges_and_center[1])))

        self.center = int(edges_and_center[1])

    def guid(self):
        return self.guid_internal

    def when(self):
        return self.when
        
    def nodes(self):
        # e.g. http://192.168.99.100:5060/nodes
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/nodes"
        )
        return response.text;

    def edges(self):
        # e.g. http://192.168.99.100:5060/edges
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/edges"
        )
        return response.text;
		
    def node_center(self):
        # e.g. http://192.168.99.100:5060/node-center
        #response = requests.get(
        #  "http://" + self.ip + ":" + str(self.port) + 
        #  "/node-center"
        #)
        #return response.text;
        return self.center, 0.0 #the second number should be the distance which we don't really care about
		
    def most_distant_internal_nodes(self, how_many):
        try:
            if (len(self.far_nodes) == how_many):
                return self.far_nodes
            else:
                return self.most_distant_internal_nodes_call(how_many)
        except:
            return self.most_distant_internal_nodes_call(how_many)

    def most_distant_internal_nodes_call(self, how_many):

        #print("@@@@@@@@ ~dk debugging:")
        #print("http://" + self.ip + ":" + str(self.port) + 
        #  "/most-distant-internal-nodes?how-many=" + str(how_many))

        # Note that remote nodes are created at id 0 in MASTER_SERVER mode.
        # i.e. http://192.168.99.100:5060/most-distant-internal-nodes?id=0&how-many=16
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/most-distant-internal-nodes?id=0&how-many=" + str(how_many)
        )
		
        responsetext = response.text
        #print("&&&&&&&&& ~dk debugging:")
        #print(responsetext)
        #print(j.loads(myjson(responsetext)))

        # [[44,0.35],[57,0.35],[46,0.36],[95,0.36],[29,0.37],[72,0.38],[183,0.38],[158,0.39],[93,0.4],
		# [105,0.4],[117,0.4],[136,0.41],[189,0.42],[38,0.44],[172,0.44],[52,0.47]]
        far_nodes_and_distance = j.loads(myjson(responsetext))
        # keep the distance!		
        #far_nodes = [n for n,d in far_nodes_and_distance]
        #self.far_nodes = far_nodes
        self.far_nodes = far_nodes_and_distance

        #if global_verbose:
        #    if total_recall:
        #        sys.stderr.write("far nodes: " + str(self.far_nodes))
        #    else:
        #        print("far nodes: " + str(self.far_nodes))

        return self.far_nodes

    # Note that info is a flattened list of lists without leading and trailing parenses.
    #input: [(ni,ne,x,y,shard,d), (), ..]
    def add_edge_external(self, nodes_and_pos):

        # query-parametrize nodes_and_pos:
        snodes_and_pos = str(nodes_and_pos).replace('[', '').replace(']', '').replace('(', '').replace(')', '').replace(' ','')

        # i.e. http://192.168.99.100:5060/add-edge-external?info=ni0,ne0,x0,y0,shard0,d0,ni1,ne1,x1,y1,shard1,d1,ni2,ne2,x2,y2,shard2,d2,...
        # i.e. http://192.168.99.100:5060/add-edge-external?info=197,30,0.5,0.5,1,10,198,31,0.6,0.6,2,11,199,32,0.7,0.7,3,12
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/add-edge-external?info=" + str(snodes_and_pos)
        )
        return response.text;

    # Note that nodes is a list without leading and trailing parenses.	
    def bfs_trees_with_remote_nodes(self, nodes):
	
        #@@@@@@
        # We are going to assume that the remote shard has id 0!
        shard_id = 0

        #@@@@@@
		# since this MASTER-SERVER call has the same surface API as a SERVER call, I
        # need to unwrap the list of nodes so I can pass them as a query parameter!
        snodes = str(nodes).replace('{', '').replace('}', '').replace(' ','')
		
        # i.e. http://192.168.99.100:5060/bfs-trees-with-remote-nodes?id=0&sources=6,9,131,44,79
        #print("Calling..." + "http://" + self.ip + ":" + str(self.port) + 
        #  "/bfs-trees-with-remote-nodes?id=0&sources=" + snodes)
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/bfs-trees-with-remote-nodes?id=" + str(shard_id) + "&sources=" + snodes
        )
        responsetext = response.text
        #print(responsetext)
        responsetext = myjson(responsetext)
        #print(responsetext)
        return j.loads(responsetext);
		
    def bfs_trees_with_remote_nodes_from_center_node(self):
        #@@@@@@
        # We are going to assume that the remote shard has id 0!
        shard_id = 0
		
        # i.e. http://192.168.99.100:5060/bfs-trees-with-remote-nodes-from-center-node?id=0
        response = requests.get(
          "http://" + self.ip + ":" + str(self.port) + 
          "/bfs-trees-with-remote-nodes-from-center-node?id=" + str(shard_id)
        )
        return j.loads(myjson(response.text));


# This class is a clone of a local Shard on a neo4j container. Pretty thin!
class dNeoShard:
    # The constructor stores ip and port for the neo4j container,
    # and clones a networkX shard.
    def __init__(self, guid, center, ip, port, verbose):
        self.guid_internal = guid
        self.center = center
        self.ip = ip
        self.port = port
        self.verbose = verbose

    def node_center(self):
        return self.center, 0.0 #the second number should be the distance which we don't really care about

    # Note that nodes is a list without leading and trailing parenses.	
    def bfs_trees_with_remote_nodes(self, nodes):

        #@@@@@@
		# since this MASTER-SERVER call has the same surface API as a SERVER call, I
        # need to unwrap the list of nodes so I can pass them as a query parameter!
        #sources = str(nodes).replace('{', '').replace('}', '').replace(' ','')
        #sources = j.loads(myjson(nodes))
		
        if self.verbose:
            print("neo bfs @ ", self.ip, self.port, nodes)		
        r = bfs_trees_with_remote_nodes_neo_internal(self.ip, self.port, nodes, self.verbose)
        if self.verbose:
            print(r)
        return j.loads(r)


# This class is a clones of a Shard on a janusgraph container. Pretty thin!
class dJanusShard:
    # The constructor stores ip and port for the janus container,
    # and clones a networkX shard.
    def __init__(self, guid, center, ip, port, verbose):
        self.guid_internal = guid
        self.center = center
        self.ip = ip
        self.port = port
        self.verbose = verbose

    def node_center(self):
        return self.center, 0.0 #the second number should be the distance which we don't really care about
		
    # Note that nodes is a list without leading and trailing parenses.	
    def bfs_trees_with_remote_nodes(self, nodes):

        #@@@@@@
		# since this MASTER-SERVER call has the same surface API as a SERVER call, I
        # need to unwrap the list of nodes so I can pass them as a query parameter!
        #sources = str(nodes).replace('{', '').replace('}', '').replace(' ','')

        if self.verbose:
            print("janus bfs @ ", self.ip, self.port, nodes)		
        r = bfs_trees_with_remote_nodes_janus_internal(self.ip, self.port, nodes, self.verbose)
        if self.verbose:
            print(r)
        return j.loads(r)


################################################
### Shard class, local.
### We are a shard CLIENT or local shards SERVER
################################################
class Shard:
    def __init__(self, guid):
        self.guid_internal = guid

    def grow_graph(self, guid, nodes, p):
        self.guid = guid
        self.numnodes = nodes
        self.probaedge = p
        self.g = nx.random_geometric_graph(nodes, p)
        self.origpos = nx.get_node_attributes(self.g, 'pos')
        
        for node_id in self.g.nodes():
            self.g.nodes[node_id]['remote'] = None
        for edge_id in self.g.edges():
            self.g.edges[edge_id]['remote'] = None

        # returns the number of edges created and the node center					
        return self.g.number_of_edges(), self.node_center()[0]

    # temporary: For debugging!
    def graph(self):
        return self.g
    
    def guid(self):
        return self.guid
        
    def nodes(self):
        return list(self.g.nodes)
    
    def edges(self):
        return list(self.g.edges)

    # ~dk networkX has an issue with this API: 
    # It produces an exception TypeError: 'int' object is not callable
    # 4-23-2020: I think i fixed it by removing trailing (): return self.g.number_of_nodes()
    def numnodes(self):
        return self.g.number_of_nodes
    
    def numedges(self):
        return self.g.number_of_edges()

    def node_attribute(self, node_id, attribute):
        try:
            return self.g.nodes[node_id][attribute]
        except:
            return "undefined!"

    def edge_attribute(self, edge_id, attribute):
        try:
            return self.g.edges[edge_id][attribute]
        except:
            return "undefined!"

    def nodes_with_attribute(self, attribute):
        try:
            an_attempt = self.g.nodes[0][attribute]
        except:
            return "The attribute " + attribute + " is not defined for all nodes!"

        return [(node_id, self.g.nodes[node_id][attribute]) for node_id in self.g.nodes]

    def edges_with_attribute(self, attribute):
        try:
            an_attempt = self.g.edges[0][attribute]
        except:
            return "The attribute " + attribute + " is not defined for all edges!"

        return [(edge_id, self.g.edges[edge_id][attribute]) for edge_id in self.g.edges]

    def nodes_with_attributes(self):
        return [(node_id, self.g.nodes[node_id]) for node_id in self.g.nodes]

    def edges_with_attributes(self):
        return [(edge_id, self.g.edges[edge_id]) for edge_id in self.g.edges]
		
    #input: [(ni,ne,x,y,shard,d), (), ..]
    def add_edge_external(self, nodes_and_pos):
        #print('-- shard ' + str(self.guid) + ': number of nodes ' + str(self.g.number_of_nodes()))
        num_new_nodes = len(nodes_and_pos)
        new_node_index = self.g.number_of_nodes()
        #print(new_node_index)
        for _ in nodes_and_pos:
            (ni, ne, x, y, shard, d) = _
            #print(ni, ne, x, y, shard, d)
            #print('-- shard ' + str(self.guid) + ': adding new node ' + str(new_node_index))
            self.g.add_node(new_node_index)
            self.g.nodes[new_node_index]['remote'] = shard, ne, d
            self.g.nodes[new_node_index]['pos'] = x, y
            self.g.add_edge(ni, new_node_index) 
            #2do: add edge 'remote' attribute
            new_node_index +=1
        return "added " + str(num_new_nodes) + " new nodes representing copies of nodes on other shards, for a total of " + str(new_node_index) + " nodes."
    
    # returns all nodes of the graph that are copies of nodes that live on other shards
    # In other words, these "remote" nodes don't actually belong to this graph. They
    # are only used to create external edges
    def external_nodes(self):
        exnodes = []
        for node_id in self.g.nodes():
            label = self.g.nodes[node_id]['remote']
            if label is not None:
                exnodes.append((node_id, label))
        return exnodes
    
    # used to find the center of a geographic graph
    def node_center(self):
        # find node near center (0.5,0.5)
        dmin=1
        ncenter=0
        pos=nx.get_node_attributes(self.g,'pos')
        for n in pos:
            x,y=pos[n]
            d=(x-0.5)**2+(y-0.5)**2
            if d<dmin:
                ncenter=n
                dmin=d
        return ncenter, dmin
    
    # used to compute distance from graph center
    def nodes_distance_from_center(self):
        distances = []
        pos=nx.get_node_attributes(self.g,'pos')
        for n in pos:
            x,y=pos[n]
            d=(x-0.5)**2+(y-0.5)**2
            distances.append((n,d))
        return distances
    
    # used to locate the most far-away-from-center nodes in the graph.
    # These can then be connected to remote nodes on other graph shards
    def most_distant_internal_nodes(self, p=1, num=0):
        distances = []
        for n in self.origpos:
            x,y=self.origpos[n]
            d=(x-0.5)**2+(y-0.5)**2
            distances.append((n,round(d,2)))
        how_many = 0
        if p > 1: p = 1
        if 0 < num: 
            how_many = num
        else:
            how_many = int(self.numnodes * p)
        return(sorted(distances, key = lambda x: x[1])[-how_many:])
    
    def bfs_edges(self, source):
        return list(nx.bfs_edges(self.g, source))
    
    def bfs_tree(self, source):
        return list(nx.bfs_tree(self.g, source))
    
    def shortest_path(self, source, target):
        return nx.shortest_path(self.g, source=source, target=target)
    
    # does an internal BFS and returns ONLY external nodes that NEED TO BE traversed, since source node
    def bfs_remote_nodes_to_explore(self, source):
        exnodes = []
        tree = list(nx.bfs_tree(self.g, source))
        for n in tree:
            label = self.g.nodes[n]['remote']
            if label is not None:
                exnodes.append((n, label))
        return exnodes
    
    # returns internal nodes traversed, as well as external nodes that NEED TO BE traversed, single source node
    # DEPRECATED in favor of bfs_trees_with_remote_nodes() that takes in a list of starting nodes.
    def bfs_tree_with_remote_nodes(self, source):
        innodes = set()
        exnodes = []
        tree = list(nx.bfs_tree(self.g, source))
        for n in tree:
            label = self.g.nodes[n]['remote']
            if label is not None:
                exnodes.append((n, label))
            else:
                innodes.add(n)
        return innodes, exnodes
    
	# if i'm a SERVER or MASTER-SERVER, I have shards.
	# But if I'm a CLIENT, I don't know about any shards.
	# However, I'm returning external nodes, which reference
	# shards, so I need to rewrite the method below so that it
	# *does not* require knowledge of number of shards! I'm going
	# to use a dictionary structure instead!
    def bfs_trees_with_remote_nodes(self, sources):

        #print(sources)	
        innodes = set()
        extnodes = dict()
        for source in sources:
            tree = list(nx.bfs_tree(self.g, source))
            for n in tree:
                label = self.g.nodes[n]['remote']
                if label is not None:  #shard, ne, d
                    shard, extnode, distance = label
					
                    if shard not in extnodes:
                        extnodes[shard] = {extnode}
                    else:
                        extnodes[shard].add(extnode)

                else:
                    innodes.add(n)

        #print(innodes)
        #print(extnodes)
        extshards_and_nodes = [(k,list(v)) for k,v in extnodes.items()]
        #print(extshards_and_nodes)
        #print(list((list(innodes), extshards_and_nodes)))
        return list((list(innodes), extshards_and_nodes))

	# deprecated in favor of above
	
    # same as bfs_tree_with_remote_nodes() (singular tree), but 
	# can submit multiple sources to BFS with and external nodes 
	# to be investigated are grouped by shard and returned. 
    # input format: sources is an iterable, either list or set
    # return format: {}, [(p, {}), (q, {}), ..]
	
    # Update: converting set output to list, to be able to JSONify
    #def bfs_trees_with_remote_nodes(self, sources, numshards):
    def deprecated_bfs_trees_with_remote_nodes(self, sources):
	
        num_shards = nshards_as_list[0]
        innodes = set()
        extshards = []
        extnodes = [None]*num_shards
        for source in sources:
            tree = list(nx.bfs_tree(self.g, source))
            for n in tree:
                label = self.g.nodes[n]['remote']
                if label is not None:  #shard, ne, d
                    shard, extnode, distance = label
                    if shard not in extshards:
                        extshards.append(shard)
                    #print('*** ' + str(num_shards))
                    #print('*** ' + str(shard))
                    if extnodes[shard] is None:
                        extnodes[shard] = set()
                        extnodes[shard].add(extnode)
                    else:
                        extnodes[shard].add(extnode)
                else:
                    innodes.add(n)
                    
        extshards_and_nodes = []
        for i in range(0, num_shards):
            if i in extshards:
                extshards_and_nodes.append((i, list(extnodes[i])))
                
        return list(innodes), extshards_and_nodes


		
#################
### toroidal wrap
#################
def tw_tr(n):
    return range(0, n)

def tw_br(n):
    return range(n**2 - 1, n**2 - 1 - n, -1)

def tw_lc(n):
    return range(0, n**2 - 1, n)

def tw_rc(n):
    return range(n**2 - 1, 0, -n)

def tw_neigh(i, n):
    return (
        i-1 if i not in tw_lc(n) else i-1+n,
        i+1 if i not in tw_rc(n) else i+1-n,
        i-n if i not in tw_tr(n) else i-n+n**2,
        i+n if i not in tw_br(n) else i+n-n**2
    )

	
####################################
### distributed BFS on remote shards
####################################
def ddbfs(begin_shard, verbose=False):
    # The code is the same because
	# our shard list s consists of
	# dShard objects instead of
	# shard objects :-)
    return dbfs(begin_shard, verbose)

	
###################################
### distributed BFS on local shards
### see better dbfs() below!
###################################
def deprecated_buggy_dbfs(begin_shard, verbose=False):

    time_spent_inside_shards_in_seconds = 0.
    time_spent_outside_shards_in_seconds = 0.
	
    num_shards = nshards_as_list[0]
    cross_cuts_per_shard = [None]*num_shards
    traversed_nodes = [None]*num_shards
    shard_queue = []

    # start BFS at which shard, which nodes (note plural nodes now)?
    total_cross_cuts_required = 0
    begin_node = s[begin_shard].node_center()[0]
    shard_queue.append((begin_shard, {begin_node}))

    # add the cross-cut for shard 'begin_shard', the starting point of the BFS.
    # Note we don't add it to the total total_cross_cuts_required
    cross_cuts_per_shard[begin_shard] = 1

    # while there are shards (and nodes on those shards) remaining to visit
    #debugging_p = True
    start_o = time.time()
    while 0 < len(shard_queue):
    #while debugging_p:
        # pop first shard/nodes from the queue
        i, ns = shard_queue.pop(0)  #p, {}

        # traverse the shard and get internal nodes visited by the
        # BFS as well as external nodes and shards that need to be
        # visited
        if global_verbose:
            print("---> Traversing shard " + str(i) + ". Queue size: " + str(len(shard_queue)))
        if verbose:
            if traversed_nodes[i] is None: print("---> traversing shard " + str(i))
            if not traversed_nodes[i] is None: print("---> traversing shard " + str(i) + " again (" + str(cross_cuts_per_shard[i]) + ")!")
        start = time.time()
        #ins, exs = s[i].bfs_trees_with_remote_nodes(ns, num_shards)   #{}, [(p, {}), (q, {}), ..]
        ins, exs = s[i].bfs_trees_with_remote_nodes(ns)   #{}, [(p, {}), (q, {}), ..]
        end = time.time()
        time_spent_inside_shards_in_seconds += end - start
        time_spent_outside_shards_in_seconds -= end - start

        # debugging
        if verbose:
            print("   BFS: internal nodes traversed: " + str(ins))
            print("   BFS: Need to additionally traverse following shards and their nodes: " + str(exs))
            print("        On these shards, only the following new nodes need to be visited:")
            for ex in exs:
                shard, nodes = ex

                if traversed_nodes[shard] is None:
                    print("        On shard " + str(shard) +": Nodes " + str(nodes))
                else:
                    print("        On shard " + str(shard) +": Nodes " + str(set(nodes) - set(traversed_nodes[shard])))
            print("        ---------")


        # add internal nodes to the visited nodes per shard
        if traversed_nodes[i] is None:		
            traversed_nodes[i] = ins
        else:
            #print("      *** " + str(traversed_nodes[i]))
            #print("      *** " + str(ins))
            #traversed_nodes[i].update(ins)
            # ins is now a list, not a set
            
            # option 1
            #seen = set(traversed_nodes[i])
            #seen.update(ins)
            #traversed_nodes[i] = list(seen)
            
            # option 2
            for node_item in ins:
                if node_item not in traversed_nodes[i]:
                    traversed_nodes[i].append(node_item)
			

        # if an external node that needs to be traversed hasn't 
        # already been traversed, schedule it for traversal and
        # increment the number of cross-cuts if that node hadn't
        # been previously scheduled for traversal
        for ex in exs:      #[(p, {}), (q, {}), ..]
            (ss, nns) = ex  #(p, {})
            if traversed_nodes[ss] is None:
                # if the shard is not on the queue yet, we create a new queue
                # entry with all the nodes on that shard that need to be visited.
                # We increment cross-cuts.
                shard_queue.append((ss,nns))
                total_cross_cuts_required += 1
                cross_cuts_per_shard[ss] = 1 if cross_cuts_per_shard[ss] is None else cross_cuts_per_shard[ss] + 1
            else:
                # Shard ss is already spooled in the queue.
                # Find the queue entry and add the additional nodes to be visited.
                # Note no new cross-cuts required at all, piggy-backing on already scheduled ones
                for nn in nns:
                    # if nn is a node that has not been traversed on shard ss, add it to ss's queue entry
                    if nn not in traversed_nodes[ss]:
                        # note here if we have a lot of shards, don't iterate across the shard queue but find a
                        # better data structure to immediately locate this particular shard's place in the queue
                        ss_shard_spooled_p = False
                        for queue_index, shard_and_nodes in enumerate(shard_queue):
                            shard, nodes = shard_and_nodes
                            if shard == ss:
                                ss_shard_spooled_p = True
                                if nn not in nodes:  #nodes is a set, but I do touch the queue so avoid this unless necessary
                                    nodes.add(nn)
                                    shard_queue[queue_index] = (shard, nodes)

                        # the shard has not been spooled yet, or has been spooled and
                        # already traversed but the node nn has not been visited
                        if not ss_shard_spooled_p:
                            # need new entry in shard queue
                            never_visited_nodes_on_shard_ss = set()
                            never_visited_nodes_on_shard_ss.add(nn)
                            shard_queue.append((ss, never_visited_nodes_on_shard_ss))
                            total_cross_cuts_required += 1
                            cross_cuts_per_shard[ss] = 1 if cross_cuts_per_shard[ss] is None else cross_cuts_per_shard[ss] + 1


        # debugging
        if verbose:
            print("        shard queue = " + str(shard_queue))
            print()
            
            # If i don't do this I may exceed the allowed data rate and crash the hotebook!
            time.sleep(0.1)
            
        #debugging_p = False
        
    # num nodes visited
    num_nodes_visited = sum(
        [0 if traversed_nodes[i] == None else len(traversed_nodes[i]) for i in range(0,num_shards)]
    )
    
    end_o = time.time()
    time_spent_outside_shards_in_seconds += end_o - start_o	
    return total_cross_cuts_required, num_nodes_visited, time_spent_inside_shards_in_seconds, time_spent_outside_shards_in_seconds


# unfortunately, popitem() returns the *last* element in a dictionary
# faster than return list(mydictionary)[0]; return next(iter(mydictionary.keys())); return list(mydictionary.keys())[0];  
# for key in mydictionary.keys(): return key; for key, v in mydictionary.items(): return key
def firstkey(mydictionary):
    for key in mydictionary:
        return key
		
# 4/14/20: optimized using dict()
def dbfs(begin_shard, verbose=False):

    if not s:
        print("Whoah! Graph has not been initialized yet!")
        return 0,0,0,0

    time_spent_inside_shards_in_seconds = 0.
    time_spent_outside_shards_in_seconds = 0.

    cross_cuts_per_shard = dict()
    traversed_nodes = dict()
    shard_queue = dict()

    # start BFS at which shard, which nodes (note plural nodes bfs_trees_with_remote_nodes() API)?
    total_cross_cuts_required = 0
    begin_node = s[begin_shard].node_center()[0]
    shard_queue[begin_shard] = {begin_node} #(set with one element)

    # add the cross-cut for shard 'begin_shard', the starting point of the BFS.
    # Note we don't add it to the total total_cross_cuts_required
    cross_cuts_per_shard[begin_shard] = 1

    # while there are shards (and nodes on those shards) on the queue
	# Note: python 3.6 safeguards queue order (random beforehand)
    #debugging_p = True
    start_o = time.time()
    while 0 < len(shard_queue):
    #while debugging_p:
        # pop first shard/nodes from the queue
        i = firstkey(shard_queue)
        ns = shard_queue.pop(i)

        # traverse the shard and get internal nodes visited by the BFS 
		# as well as external nodes and shards that still need to be visited
        if global_verbose:
            print("---> Traversing shard " + str(i) + ". Queue size: " + str(len(shard_queue)))
        if verbose:
            if i in traversed_nodes: 
                print("---> traversing shard " + str(i) + " again (" + str(cross_cuts_per_shard[i]) + ")!")
            else:
                print("---> traversing shard " + str(i))

        start = time.time()
        #ins, exs = s[i].bfs_trees_with_remote_nodes(ns, num_shards)   #{}, [(p, {}), (q, {}), ..]
        ins, exs = s[i].bfs_trees_with_remote_nodes(ns)   #{}, [(p, {}), (q, {}), ..]
        end = time.time()
        time_spent_inside_shards_in_seconds += end - start
        time_spent_outside_shards_in_seconds -= end - start

        # debugging
        if verbose:
            print("   BFS: internal nodes traversed: " + str(ins))
            print("   BFS: Need to additionally traverse following shards and their nodes: " + str(exs))
            print("        On these shards, only the following new nodes need to be visited:")
            for ex in exs:
                shard, nodes = ex

                if shard in traversed_nodes:
                    print("        On shard " + str(shard) +": Nodes " + str(set(nodes) - traversed_nodes[shard]))
                else:
                    print("        On shard " + str(shard) +": Nodes " + str(nodes))
            print("        ---------")


        # Action 1: Add internal nodes to the visited nodes per shard
        if i in traversed_nodes:
            traversed_nodes[i].update(set(ins)) # automatically discards duplicates
        else:
            traversed_nodes[i] = set(ins)


        # Action 2: if an external node that needs to be traversed hasn't 
        # already been traversed, schedule it for traversal and
        # increment the number of cross-cuts if that node hadn't
        # already been previously scheduled for traversal
        for ex in exs:      #[(p, {}), (q, {}), ..]
            (ss, nns) = ex  #(p, {})
			
			# nodes that have not already been traversed:
            real_nns = set(nns) - traversed_nodes[ss] if ss in traversed_nodes else set(nns)

            # if non-empty
            if real_nns:
                if ss in shard_queue:

                    # Shard ss is already spooled in the queue.
                    # Find queue entry and add the additional nodes to be visited only if they have not already been visited
                    # Note no new cross-cuts required at all, piggy-backing on already scheduled ones!
                    shard_queue[ss].update(real_nns)

                else:

                    # need new entry in shard queue, need to increment cross-cuts
                    shard_queue[ss] = real_nns
                    total_cross_cuts_required += 1
                    cross_cuts_per_shard[ss] = cross_cuts_per_shard[ss] + 1 if ss in cross_cuts_per_shard else 1

        # debugging
        if verbose:
            print("        shard queue = " + str(shard_queue))
            print()
            
            # If i don't do this I may exceed the allowed data rate and crash the hotebook!
            time.sleep(0.1)
            
        #debugging_p = False
	
    if verbose:
        num_shards = nshards_as_list[0]
        for i in range(0, num_shards):
            if i not in traversed_nodes:
                print("        fyi, shard " + str(i) + " was never visited!")
				
    # num nodes visited
    num_nodes_visited = sum(
        [len(traversed_nodes[i]) for i in traversed_nodes]
    )
    
    end_o = time.time()
    time_spent_outside_shards_in_seconds += end_o - start_o	
    return total_cross_cuts_required, num_nodes_visited, time_spent_inside_shards_in_seconds, time_spent_outside_shards_in_seconds
	

###########################################
### grow distributed graph on REMOTE shards
###
### The remote containers need to exist, at
### the specified IP and ports.
###########################################
def grow_remote_shards(numshards, nodespershard, pedge, farnodes, verbose):	
    num_shards = numshards
    num_nodes_per_shard = nodespershard
    p_edge_creation = pedge
    num_far_nodes_per_shard = farnodes  #number of nodes in each shard that will be connected to another shard's nodes

    # where?	
    if not IP:
        return "Remote IP has not been set!"
    ip = IP[0]

    if global_verbose:
        if total_recall:
            sys.stderr.write("Growing remote shards, each one in its own container..")
        else:
            print("Growing remote shards, each one in its own container..")

    # the loop that creates the remote shards			
    for i in range(0, num_shards):
        curr_shard = dShard(i, ip, ports[i], num_nodes_per_shard, p_edge_creation, verbose)
        s.append(curr_shard) #keep track of remote shards..
        sfar.append(curr_shard.most_distant_internal_nodes(num_far_nodes_per_shard)) #..and of their far nodes!
        time.sleep(0.1)

    if global_verbose:
        if total_recall:
            sys.stderr.write("Connecting shard neighborhoods..")
        else:
            print("Connecting shard neighborhoods..")
			
    # shard neighborhoods (toroidally wrapped)
    for i in range(0, num_shards):
        sneigh[i] = tw_neigh(i, int(m.sqrt(num_shards)))
		
    if global_verbose:
        if total_recall:
            sys.stderr.write("Pairing shards' distant nodes..")
        else:
            print("Pairing shards' distant nodes..")

    # geometric graph is undirected, so external nodes need to be mirrored: a connection from a node on shard p to 
    # a node on shard q needs to be accompanied by a connection from the node on shard q to the node on shard p
    # Note that I allow pairings to be repeated but I only connect two shards once, using paired_already as semaphore
    paired_already = []
    for p in range(0, num_shards):
        for q in sneigh[p]:
            if (p,q) not in paired_already and (q,p) not in paired_already:
                pairings = sample(set(product([i for i,k in sfar[p]], [i for i,k in sfar[q]])), int(num_far_nodes_per_shard/2))
                #print(pairings)
                for n in pairings:
                    s[p].add_edge_external([(n[0], n[1], 1., 1., q, 1)])  #(ni, ne, x, y, shard, d)
                    s[q].add_edge_external([(n[1], n[0], 1., 1., p, 1)])
                paired_already.append((p,q))

    comment = "Created " + str(num_shards) + " remote toroidal shards, with " + str(int(num_far_nodes_per_shard * 2)) + " nodes per shard connected to other shards' nodes."
    if global_verbose:
        if total_recall:
            sys.stderr.write(comment)
        else:
            print(comment)
    return comment


############################################
### grow distributed graph with LOCAL shards
############################################
def grow_shards(numshards, nodespershard, pedge, farnodes):
    num_shards = numshards
    num_nodes_per_shard = nodespershard
    p_edge_creation = pedge
    num_far_nodes_per_shard = farnodes  #number of nodes in each shard that will be connected to another shard's nodes

    if global_verbose:
        if total_recall:
            sys.stderr.write("Growing local shards`..")
        else:
            print("Growing local shards..")

    for i in range(0, num_shards):
        # Need to change this since my constructor has changed
        #s.append(Shard(i, num_nodes_per_shard, p_edge_creation))
        curr_shard = Shard(i)
        curr_shard.grow_graph(i, num_nodes_per_shard, p_edge_creation)
        s.append(curr_shard) #we keep track of local shards created..
        sfar.append(curr_shard.most_distant_internal_nodes(num=num_far_nodes_per_shard)) ##..and of their far nodes!

    if global_verbose:
        if total_recall:
            sys.stderr.write("Connecting shard neighborhoods..")
        else:
            print("Connecting shard neighborhoods..")		
    # shard neighborhoods (toroidally wrapped)
    for i in range(0, num_shards):
        sneigh[i] = tw_neigh(i, int(m.sqrt(num_shards)))
	
    if global_verbose:
        if total_recall:
            sys.stderr.write("Pairing shards' distant nodes..")
        else:
            print("Pairing shards' distant nodes..")

    # geometric graph is undirected, so external nodes need to be mirrored: a connection from a node on shard p to 
    # a node on shard q needs to be accompanied by a connection from the node on shard q to the node on shard p
    # Note that I allow pairings to be repeated but I only connect two shards once, using paired_already as semaphore
    paired_already = []
    for p in range(0, num_shards):
        for q in sneigh[p]:
            if (p,q) not in paired_already and (q,p) not in paired_already:
                pairings = sample(set(product([i for i,k in sfar[p]], [i for i,k in sfar[q]])), 8)
                #print(pairings)
                for n in pairings:
                    s[p].add_edge_external([(n[0], n[1], 1., 1., q, 1)])  #(ni, ne, x, y, shard, d)
                    s[q].add_edge_external([(n[1], n[0], 1., 1., p, 1)])
                paired_already.append((p,q))

    comment = "Created " + str(num_shards) + " local toroidal shards, with " + str(int(num_far_nodes_per_shard * 2)) + " nodes per shard connected to other shards' nodes."
    if global_verbose:
        if total_recall:
            sys.stderr.write(comment)
        else:
            print(comment)
    return comment


##################################
### dbfs on remotely sharded graph
##################################
def run_ddbfs(begin_shard, verbose=False):
    #if 0 == len(ports):
    #    oopsie = "remote graph shards have not been created yet!"
    #    print(oopsie)
    #    return oopsie

    num_shards = nshards_as_list[0]
    num_nodes_per_shard = num_nodes_per_shard_as_list[0]
    total_cross_cuts_required, num_nodes_visited, time_in, time_out = ddbfs(begin_shard, verbose)

    if global_verbose:
        if total_recall:
            sys.stderr.write("---> Distributed BFS on remote shard fleet complete!")
            sys.stderr.write('    ' + str(total_cross_cuts_required) + 
              ' cross-cuts required for DBFS on ' + str(num_shards) + ' shards starting from shard ' 
              + str(begin_shard) + ', node ' + str(s[begin_shard].node_center()[0]))
            sys.stderr.write('    Total number of nodes visited over total number of nodes in the entire graph: ' + 
              str(num_nodes_visited) + '/' +  str(num_shards * num_nodes_per_shard))
            sys.stderr.write('    Seconds doing BFS inside shards: ' + str(time_in))
            sys.stderr.write('    Seconds doing overhead outside shards: ' + str(time_out))
        else:
            print("---> Distributed BFS on remote shard fleet complete!")
            print('    ' + str(total_cross_cuts_required) + 
              ' cross-cuts required for DBFS on ' + str(num_shards) + ' shards starting from shard ' 
              + str(begin_shard) + ', node ' + str(s[begin_shard].node_center()[0]))
            print('    Total number of nodes visited over total number of nodes in the entire graph: ' + 
              str(num_nodes_visited) + '/' +  str(num_shards * num_nodes_per_shard))
            print('    Seconds doing BFS inside shards: ' + str(time_in))
            print('    Seconds doing overhead outside shards: ' + str(time_out))

    return "Total cross cuts: " + str(total_cross_cuts_required) + ". Total nodes visited: " + str(num_nodes_visited) + "/" +  str(num_shards * num_nodes_per_shard) + ". Total bfs time: " + str(round(time_in,2)) + " s. Overhead: " + str(round(time_out,2)) + " s."


#################################
### dbfs on locally sharded graph
#################################
def run_dbfs(begin_shard, verbose=False):
    total_cross_cuts_required, num_nodes_visited, time_in, time_out = dbfs(begin_shard, verbose)

    num_shards = nshards_as_list[0]
    num_nodes_per_shard = num_nodes_per_shard_as_list[0]

    if global_verbose:
        if total_recall:
            sys.stderr.write("---> Distributed BFS on co-located shards complete!")
            sys.stderr.write('    ' + str(total_cross_cuts_required) + 
              ' cross-cuts required for BFS on ' + str(num_shards) + ' shards starting from shard ' 
              + str(begin_shard) + ', node ' + str(s[begin_shard].node_center()[0]))
            sys.stderr.write('    Total number of nodes visited over total number of nodes in the entire graph: ' + 
              str(num_nodes_visited) + '/' +  str(num_shards * num_nodes_per_shard))
            sys.stderr.write('    Seconds doing BFS inside shards: ' + str(time_in))
            sys.stderr.write('    Seconds doing overhead outside shards: ' + str(time_out))
        else:
            print("---> Distributed BFS on co-located shards complete!")
            print('    ' + str(total_cross_cuts_required) + 
              ' cross-cuts required for BFS on ' + str(num_shards) + ' shards starting from shard ' 
              + str(begin_shard) + ', node ' + str(s[begin_shard].node_center()[0]))
            print('    Total number of nodes visited over total number of nodes in the entire graph: ' + 
              str(num_nodes_visited) + '/' +  str(num_shards * num_nodes_per_shard))
            print('    Seconds doing BFS inside shards: ' + str(time_in))
            print('    Seconds doing overhead outside shards: ' + str(time_out))

    return "Total cross cuts: " + str(total_cross_cuts_required) + ". Total nodes visited: " + str(num_nodes_visited) + "/" +  str(num_shards * num_nodes_per_shard) + ". Total bfs time: " + str(round(time_in,2)) + " s. Overhead: " + str(round(time_out,2)) + " s."


def is_perfect_square(n):
    x = n // 2
    y = set([x])
    while x * x != n:
        x = (x + (n // x)) // 2
        if x in y: return False
        y.add(x)
    return True


def clear_all_lists():
    IP.clear()
    ports_start.clear()
    ports.clear()
    s.clear()
    sfar.clear()
    nshards_as_list.clear()
    num_nodes_per_shard_as_list.clear()
    for i in range(0, nshards_max):
        try:
            sneigh[i].clear()
        except:
            j=0
    sneigh = [None]*nshards_max
	
#####################################################
### globals
#####################################################
app = Flask(__name__)

# global verbosity
global_verbose = True

# role: CLIENT, SERVER, or MASTER-SERVER
# once set cannot be changed. Too confusing!
# This i really just one constant, I use a list to make it persist across calls
role = []

# IP for distributed shards
# This i really just one number, I use a list to make it persist across calls
IP = []

# ports for distributed shards
ports_start = []
ports = []

# number of shards, upper limit
nshards_max = 10000

# number of shards
# This i really just one number, I use a list to make it persist across calls
nshards_as_list = []

# number of nodes per shard
# This i really just one number, I use a list to make it persist across calls
num_nodes_per_shard_as_list = []

# single shard
s = Shard(1776)

# list of shards, either local Shard, remote dShard, dNeoShard, or dJanusShard
s = []
s_neo = []
s_janus = []
s_backup = []

# list of most distant nodes per shard
sfar = []

# shard neighborhoods
sneigh = [None]*nshards_max

# are we containerized?
total_recall = False


#####################################################
###  PUBLIC ENDPOINTS
#####################################################

######################
### Usage: test health
######################
@app.route("/testHealth")
def hello():
    return "Hello from hyper-capable graph shard flask app!"


#####################################################
### Usage: MASTER SERVER (sharded distributed graph)
###
### Caller uses this surface API to create a remote
### distribution of shards and to run a distributed 
### BFS on them.
###
### This is the final scenario where the shards are 
### all remotely located on different containers.
### This specific container does not contain any
### shards. It just coordinates queries across remote
### containers that contain shards.
###
### Note: All remote containers needs to be at a
### single IP address! All graph shard ports need to
### be contiguous! So this only works for docker,
### containers, not k8s pods yet. But the idea is we
### could do something very similar on a k8s cluster.
#####################################################
# i.e. http://localhost:5000/when?port=1234
@app.route("/when", methods=['GET'])
def when():
    port = int(request.args.get('port`'))
    try:
        index = port - ports_start[0]
        return s[index].when 
    except:
        return "Could not find remote shard at that port!"
		

# i.e. http://localhost:5000/create-remote-shards?shards=16&nodes=200&edges=0.08&farnodes=16&shards-ip=192.168.99.100&shard-ports-start-at=1234&verbose=0
@app.route("/create-remote-shards", methods=['GET'])
def create_remote_shards():
    num_shards = int(request.args.get('shards'))
    nodes = int(request.args.get('nodes'))
    edges_p = float(request.args.get('edges'))
    farnodes = int(request.args.get('farnodes'))
    shards_ip = str(request.args.get('shards-ip'))
    ports_start_at = int(request.args.get('shard-ports-start-at'))
    verbose = int(request.args.get('verbose'))
	
    # This instance is now a master-server instance!
    try:
        if (role[0] != "MASTER-SERVER"):
            print("This instance is now a MASTER-SERVER instance!")
        role.clear()
        role.append("MASTER-SERVER")
        s.clear()
        sfar.clear()
    except:
        role.append("MASTER-SERVER")	

    if (num_shards > nshards_max):
        comment = "The upper limit on the number of shards is set as a constant in the program and is equal to " + str(nshards_max) + "." 
        if global_verbose:
            print(comment)
        return comment
		
    if not is_perfect_square(num_shards):
        comment = str(num_shards) + " is not a perfect square! Toroidal wrap will not work. Please specify perfect square number of shards."
        if global_verbose:
            print(comment)
        return comment

    #if 10000 < num_shards and global_verbose:
    #    print("That dbfs will take a loooooooooooooooooong time..")

    # clear lists, set number of shards global
    clear_all_lists()
    nshards_as_list.append(num_shards)
    num_nodes_per_shard_as_list.append(nodes)
	
	# set IP and ports
    IP.append(shards_ip)
    ports_start.append(ports_start_at)
    for i in range(0, num_shards):
        ports.append(ports_start_at + i)
		

    if global_verbose:	
        print("*** This master server will create " + str(num_shards) + " shards of " + str(nodes) + " nodes and " + str(farnodes) + " external edges each, at IP " + shards_ip + ", at ports [" + str(ports_start_at) + "," + str(ports_start_at + num_shards) + "]")	

    # do it
    return grow_remote_shards(num_shards, nodes, edges_p, farnodes, verbose)


# i.e. http://localhost:5000/do-ddbfs?shard=5&verbose=0
@app.route("/do-ddbfs", methods=['GET'])
def do_ddbfs():

    # This instance should be a master-server instance!
    try:
        if (role[0] != "MASTER-SERVER"):
            return "This instance is not a MASTER-SERVER instance!"
    except:
        return "The remote shards have not been created yet!"	

    begin_shard = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))
    if 0 == verbose:
        verbose = False
    else:
        verbose = True

    start = time.ctime()
    if global_verbose:
        print('Starting DBFS on remote shard fleet. The current time is :', start)
    result = run_ddbfs(begin_shard, verbose)
    end = time.ctime()

    if global_verbose:
        if total_recall:
            sys.stderr.write('Finished DBFS. The current time is :', end)
        else:
            print('Finished DBFS. The current time is :', end)

    return 'DBFS started ' + str(start) + ', finished ' + str(end) + '. ' + result 	



###########################################
### Usage: SERVER (graph with local shards)
###
### Caller uses this surface API to create
### a local distribution of shards and to
### run a distributed BFS on them.
###
### This is an interim scenario where the
### shards are all co-located on the same
### container.
###########################################
# i.e. http://localhost:5000/create-shards?shards=16&nodes=200&edges=0.08&farnodes=16
@app.route("/create-shards", methods=['GET'])
def create_shards():
    shards = int(request.args.get('shards'))
    nodes = int(request.args.get('nodes'))
    edges_p = float(request.args.get('edges'))
    farnodes = int(request.args.get('farnodes'))
	
    # clear lists, set number of shards global
    clear_all_lists()
    nshards_as_list.append(shards)
    num_nodes_per_shard_as_list.append(nodes)
    num_shards = shards
	
    # This instance is now a server instance!
    try:
        if (role[0] != "SERVER"):
            print("This instance is now a SERVER instance!")
        role.clear()
        role.append("SERVER")
        s.clear()
        sfar.clear()
    except:
        role.append("SERVER")

    if (num_shards > nshards_max):
        comment = "The upper limit on the number of shards is set as a constant in the program and is equal to " + str(nshards_max) + "." 
        if global_verbose:
            print(comment)
        return comment
		
    if not is_perfect_square(num_shards):
        comment = str(num_shards) + " is not a perfect square! Toroidal wrap will not work. Please specify perfect square number of shards."
        if global_verbose:
            print(comment)
        return comment

    #if 10000 < num_shards and global_verbose:
    #    print("That dbfs will take a loooooooooooooooooong time..")

    # do it
    return grow_shards(num_shards, nodes, edges_p, farnodes)


# i.e. http://localhost:5000/do-dbfs?shard=5&verbose=0
@app.route("/do-dbfs", methods=['GET'])
def do_dbfs():

    # This instance is a server instance!
    try:
        if (role[0] != "SERVER"):
            return "This instance is not a SERVER instance!"
    except:
        return "The local sharded graph has not been created yet!"

    begin_shard = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))
    if 0 == verbose:
        verbose = False
    else:
        verbose = True
    start = time.ctime()
    if global_verbose:
        print('Starting DBFS on local shard fleet. The current time is :', start)
    result = run_dbfs(begin_shard, verbose)
    end = time.ctime()
    if global_verbose:
        print('Finished DBFS. The current time is :', end)
    return 'DBFS started ' + str(start) + ', finished ' + str(end) + '. ' + result 


# i.e. http://localhost:5000/clone-shards-to-neo?neo-ip=192.168.99.100&neo-start-port=7474&how-many-shards=16&verbose=1
@app.route("/clone-shards-to-neo", methods=['GET'])
def clone_shards_to_neo():
    global s_neo
	
    neo_ip = str(request.args.get('neo-ip'))
    neo_start_port = int(request.args.get('neo-start-port'))
    shard_num = int(request.args.get('how-many-shards'))
    verbose = int(request.args.get('verbose'))

    s_neo.clear()
    for i in range(0, shard_num):
        if global_verbose:
            if verbose: print("")
            print("*** cloning local shard #" + str(i) + " to neo port " + str(neo_start_port + i) + "..")
        r = clone_shard_to_neo_internal(neo_ip, neo_start_port + i, i, verbose)
        if verbose:
            print(r)
        s_neo.append(dNeoShard(i, s[i].node_center()[0], neo_ip, neo_start_port + i, verbose))
    done = "finished cloning " + str(shard_num) + " local shards to neo containers at ip " + neo_ip + " and ports [" + str(neo_start_port) + ", " + str(neo_start_port + shard_num - 1) + "]"
    if verbose:
        print("")
        print(done)
    return done	


# i.e. http://localhost:5000/clone-shards-to-janus?janus-ip=192.168.99.100&janus-start-port=7474&how-many-shards=16&verbose=1
@app.route("/clone-shards-to-janus", methods=['GET'])
def clone_shards_to_janus():
    global s_janus

    janus_ip = str(request.args.get('janus-ip'))
    janus_start_port = int(request.args.get('janus-start-port'))
    shard_num = int(request.args.get('how-many-shards'))
    verbose = int(request.args.get('verbose'))

    s_janus.clear()
    for i in range(0, shard_num):
        if global_verbose:
            if verbose: print("")
            print("*** cloning local shard #" + str(i) + " to janus port " + str(janus_start_port + i) + "..")
        r = clone_shard_to_janus_internal(janus_ip, janus_start_port + i, i, verbose)
        if verbose:
            print(r)
        s_janus.append(dJanusShard(i, s[i].node_center()[0], janus_ip, janus_start_port + i, verbose))
    done = "finished cloning " + str(shard_num) + " local shards to janus containers at ip " + janus_ip + " and ports [" + str(janus_start_port) + ", " + str(janus_start_port + shard_num - 1) + "]"
    if verbose:
        print("")
        print(done)
    return done


# i.e. http://localhost:5000/do-ddbfs-on-neo-shards?shard=5&verbose=0
@app.route("/do-ddbfs-on-neo-shards", methods=['GET'])
def do_ddbfs_on_neo_shards():
    global s, s_neo, s_backup
	
    # This should do the dbfs on a dNeoShard cluster

    # move s_neo[] over to s[]
    s_backup.clear()
    for local_shard in s:
        s_backup.append(local_shard)
    s.clear()
    for neo_shard in s_neo:
        s.append(neo_shard)

    # do a stock DBFS
    begin_shard = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))
    if 0 == verbose:
        verbose = False
    else:
        verbose = True

    start = time.ctime()
    if global_verbose:
        print('Starting DBFS on remote neo fleet. The current time is :', start)
    result = run_ddbfs(begin_shard, verbose)
    end = time.ctime()

    if global_verbose:
        if total_recall:
            sys.stderr.write('Finished DBFS. The current time is :', end)
        else:
            print('Finished DBFS. The current time is :', end)
			
    # restore s to local shards:
    s.clear()
    for local_shard in s_backup:
        s.append(local_shard)
    s_backup.clear()

    return 'DBFS on neo fleet started ' + str(start) + ', finished ' + str(end) + '. ' + result 	


# i.e. http://localhost:5000/do-ddbfs-on-janus-shards?shard=5&verbose=0
@app.route("/do-ddbfs-on-janus-shards", methods=['GET'])
def do_ddbfs_on_janus_shards():
    global s, s_janus, s_backup
	
    # This should do the dbfs on a dJanusShard cluster

    # move s_janus[] over to s[]
    s_backup.clear()
    for local_shard in s:
        s_backup.append(local_shard)
    s.clear()
    for janus_shard in s_janus:
        s.append(janus_shard)

    # do a stock DBFS
    begin_shard = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))
    if 0 == verbose:
        verbose = False
    else:
        verbose = True

    start = time.ctime()
    if global_verbose:
        print('Starting DBFS on remote janus fleet. The current time is :', start)
    result = run_ddbfs(begin_shard, verbose)
    end = time.ctime()

    if global_verbose:
        if total_recall:
            sys.stderr.write('Finished DBFS. The current time is :', end)
        else:
            print('Finished DBFS. The current time is :', end)
			
    # restore s to local shards:
    s.clear()
    for local_shard in s_backup:
        s.append(local_shard)
    s_backup.clear()

    return 'DBFS on janus fleet started ' + str(start) + ', finished ' + str(end) + '. ' + result 


############################################
### Usage: CLIENT (one local shard only)
###
### Caller uses this surface API to create
### a single local shard, inquire upon the 
### shard's distant nodes, add cross-cut 
### edges, and run single shard BFSes.
###
### This would be the most typical scenario.
############################################
# i.e. http://localhost:5000/role
@app.route("/role", methods=['GET'])
def instancerole():	
    if 0 == len(role):
        return "Undecided"
    else:
        return role[0]

# i.e. http://localhost:5000/create-graph-shard?id=0&nodes=200&edges=0.08
@app.route("/create-graph-shard", methods=['GET'])
def create_graph_shard():
    id = int(request.args.get('id'))
    nodes = int(request.args.get('nodes'))
    edges_p = float(request.args.get('edges'))
	
    # accessing globals
    global s, sfar, role, num_nodes_per_shard_as_list
	
    # This instance is now a client instance!
    try:
        if (role[0] != "CLIENT"):
            print("This instance is now a CLIENT instance!")
        role.clear()
        role.append("CLIENT")
        s.clear()
        sfar.clear()
    except:
        role.append("CLIENT")		
	
    if global_verbose:
        print("Instantiating sole shard..")

    # I keep adding shards. Note only the last shard is referenced in methods below.
	# I could just as easily delete the old shards, but I may want to debug with them.
    #sole_shard = Shard(1779 if 0==len(s) else 1779 + len(s))
	
	# Nah, just clear the list
    sole_shard = Shard(1779)
    s.clear()
    s.append(sole_shard)
    num_nodes_per_shard_as_list.clear()
    num_nodes_per_shard_as_list.append(nodes)
		
    if global_verbose:
        print("Creating graph shard with nodes, edge probability ", str(nodes), str(edges_p))
    return str(sole_shard.grow_graph(id, nodes, edges_p))


# i.e. http://localhost:5000/nodes?id=0
@app.route("/nodes", methods=['GET'])
def nodes():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    id = int(request.args.get('id'))
    return j.dumps(s[id].nodes()).replace(' ', '')


# i.e. http://localhost:5000/edges?id=0
@app.route("/edges", methods=['GET'])
def edges():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    id = int(request.args.get('id'))
    return j.dumps(s[id].edges()).replace(' ', '')


# i.e. http://localhost:5000/node-center?id=0
@app.route("/node-center", methods=['GET'])
def node_center():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    id = int(request.args.get('id'))
    return j.dumps(s[id].node_center()).replace(' ', '')


# i.e. http://localhost:5000/node-attribute?id=0&node-id=0&attribute=remote
@app.route("/node-attribute", methods=['GET'])
def node_attribute():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    shard_id = int(request.args.get('id'))
    node_id = int(request.args.get('node-id'))
    node_attribute = str(request.args.get('attribute'))
	
    return j.dumps(s[shard_id].node_attribute(node_id, node_attribute)).replace(' ', '')


# i.e. http://localhost:5000/edge-attribute?id=0&edge-id=0&attribute=remote
@app.route("/edge-attribute", methods=['GET'])
def edge_attribute():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    shard_id = int(request.args.get('id'))
    edge_id = int(request.args.get('edge-id'))
    edge_attribute = str(request.args.get('attribute'))
	
    return j.dumps(s[shard_id].edge_attribute(edge_id, edge_attribute)).replace(' ', '')


# i.e. http://localhost:5000/nodes-with-attribute?id=0&attribute=remote
@app.route("/nodes-with-attribute", methods=['GET'])
def nodes_with_attribute():
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    shard_id = int(request.args.get('id'))
    node_attribute = str(request.args.get('attribute'))
	
    return j.dumps(s[shard_id].nodes_with_attribute(node_attribute)).replace(' ', '')


# i.e. http://localhost:5000/most-distant-internal-nodes?id=0&how-many=16
@app.route("/most-distant-internal-nodes", methods=['GET'])
def most_distant_internal_nodes_endpoint():

    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    id = int(request.args.get('id'))
    how_many = int(request.args.get('how-many'))

    #print("$$$$$$$$$$$$$$$ ~dk debugging:")
    #print(str(id))
    #print(s[id].most_distant_internal_nodes(num = how_many))
    #print(j.dumps(s[id].most_distant_internal_nodes(num = how_many)).replace(' ', ''))

    return j.dumps(s[id].most_distant_internal_nodes(num = how_many)).replace(' ', '')


# Note that info is a list without leading and trailing parenses. Gets converted to a list of lists herein.
# i.e. http://localhost:5000/add-edge-external?info=ni0,ne0,x0,y0,shard0,d0,ni1,ne1,x1,y1,shard1,d1,ni2,ne2,x2,y2,shard2,d2,...
# i.e. http://localhost:5000/add-edge-external?info=197,30,0.5,0.5,1,10,198,31,0.6,0.6,2,11,199,32,0.7,0.7,3,12
@app.route("/add-edge-external", methods=['GET'])
def add_edge_external():
    global s

    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    # This instance is a client instance!
    try:
        if (role[0] != "CLIENT"):
            return "This instance is not a CLIENT instance!"
    except:
        return "graph has not been created yet!"

		
	# [(n[0], n[1], 1., 1., q, 1)] == (ni, ne, x, y, shard, d)
	
	# flat list (note: x and y are floats)
    info = request.args.get('info')
    list_of_strings = info.split(",")
    #info = list(filter(lambda e: e != ',', info))
    list_of_numbers = list(map(lambda e: round(float(e),2) if '.' in e else int(e), list_of_strings))
	
    if 0 > len(info) % 6:
        print("The argument should be a list of 6-tuple external edge information!")
        return "The argument should be a list of 6-tuple external edge information!"
	
	# list of lists conversion
    list_of_crosscuts = [list_of_numbers[i:i+6] for i in range(0, len(list_of_numbers), 6)]
    #print(list_of_crosscuts)

    return s[0].add_edge_external(list_of_crosscuts)

    # unit-testing
    #info = list(request.args.get('info'))
    #info = list(filter(lambda e: e != ',', info))
    #info = list(map(lambda e: int(e), info))
    #info_type = type(info)
    #print(info)
    #print(info_type)
    #return "testing"


# 4-19-2020: I had a very crazy bug here: If the block checking on the length of s is after the parsing
# of query arguments, then somehow s[shard_id] gets lots in space, and only s[0] works...

# Same as below except I start a BFS from multiple internal nodes
# 
# i.e. http://localhost:5000/bfs-trees-with-remote-nodes?sources=22,171,99,7,44&verbose=1
@app.route("/bfs-trees-with-remote-nodes", methods=['GET'])
def bfs_trees_with_remote_nodes():
    global s
	
    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"
		
    # This instance is a client instance!
    try:
        if (role[0] != "CLIENT"):
            return "This instance is not a CLIENT instance!"
    except:
        return "graph has not been created yet!"

    #sources = list(request.args.get('sources'))
    sources = myints(j.loads(myjson(request.args.get('sources')))) 
    #sources = list(filter(lambda e: e != ',', sources))
    #sources = list(map(lambda e: int(e), sources))
    try:
        verbose = int(request.args.get('verbose'))
    except:
        verbose = 0
    #print('@@@: ' + str(sources))

    shard_id = 0
    try:
        shard_id = int(request.args.get('id'))
    except:
        shard_id = 0

    result = s[shard_id].bfs_trees_with_remote_nodes(sources)
    if verbose:
        print(result)
    return j.dumps(result).replace(' ', '')
	

# I do a BFS starting from the shard's center node. The internal path is returned
# together with the external node (and its shard #) that needs to be visited next
#	
# i.e. http://localhost:5000/bfs-trees-with-remote-nodes-from-center-node?id=0
@app.route("/bfs-trees-with-remote-nodes-from-center-node", methods=['GET'])
def bfs_trees_with_remote_nodes_from_center_node():
    global s

    if(0 == len(s)):
        print("graph shard not yet created!")
        return "graph shard not yet created!"

    # This instance is a client instance!
    try:
        if (role[0] != "CLIENT"):
            return "This instance is not a CLIENT instance!"
    except:
        return "graph has not been created yet!"

    shard_id = 0
    try:
        shard_id = int(request.args.get('id'))
    except:
        shard_id = 0

    start_node = s[shard_id].node_center()[0]
    start_node_list = []
    start_node_list.append(start_node)
    return j.dumps(s[shard_id].bfs_trees_with_remote_nodes(start_node_list)).replace(' ', '')
	

# This clones the specified local shard to a neo container
def clone_shard_to_neo_internal(neo_ip, neo_port, shard_id, verbose):
    global s
	
    if(0 == len(s)):
        print("Local graph shards not yet created!")
        return "Local graph shards not yet created!"
	
    # login to neo server
    #graph = Graph()
    #graph = Graph(host=url, auth=("neo4j", "test"))
    graph = Graph("http://" + neo_ip + ":" + str(neo_port) + "/db/data/", bolt=False, auth=("neo4j", "test"))


    # just don't call these networx APIs, all kinds of problems ensue!
    #numnodes = s[shard_id].numnodes
    #numedges = s[shard_id].numedges

	# get edges
    edges = s[shard_id].edges()
    if verbose:
        print("edges:")
        print (edges)
    numedges = len(edges)
	
    # get node 'remote' properties
    numnodes = 0
    remote_nodes = dict()
    for node_id in s[shard_id].graph().nodes():
        numnodes += 1
        label = s[shard_id].graph().nodes[node_id]['remote']
        if label is not None:
            remote_nodes[node_id] = label
    if verbose:
        print("remote nodes:")
        print(remote_nodes)

    # go through edges and create source and target nodes and relationship
    #for source_node_id, target_node_id in s[i].edges():
    i = 0
    if verbose:
        print("cloning nodes and edges to neo with CYPHER..")
    for source_node_id, target_node_id in edges:
        
        #source_remote_attribute = s[i].graph().nodes[source_node_id]['remote'] #None or (shard, ne, d)
        #source_pos_attribute = s[i].graph().nodes[target_node_id]['pos'] #x,y
        #target_remote_attribute = s[i].graph().nodes[target_node_id]['remote'] #None or (shard, ne, d)
        #target_pos_attribute = s[i].graph().nodes[target_node_id]['pos'] #x,y
        source_remote_attribute = remote_nodes[source_node_id] if source_node_id in remote_nodes else []
        source_pos_attribute = 'foo'
        target_remote_attribute = remote_nodes[target_node_id] if target_node_id in remote_nodes else []
        target_pos_attribute = 'bar'	
        
        #if not source_remote_attribute is None:
        #    print("source(" + str(source_node_id) + ": " + str(source_remote_attribute))

        i += 1
        if verbose:
            print("*** iteration", str(i))	
            if 0 < len(target_remote_attribute):
                print("source(" + str(source_node_id) + "), target(" + str(target_node_id) + "): " + str(target_remote_attribute))

        n = Node("person", id=source_node_id, remote=source_remote_attribute, pos=source_pos_attribute)
        graph.create(n)
        m = Node("person", id=target_node_id, remote=target_remote_attribute, pos=target_pos_attribute)
        graph.create(m)
        r = Relationship(n, "connected", m, since=1999)
        graph.create(r)
        #r2 = Relationship(m, "connected", n, since=1999)
        #graph.create(r2)


    if verbose:
        print("neo status:")
        for n,r,m in graph.run("MATCH (n)-[r]-(m) RETURN n,r,m;"):
            print (n,r,m)

    return str(numnodes) + " nodes and " + str(numedges) + " edges cloned to neo on port " + str(neo_port) + " and ip " + neo_ip


# i.e. http://localhost:5000/clone-shard-to-neo?neo-ip=192.168.99.100&neo-port=7474&shard=0&verbose=1
@app.route("/clone-shard-to-neo", methods=['GET'])
def clone_shard_to_neo():

    neo_ip = str(request.args.get('neo-ip'))
    neo_port = int(request.args.get('neo-port'))
    shard_id = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))

    return clone_shard_to_neo_internal(neo_ip, neo_port, shard_id, verbose)


# i.e. http://localhost:5000/neo-edges?neo-ip=192.168.99.100&neo-port=7474
@app.route("/neo-edges", methods=['GET'])
def neo_edges():

    neo_ip = str(request.args.get('neo-ip'))
    neo_port = int(request.args.get('neo-port'))
	
    # login to neo server
    graph = Graph("http://" + neo_ip + ":" + str(neo_port) + "/db/data/", bolt=False, auth=("neo4j", "test"))
	
    print("status:")
    for n,r,m in graph.run("MATCH (n)-[r]-(m) RETURN n,r,m;"):
        print (n,r,m)

    return "edges printed on STDOUT. You need to run this container with -it option to see this."
	

# i.e. http://localhost:5000/neo-clear?neo-ip=192.168.99.100&neo-port=7474
@app.route("/neo-clear", methods=['GET'])
# deletes all nodes and edges!	
def neo_clear():

    neo_ip = str(request.args.get('neo-ip'))
    neo_port = int(request.args.get('neo-port'))
	
    # login to neo server
    graph = Graph("http://" + neo_ip + ":" + str(neo_port) + "/db/data/", bolt=False, auth=("neo4j", "test"))
	
    graph.run("MATCH (n) DETACH DELETE n;")
    return "cleared all nodes and edges!"
	

# This is a multi-BFS on a neo4j graph. This is *not optimized for performance* and
# probably not really reflective of the performance of CYPHER traversals. But since
# there is no built-in CYPHER BFS, I just get a list of nodes and edges using CYPHER 
# and then do a classic BFS. So, there.	
def bfs_trees_with_remote_nodes_neo_internal(neo_ip, neo_port, sources, verbose):

    start_time = 0
    finish_time = 0
    if verbose:
        start_time = time.time()
        print('BFS from: ' + str(sources))
	
    # login to neo server
    #graph = Graph()
    #graph = Graph(host=url, auth=("neo4j", "test"))
    graph = Graph("http://" + neo_ip + ":" + str(neo_port) + "/db/data/", bolt=False, auth=("neo4j", "test"))

	
	# step 1: get all graph relationships, and find remote nodes with link info
	# NOTE: Just like janus, neo creates its own id's, but I don;t have to go through
	# neos ids because of the expressivity of CYPHER: I can get the edges together with
	# the nodes, so I expect CYPHER queries to complete faster, for a beginner level of
	# expertise on both DSLs
    nodes = set()
	
    # Question: If a node is disconnected, it does not appear in this query. Wild! How do I get all nodes?
    #for n in graph.run("MATCH (n) RETURN n;"):
    #    nodes.add(n[0]['id'])
    #    #print(n[0]['id'])
    #print("number of nodes:")
    #print(len(nodes))
	
    remote_nodes = dict()
    edges = dict()
    for n,r,m in graph.run("MATCH (n)-[r]-(m) RETURN n,r,m;"):
        nodes.add(n['id'])
        if n['id'] in edges:
            edges[n['id']].add(m['id'])
        else:
            edges[n['id']] = {m['id']}
        if n['remote']:
            remote_nodes[n['id']] = n['remote']

    numedges = 0
    for i in edges:
        numedges += len(edges[i])

    # This is totally cheating.. but I don't have an answer to my question above!
    max_node = max(nodes)
		
    if verbose: 
        print("edges:")
        print(edges)
        print("number of edges:")
        print(numedges)
        print("remote nodes:")
        print(remote_nodes)
        print("number of nodes:")
        print(len(nodes))
        print("max of nodes:")
        print(max_node)
        print("BFS..")

    # step 2: BFS for each source
	
    # Mark all the vertices as not visited 
    visited = [False] * (max_node + 1) 
		
    innodes = set()
    extnodes = dict()
    for s in sources:
  
        # Create a queue for BFS starting from s
        queue = [] 

        # Mark the source node as  
        # visited and enqueue it,
        # add it to either innodes
        # or extnodes		
        queue.append(s) 
        visited[s] = True
        if s in remote_nodes:
            if verbose:
                print(s, remote_nodes[s])
            #extnodes.add((s, remote_nodes[s]))
            extnodes[s] = remote_nodes[s]
        else:
            innodes.add(s)
  
        while queue: 
  
            # Dequeue a vertex from queue
            s = queue.pop(0) 
  
            # Get all adjacent vertices of the 
            # dequeued vertex s. If not visited, 
            # then mark it visited, enqueue it,
            # and add it to either innodes or 
            # extnodes			
            if s in edges:
                for i in edges[s]: 
                    if visited[i] == False: 
                        queue.append(i) 
                        visited[i] = True
                        if i in remote_nodes:
                            #print(i, remote_nodes[i])
                            #extnodes.add((i, remote_nodes[i]))
                            extnodes[i] = remote_nodes[i]
                        else:
                            innodes.add(i)

    # return all internal nodes visited and all external nodes visited
    # as separate lists
    #print("innodes:")
    #print(innodes)
    #print("extnodes:")
    #print(extnodes)
    extnodes_as_list = []
    #for k in extnodes:
    #    extnodes_as_list.append([k, extnodes[k]])
    ext_shards_and_nodes = dict()
    for k in extnodes:
        if extnodes[k][0] in ext_shards_and_nodes:
            ext_shards_and_nodes[extnodes[k][0]].add(extnodes[k][1])
        else:
            ext_shards_and_nodes[extnodes[k][0]] = {extnodes[k][1]}
    #print(ext_shards_and_nodes)
    for k in ext_shards_and_nodes:
        extnodes_as_list.append([k, list(ext_shards_and_nodes[k])])
    #print(extnodes_as_list)

    if verbose:
        print(list((list(innodes), extnodes_as_list)))
        finish_time = time.time()
        bfs_time_in_seconds = finish_time - start_time
        print("*** BFS on neo took " + str(bfs_time_in_seconds) + " seconds.")

    return j.dumps(list((list(innodes), extnodes_as_list)))
	

# i.e. http://localhost:5000/bfs-trees-with-remote-nodes-neo?neo-ip=192.168.99.100&neo-port=7474&sources=22,171,99,7,44&verbose=1
@app.route("/bfs-trees-with-remote-nodes-neo", methods=['GET'])
def bfs_trees_with_remote_nodes_neo():

    neo_ip = str(request.args.get('neo-ip'))
    neo_port = int(request.args.get('neo-port'))
    verbose = int(request.args.get('verbose'))
    sources = j.loads(myjson(request.args.get('sources')))

    return bfs_trees_with_remote_nodes_neo_internal(neo_ip, neo_port, sources, verbose)

	
# This clones the specified local shard to a janus container
def clone_shard_to_janus_internal(janus_ip, janus_port, shard_id, verbose):
    global s
	
    if(0 == len(s)):
        print("Local graph shards not yet created!")
        return "Local graph shards not yet created!"
	
    # login to janus server
    graph = jGraph()
    #connstring = 'ws://' + url + ':8182/gremlin'
    connstring = 'ws://' + janus_ip + ':' + str(janus_port) + '/gremlin'
    #print(connstring)
    g = graph.traversal().withRemote(DriverRemoteConnection(connstring, 'g'))


    # just don't call these networx APIs, all kinds of problems ensue!
    #numnodes = s[shard_id].numnodes
    #numedges = s[shard_id].numedges

	# get edges
    edges = s[shard_id].edges()
    if verbose:
        print("edges:")
        print (edges)
    numedges = len(edges)
	
    # get node 'remote' properties
    numnodes = 0
    remote_nodes = dict()
    for node_id in s[shard_id].graph().nodes():
        numnodes += 1
        label = s[shard_id].graph().nodes[node_id]['remote']
        if label is not None:
            remote_nodes[node_id] = label
    if verbose:
        print("remote nodes:")
        print(remote_nodes)

    # go through edges and create source and target nodes and relationship
    #for source_node_id, target_node_id in s[i].edges():
    i = 0
    if verbose:
        print("cloning nodes and edges to janus with GREMLIN..")
    for source_node_id, target_node_id in edges:
        
        #source_remote_attribute = s[i].graph().nodes[source_node_id]['remote'] #None or (shard, ne, d)
        #source_pos_attribute = s[i].graph().nodes[target_node_id]['pos'] #x,y
        #target_remote_attribute = s[i].graph().nodes[target_node_id]['remote'] #None or (shard, ne, d)
        #target_pos_attribute = s[i].graph().nodes[target_node_id]['pos'] #x,y
		
        # Note I mark properties differently on janus because of the following exception when trying to use json arrays:
        # gremlin_python.driver.protocol.GremlinServerError: 500: Property value [[]] is of type class java.util.ArrayList is not supported
        # So I turn them into strings first! Need to convert back when BFSing!

        #source_remote_attribute = remote_nodes[source_node_id] if source_node_id in remote_nodes else []
        source_remote_attribute = j.dumps(remote_nodes[source_node_id]).replace(' ', '') if source_node_id in remote_nodes else '[]'
        source_pos_attribute = 'foo'
        #target_remote_attribute = remote_nodes[target_node_id] if target_node_id in remote_nodes else []
        target_remote_attribute = j.dumps(remote_nodes[target_node_id]).replace(' ', '') if target_node_id in remote_nodes else '[]'
        target_pos_attribute = 'bar'	
        
        #if not source_remote_attribute is None:
        #    print("source(" + str(source_node_id) + ": " + str(source_remote_attribute))

        i += 1
        if verbose:
            print("*** iteration", str(i))
        trg_a = j.loads(target_remote_attribute)
        if verbose:		
            if 0 < len(trg_a):
                print("source(" + str(source_node_id) + "), target(" + str(target_node_id) + "): " + str(target_remote_attribute))

        n = g.addV('person').property('id', source_node_id).property('remote', source_remote_attribute).property('pos', source_pos_attribute).next()
        #g.V(n).property('remote', source_remote_attribute).next()
        #g.V(n).property('pos', source_pos_attribute).next()
        
        m = g.addV('person').property('id', target_node_id).property('remote', target_remote_attribute).property('pos', target_pos_attribute).next()
        #g.V(m).property('remote', target_remote_attribute).next()
        #g.V(m).property('pos', target_pos_attribute).next()

        # janus by default is one-directional, as opposed to neo, so I need to add the edge both ways        
        g.V(n).addE('connected').to(m).property('since', 1999).next()
        g.V(m).addE('connected').to(n).property('since', 1999).next()
        # groovy: j.addE('edge').from(n).to(m).property('since', 1999)
        # g.V(Bindings.of('id',v1)).addE('knows').to(v2).property('weight',0.75).iterate()


    if verbose:
        print("janus status:")
        l = [{**node.__dict__, **properties} for node in g.V() for properties in g.V(node).valueMap()]
        print(l)

    return str(numnodes) + " nodes and " + str(numedges) + " edges cloned to janus on port " + str(janus_port) + " and ip " + janus_ip


# i.e. http://localhost:5000/clone-shard-to-janus?janus-ip=192.168.99.100&janus-port=8182&shard=0&verbose=1
@app.route("/clone-shard-to-janus", methods=['GET'])
def clone_shard_to_janus():

    janus_ip = str(request.args.get('janus-ip'))
    janus_port = int(request.args.get('janus-port'))
    shard_id = int(request.args.get('shard'))
    verbose = int(request.args.get('verbose'))

    return clone_shard_to_janus_internal(janus_ip, janus_port, shard_id, verbose)

# i.e. http://localhost:5000/janus-edges?janus-ip=192.168.99.100&janus-port=8182
@app.route("/janus-edges", methods=['GET'])
def janus_edges():

    janus_ip = str(request.args.get('janus-ip'))
    janus_port = int(request.args.get('janus-port'))
	
    # login to janus server
    graph = jGraph()
    #connstring = 'ws://' + url + ':8182/gremlin'
    connstring = 'ws://' + janus_ip + ':' + str(janus_port) + '/gremlin'
    #print(connstring)
    g = graph.traversal().withRemote(DriverRemoteConnection(connstring, 'g'))

    id_mapping = dict()
    l1 = [{**node.__dict__}['id'] for node in g.V()]
    l2 = [properties['id'][0] for node in g.V() for properties in g.V(node).valueMap()]
    print(l2)
    print(len(l1))
    print(len(l2))
    for (a, b) in zip(l1, l2): 
        id_mapping[a] = b
    print(id_mapping)
    return "edges printed on STDOUT. You need to run this container with -it option to see this."


# i.e. http://localhost:5000/janus-clear?janus-ip=192.168.99.100&janus-port=8182
@app.route("/janus-clear", methods=['GET'])
# deletes all nodes and edges!	
def janus_clear():

    janus_ip = str(request.args.get('janus-ip'))
    janus_port = int(request.args.get('janus-port'))
	
    # login to janus server
    graph = jGraph()
    #connstring = 'ws://' + url + ':8182/gremlin'
    connstring = 'ws://' + janus_ip + ':' + str(janus_port) + '/gremlin'
    #print(connstring)
    g = graph.traversal().withRemote(DriverRemoteConnection(connstring, 'g'))
	
    try:
        g.V().drop().next()
    except:
        print("cleared all nodes and edges!")
    return "cleared all nodes and edges!"


# This is a multi-BFS on a janus graph. This is *not optimized for performance* and
# probably not really reflective of the performance of GREMLIN traversals. But since
# there is no built-in GREMLIN BFS, I just get a list of nodes and edges using GREMLIN 
# and then do a classic BFS. So, there.	
def bfs_trees_with_remote_nodes_janus_internal(janus_ip, janus_port, sources, verbose):

    start_time = 0
    finish_time = 0
    if verbose:
        start_time = time.time()
        print('BFS from: ' + str(sources))
	
    # login to janus server
    graph = jGraph()
    #connstring = 'ws://' + url + ':8182/gremlin'
    connstring = 'ws://' + janus_ip + ':' + str(janus_port) + '/gremlin'
    g = graph.traversal().withRemote(DriverRemoteConnection(connstring, 'g'))
	
	# step 1: map janus id's to my id's, and find remote nodes with link info
    id_mapping = dict()
    remote_nodes = dict()
    janus_ids = [{**node.__dict__}['id'] for node in g.V()]
    node_props = [properties for node in g.V() for properties in g.V(node).valueMap()]

    if verbose:
        print("nodes:")
    for n in node_props:
        #print(n)
        try:
            if verbose:
                print(n['id'], n['remote'])
                #print('---')
            # Note I mark an empty property differently on janus because of the following exception with '[]':
            # Instead of if n['remote'][0] != '[]': like with neo, which causes the following error:
            # gremlin_python.driver.protocol.GremlinServerError: 500: Property value [[]] is of type class java.util.ArrayList is not supported
            if 0 < len(j.loads(n['remote'][0])):
                remote_nodes[n['id'][0]] = j.loads(n['remote'][0])
        except:
            #print('')
            continue
    if verbose:
        print("number of nodes:")
        print(str(len(node_props)))
        print("remote_nodes:")
        print(remote_nodes)
	
    dino_ids = [n['id'][0] for n in node_props]
    for (a, b) in zip(janus_ids, dino_ids): 
        id_mapping[a] = b
    if verbose:
        print("janus to dino id mapping:")
        print(id_mapping)
		
			
    # step 2: get edges
    edges = dict()
    for e in g.E():
        #return e.inVertex(), e.outVertex()
        #return e.bothVertices()
        j_src = e.inV.__dict__['id']
        j_trg = e.outV.__dict__['id']
        d_src = id_mapping[j_src]
        d_trg = id_mapping[j_trg]
        if d_src in edges:
            edges[d_src].add(d_trg)
        else:
            edges[d_src] = {d_trg}
    if verbose:
        print("edges:")
        print(edges)
        print("BFS..")

    # step 3: BFS for each source
	
    # Mark all the vertices as not visited 
    visited = [False] * (len(node_props)) 
		
    innodes = set()
    extnodes = dict()
    for s in sources:
  
        # Create a queue for BFS starting from s
        queue = [] 

        # Mark the source node as  
        # visited and enqueue it,
        # add it to either innodes
        # or extnodes		
        queue.append(s) 
        visited[s] = True
        if s in remote_nodes:
            #print(s, remote_nodes[s])
            #extnodes.add((s, remote_nodes[s]))
            extnodes[s] = remote_nodes[s]
        else:
            innodes.add(s)
  
        while queue: 
  
            # Dequeue a vertex from queue
            s = queue.pop(0) 
  
            # Get all adjacent vertices of the 
            # dequeued vertex s. If not visited, 
            # then mark it visited, enqueue it,
            # and add it to either innodes or 
            # extnodes			
            if s in edges:
                for i in edges[s]: 
                    if visited[i] == False: 
                        queue.append(i) 
                        visited[i] = True
                        if i in remote_nodes:
                            #print(i, remote_nodes[i])
                            #extnodes.add((i, remote_nodes[i]))
                            extnodes[i] = remote_nodes[i]
                        else:
                            innodes.add(i)

    # return all internal nodes visited and all external nodes visited
    # as separate lists
    #print("innodes:")
    #print(innodes)
    #print("extnodes:")
    #print(extnodes)
    #print("done")
    extnodes_as_list = []
    #for k in extnodes:
    #    extnodes_as_list.append([k, extnodes[k]])
    ext_shards_and_nodes = dict()
    for k in extnodes:
        if extnodes[k][0] in ext_shards_and_nodes:
            ext_shards_and_nodes[extnodes[k][0]].add(extnodes[k][1])
        else:
            ext_shards_and_nodes[extnodes[k][0]] = {extnodes[k][1]}
    #print(ext_shards_and_nodes)
    for k in ext_shards_and_nodes:
        extnodes_as_list.append([k, list(ext_shards_and_nodes[k])])
    #print(extnodes_as_list)

    if verbose:
        print(list((list(innodes), extnodes_as_list)))
        finish_time = time.time()
        bfs_time_in_seconds = finish_time - start_time
        print("*** BFS on janus took " + str(bfs_time_in_seconds) + " seconds.")

    return j.dumps(list((list(innodes), extnodes_as_list)))
	

# i.e. http://localhost:5000/bfs-trees-with-remote-nodes-janus?janus-ip=192.168.99.100&janus-port=8182&sources=22,171,99,7,44&verbose=1
@app.route("/bfs-trees-with-remote-nodes-janus", methods=['GET'])
def bfs_trees_with_remote_nodes_janus():

    janus_ip = str(request.args.get('janus-ip'))
    janus_port = int(request.args.get('janus-port'))
    verbose = int(request.args.get('verbose'))
    sources = j.loads(myjson(request.args.get('sources')))

    return bfs_trees_with_remote_nodes_janus_internal(janus_ip, janus_port, sources, verbose)


# For reference: How to do a POST	
#@app.route("/analyse/sentiment", methods=['POST'])
#def analyse_sentiment():
#    sentence = request.get_json()['sentence']
#    polarity = TextBlob(sentence).sentences[0].polarity
#    return jsonify(
#        sentence=sentence,
#        polarity=polarity
#    )

#@app.route('/person', methods=['POST'])
#def new_person():
#    logging.info('Request Received: Add New Person')
#    g = setup_graph()
#    try:
#        properties = app.current_request.json_body
#        # TODO - Validate the JSON
#        logging.info('Adding New Person to Graph')
#        # Get the ID from the JSON
#        person_id = properties.pop('id')

# The UI
@app.route("/")
def home():
    return render_template("home.html")
	
@app.route("/theory")
def theory():
    return render_template("theory.html")

@app.route("/exp1")
def exp1():
    return render_template("exp1.html")

@app.route("/exp2")
def exp2():
    return render_template("exp2.html")

@app.route("/exp3")
def exp3():
    return render_template("exp3.html")
		
if __name__ == '__main__':
    app.run(host='0.0.0.0', port=5000)
