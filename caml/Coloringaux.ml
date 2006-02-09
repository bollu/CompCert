open Camlcoq
open Datatypes
open BinPos
open BinInt
open AST
open Maps
open Registers
open Locations
open RTL
open RTLtyping
open InterfGraph
open Conventions

(* George-Appel graph coloring *)

(* \subsection{Internal representation of the interference graph} *)

(* To implement George-Appel coloring, we first transform the representation
   of the interference graph, switching to the following 
   imperative representation that is well suited to the coloring algorithm. *)

(* Each node of the graph (i.e. each pseudo-register) is represented as
   follows. *)

type node =
  { ident: reg;                         (*r register identifier *)
    typ: typ;                           (*r its type *)
    regclass: int;                      (*r identifier of register class *)
    spillcost: float;                   (*r estimated cost of spilling *)
    mutable adjlist: node list;         (*r all nodes it interferes with *)
    mutable degree: int;                (*r number of adjacent nodes *)
    mutable movelist: move list;        (*r list of moves it is involved in *)
    mutable alias: node option;         (*r [Some n] if coalesced with [n] *)
    mutable color: loc option;          (*r chosen color *)
    mutable nstate: nodestate;          (*r in which set of nodes it is *)
    mutable nprev: node;                (*r for double linking *)
    mutable nnext: node                 (*r for double linking *)
  }

(* These are the possible states for nodes. *)

and nodestate =
  | Colored
  | Initial
  | SimplifyWorklist
  | FreezeWorklist
  | SpillWorklist
  | CoalescedNodes
  | SelectStack

(* Each move (i.e. wish to be put in the same location) is represented
   as follows. *)

and move =
  { src: node;                          (*r source of the move *)
    dst: node;                          (*r destination of the move *)
    mutable mstate: movestate;          (*r in which set of moves it is *)
    mutable mprev: move;                (*r for double linking *)
    mutable mnext: move                 (*r for double linking *)
  }

(* These are the possible states for moves *)

and movestate =
  | CoalescedMoves
  | ConstrainedMoves
  | FrozenMoves
  | WorklistMoves
  | ActiveMoves

(* The algorithm manipulates partitions of the nodes and of the moves
   according to their states, frequently moving a node or a move from
   a state to another, and frequently enumerating all nodes or all moves
   of a given state.  To support these operations efficiently,
   nodes or moves having the same state are put into imperative doubly-linked
   lists, allowing for constant-time insertion and removal, and linear-time
   scanning.  We now define the operations over these doubly-linked lists. *)

module DLinkNode = struct
  type t = node
  let make state =
    let rec empty =
      { ident = Coq_xH; typ = Tint; regclass = 0;
        adjlist = []; degree = 0; spillcost = 0.0;
        movelist = []; alias = None; color = None;
        nstate = state; nprev = empty; nnext = empty }
    in empty
  let dummy = make Colored
  let clear dl = dl.nnext <- dl; dl.nprev <- dl
  let notempty dl = dl.nnext != dl
  let insert n dl =
    n.nstate <- dl.nstate;
    n.nnext <- dl.nnext; n.nprev <- dl;
    dl.nnext.nprev <- n; dl.nnext <- n
  let remove n dl =
    assert (n.nstate = dl.nstate);
    n.nnext.nprev <- n.nprev; n.nprev.nnext <- n.nnext
  let move n dl1 dl2 =
    remove n dl1; insert n dl2
  let pick dl =
    let n = dl.nnext in remove n dl; n
  let iter f dl =
    let rec iter n = if n != dl then (f n; iter n.nnext)
    in iter dl.nnext
  let fold f dl accu =
    let rec fold n accu = if n == dl then accu else fold n.nnext (f n accu)
    in fold dl.nnext accu
end

module DLinkMove = struct
  type t = move
  let make state =
    let rec empty =
      { src = DLinkNode.dummy; dst = DLinkNode.dummy; 
        mstate = state; mprev = empty; mnext = empty }
    in empty
  let dummy = make CoalescedMoves
  let clear dl = dl.mnext <- dl; dl.mprev <- dl
  let notempty dl = dl.mnext != dl
  let insert m dl =
    m.mstate <- dl.mstate;
    m.mnext <- dl.mnext; m.mprev <- dl;
    dl.mnext.mprev <- m; dl.mnext <- m
  let remove m dl =
    assert (m.mstate = dl.mstate);
    m.mnext.mprev <- m.mprev; m.mprev.mnext <- m.mnext
  let move m dl1 dl2 =
    remove m dl1; insert m dl2
  let pick dl =
    let m = dl.mnext in remove m dl; m
  let iter f dl =
    let rec iter m = if m != dl then (f m; iter m.mnext)
    in iter dl.mnext
  let fold f dl accu =
    let rec fold m accu = if m == dl then accu else fold m.mnext (f m accu)
    in fold dl.mnext accu
end

(* \subsection{The George-Appel algorithm} *)

(* Below is a straigthforward translation of the pseudo-code at the end
   of the TOPLAS article by George and Appel.  Two bugs were fixed
   and are marked as such.  Please refer to the article for explanations. *)

(* Low-degree, non-move-related nodes *)
let simplifyWorklist = DLinkNode.make SimplifyWorklist

(* Low-degree, move-related nodes *)
let freezeWorklist = DLinkNode.make FreezeWorklist

(* High-degree nodes *)
let spillWorklist = DLinkNode.make SpillWorklist

(* Nodes that have been coalesced *)
let coalescedNodes = DLinkNode.make CoalescedNodes

(* Moves that have been coalesced *)
let coalescedMoves = DLinkMove.make CoalescedMoves

(* Moves whose source and destination interfere *)
let constrainedMoves = DLinkMove.make ConstrainedMoves

(* Moves that will no longer be considered for coalescing *)
let frozenMoves = DLinkMove.make FrozenMoves

(* Moves enabled for possible coalescing *)
let worklistMoves = DLinkMove.make WorklistMoves

(* Moves not yet ready for coalescing *)
let activeMoves = DLinkMove.make ActiveMoves

(* Initialization of all global data structures *)

let init() =
  DLinkNode.clear simplifyWorklist;
  DLinkNode.clear freezeWorklist;
  DLinkNode.clear spillWorklist;
  DLinkNode.clear coalescedNodes;
  DLinkMove.clear coalescedMoves;
  DLinkMove.clear frozenMoves;
  DLinkMove.clear worklistMoves;
  DLinkMove.clear activeMoves

(* Determine if two nodes interfere *)

let interfere n1 n2 =
  if n1.degree < n2.degree
  then list_memq n2 n1.adjlist
  else list_memq n1 n2.adjlist

(* Add an edge to the graph.  Assume edge is not in graph already *)

let addEdge n1 n2 =
  n1.adjlist <- n2 :: n1.adjlist;
  n1.degree  <- 1 + n1.degree;
  n2.adjlist <- n1 :: n2.adjlist;
  n2.degree  <- 1 + n2.degree

(* Apply the given function to the relevant adjacent nodes of a node *)

let iterAdjacent f n =
  list_iter
    (fun n ->
      match n.nstate with
      | SelectStack | CoalescedNodes -> ()
      | _ -> f n)
    n.adjlist

(* Determine the moves affecting a node *)

let moveIsActiveOrWorklist m =
  match m.mstate with
  | ActiveMoves | WorklistMoves -> true
  | _ -> false

let nodeMoves n =
  list_filter moveIsActiveOrWorklist n.movelist

(* Determine whether a node is involved in a move *)

let moveRelated n =
  list_exists moveIsActiveOrWorklist n.movelist

(*i
(* Check invariants *)

let degreeInvariant n =
  let c = ref 0 in
  iterAdjacent (fun n -> incr c) n;
  if !c <> n.degree then
    fatal_error("degree invariant violated by " ^ name_of_node n)

let simplifyWorklistInvariant n =
  if n.degree < num_available_registers.(n.regclass)
  && not (moveRelated n)
  then ()
  else fatal_error("simplify worklist invariant violated by " ^ name_of_node n)

let freezeWorklistInvariant n =
  if n.degree < num_available_registers.(n.regclass)
  && moveRelated n
  then ()
  else fatal_error("freeze worklist invariant violated by " ^ name_of_node n)

let spillWorklistInvariant n =
  if n.degree >= num_available_registers.(n.regclass)
  then ()
  else fatal_error("spill worklist invariant violated by " ^ name_of_node n)

let checkInvariants () =
  DLinkNode.iter
    (fun n -> degreeInvariant n; simplifyWorklistInvariant n)
    simplifyWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant n; freezeWorklistInvariant n)
    freezeWorklist;
  DLinkNode.iter
    (fun n -> degreeInvariant n; spillWorklistInvariant n)
    spillWorklist
i*)

(* Register classes *)

let class_of_type = function Tint -> 0 | Tfloat -> 1

let num_register_classes = 2

let caller_save_registers = [|
  [| R3; R4; R5; R6; R7; R8; R9; R10 |];
  [| F1; F2; F3; F4; F5; F6; F7; F8; F9; F10 |]
|]

let callee_save_registers = [|
  [| R13; R14; R15; R16; R17; R18; R19; R20; R21; R22; 
     R23; R24; R25; R26; R27; R28; R29; R30; R31 |];
  [| F14; F15; F16; F17; F18; F19; F20; F21; F22; 
     F23; F24; F25; F26; F27; F28; F29; F30; F31 |]
|]

let num_available_registers = 
  [| Array.length caller_save_registers.(0)
           + Array.length callee_save_registers.(0);
     Array.length caller_save_registers.(1)
           + Array.length callee_save_registers.(1) |]

(* Build the internal representation of the graph *)

let nodeOfReg r typenv spillcosts =
  let ty = typenv r in
  { ident = r; typ = ty; regclass = class_of_type ty;
    spillcost = (try float(Hashtbl.find spillcosts r) with Not_found -> 0.0);
    adjlist = []; degree = 0; movelist = []; alias = None;
    color = None;
    nstate = Initial;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let nodeOfMreg mr =
  let ty = mreg_type mr in
  { ident = Coq_xH; typ = ty; regclass = class_of_type ty;
    spillcost = 0.0;
    adjlist = []; degree = 0; movelist = []; alias = None;
    color = Some (R mr);
    nstate = Colored;
    nprev = DLinkNode.dummy; nnext = DLinkNode.dummy }

let build g typenv spillcosts =
  (* Associate an internal node to each pseudo-register and each location *)
  let reg_mapping = Hashtbl.create 27
  and mreg_mapping = Hashtbl.create 27 in
  let find_reg_node r =
    try
      Hashtbl.find reg_mapping r
    with Not_found ->
      let n = nodeOfReg r typenv spillcosts in
      Hashtbl.add reg_mapping r n;
      n
  and find_mreg_node mr =
    try
      Hashtbl.find mreg_mapping mr
    with Not_found ->
      let n = nodeOfMreg mr in
      Hashtbl.add mreg_mapping mr n;
      n in
  (* Fill the adjacency lists and compute the degrees. *)
  SetRegReg.fold
    (fun (Coq_pair(r1, r2)) () ->
      addEdge (find_reg_node r1) (find_reg_node r2))
    g.interf_reg_reg ();
  SetRegMreg.fold
    (fun (Coq_pair(r1, mr2)) () ->
      addEdge (find_reg_node r1) (find_mreg_node mr2))
    g.interf_reg_mreg ();
  (* Process the moves and insert them in worklistMoves *)
  let add_move n1 n2 =
    let m =
      { src = n1; dst = n2; mstate = WorklistMoves;
        mnext = DLinkMove.dummy; mprev = DLinkMove.dummy } in
    n1.movelist <- m :: n1.movelist;
    n2.movelist <- m :: n2.movelist;
    DLinkMove.insert m worklistMoves in
  SetRegReg.fold
    (fun (Coq_pair(r1, r2)) () ->
      add_move (find_reg_node r1) (find_reg_node r2))
    g.pref_reg_reg ();
  SetRegMreg.fold
    (fun (Coq_pair(r1, mr2)) () ->
      add_move (find_reg_node r1) (find_mreg_node mr2))
    g.pref_reg_mreg ();
  (* Initial partition of nodes into spill / freeze / simplify *)
  Hashtbl.iter
    (fun r n ->
      assert (n.nstate = Initial);
      let k = num_available_registers.(n.regclass) in
      if n.degree >= k then
        DLinkNode.insert n spillWorklist
      else if moveRelated n then
        DLinkNode.insert n freezeWorklist
      else
        DLinkNode.insert n simplifyWorklist)
    reg_mapping;
  reg_mapping

(* Enable moves that have become low-degree related *)

let enableMoves n =
  list_iter
    (fun m ->
      if m.mstate = ActiveMoves
      then DLinkMove.move m activeMoves worklistMoves)
    (nodeMoves n)

(* Simulate the removal of a node from the graph *)

let decrementDegree n =
  let k = num_available_registers.(n.regclass) in
  let d = n.degree in
  n.degree <- d - 1;
  if d = k then begin
    enableMoves n;
    iterAdjacent enableMoves n;
    if n.nstate <> Colored then begin
      if moveRelated n
      then DLinkNode.move n spillWorklist freezeWorklist
      else DLinkNode.move n spillWorklist simplifyWorklist
    end
  end

(* Simulate the effect of combining nodes [n1] and [n3] on [n2],
   where [n2] is a node adjacent to [n3]. *)

let combineEdge n1 n2 =
  assert (n1 != n2);
  if interfere n1 n2 then begin
    decrementDegree n2
  end else begin
    n1.adjlist <- n2 :: n1.adjlist;
    n2.adjlist <- n1 :: n2.adjlist;
    n1.degree  <- n1.degree + 1
  end

(* Simplification of a low-degree node *)

let simplify () =
  let n = DLinkNode.pick simplifyWorklist in
  (*i Printf.printf "Simplifying %s\n" (name_of_node n); i*)
  n.nstate <- SelectStack;
  iterAdjacent decrementDegree n;
  n

(* Briggs' conservative coalescing criterion *)

let canConservativelyCoalesce n1 n2 =
  let seen = ref Regset.empty in
  let k = num_available_registers.(n1.regclass) in
  let c = ref 0 in
  let consider n =
    if not (Regset.mem n.ident !seen) then begin
      seen := Regset.add n.ident !seen;
      if n.degree >= k then incr c
    end in
  iterAdjacent consider n1;
  iterAdjacent consider n2;
  !c < k

(* Update worklists after a move was processed *)

let addWorkList u =
  if (not (u.nstate = Colored))
  && u.degree < num_available_registers.(u.regclass)
  && (not (moveRelated u))
  then DLinkNode.move u freezeWorklist simplifyWorklist

(* Return the canonical representative of a possibly coalesced node *)

let rec getAlias n =
  match n.alias with None -> n | Some n' -> getAlias n'

(* Combine two nodes *)

let combine u v =
  (*i Printf.printf "Combining %s and %s\n" (name_of_node u) (name_of_node v); i*)
  if v.nstate = FreezeWorklist
  then DLinkNode.move v freezeWorklist coalescedNodes
  else DLinkNode.move v spillWorklist coalescedNodes;
  v.alias <- Some u;
  u.movelist <- u.movelist @ v.movelist;
  iterAdjacent (combineEdge u) v;  (*r original code using [decrementDegree] is buggy *)
  enableMoves v;                   (*r added as per Appel's book erratum *)
  if u.degree >= num_available_registers.(u.regclass)
  && u.nstate = FreezeWorklist
  then DLinkNode.move u freezeWorklist spillWorklist

(* Attempt coalescing *)

let coalesce () =
  let m = DLinkMove.pick worklistMoves in
  let x = getAlias m.src and y = getAlias m.dst in
  let (u, v) = if y.nstate = Colored then (y, x) else (x, y) in
  if u == v then begin
    DLinkMove.insert m coalescedMoves;
    addWorkList u
  end else if v.nstate = Colored || interfere u v then begin
    DLinkMove.insert m constrainedMoves;
    addWorkList u;
    addWorkList v
  end else if canConservativelyCoalesce u v then begin
    DLinkMove.insert m coalescedMoves;
    combine u v;
    addWorkList u
  end else begin
    DLinkMove.insert m activeMoves    
  end

(* Freeze moves associated with node [u] *)

let freezeMoves u =
  let au = getAlias u in
  let freeze m =
    let y = getAlias m.src in
    let v = if y == au then getAlias m.dst else y in
    DLinkMove.move m activeMoves frozenMoves;
    if not (moveRelated v)
    && v.degree < num_available_registers.(v.regclass)
    && v.nstate <> Colored
    then DLinkNode.move v freezeWorklist simplifyWorklist in
  list_iter freeze (nodeMoves u)

(* Pick a move and freeze it *)

let freeze () =
  let u = DLinkNode.pick freezeWorklist in
  (*i Printf.printf "Freezing %s\n" (name_of_node u); i*)
  DLinkNode.insert u simplifyWorklist;
  freezeMoves u

(* Chaitin's cost measure *)

let spillCost n = n.spillcost /. float n.degree

(* Spill a node *)

let selectSpill () =
  (* Find a spillable node of minimal cost *)
  let (n, cost) =
    DLinkNode.fold
      (fun n (best_node, best_cost as best) ->
        let cost = spillCost n in
        if cost < best_cost then (n, cost) else best)
      spillWorklist (DLinkNode.dummy, infinity) in
  assert (n != DLinkNode.dummy);
  DLinkNode.remove n spillWorklist;
  (*i Printf.printf "Spilling %s\n" (name_of_node n); i*)
  freezeMoves n;
  n.nstate <- SelectStack;
  iterAdjacent decrementDegree n;
  n

(* Produce the order of nodes that we'll use for coloring *)

let rec nodeOrder stack =
  (*i checkInvariants(); i*)
  if DLinkNode.notempty simplifyWorklist then
    (let n = simplify() in nodeOrder (n :: stack))
  else if DLinkMove.notempty worklistMoves then
    (coalesce(); nodeOrder stack)
  else if DLinkNode.notempty freezeWorklist then
    (freeze(); nodeOrder stack)
  else if DLinkNode.notempty spillWorklist then
    (let n = selectSpill() in nodeOrder (n :: stack))
  else
    stack

(* Assign a color (i.e. a hardware register or a stack location)
   to a node.  The color is chosen among the colors that are not
   assigned to nodes with which this node interferes.  The choice
   is guided by the following heuristics: consider first caller-save
   hardware register of the correct type; second, callee-save registers;
   third, a stack location.  Callee-save registers and stack locations
   are ``expensive'' resources, so we try to minimize their number
   by picking the smallest available callee-save register or stack location.
   In contrast, caller-save registers are ``free'', so we pick an
   available one pseudo-randomly. *)

module Locset =
  Set.Make(struct type t = loc let compare = compare end)

let start_points = Array.make num_register_classes 0

let find_reg conflicts regclass =
  let rec find avail curr last =
    if curr >= last then None else begin
      let l = R avail.(curr) in
      if Locset.mem l conflicts
      then find avail (curr + 1) last
      else Some l
    end in
  let caller_save = caller_save_registers.(regclass)
  and callee_save = callee_save_registers.(regclass)
  and start = start_points.(regclass) in
  match find caller_save start (Array.length caller_save) with
  | Some _ as res ->
      start_points.(regclass) <-
        (if start + 1 < Array.length caller_save then start + 1 else 0);
      res
  | None ->
      match find caller_save 0 start with
      | Some _ as res ->
          start_points.(regclass) <-
            (if start + 1 < Array.length caller_save then start + 1 else 0);
          res
      | None ->
          find callee_save 0 (Array.length callee_save)

let find_slot conflicts typ =
  let rec find curr =
    let l = S(Local(curr, typ)) in
    if Locset.mem l conflicts then find (coq_Zsucc curr) else l
  in find Z0

let assign_color n =
  let conflicts = ref Locset.empty in
  list_iter
    (fun n' ->
      match (getAlias n').color with
      | None -> ()
      | Some l -> conflicts := Locset.add l !conflicts)
    n.adjlist;
  match find_reg !conflicts n.regclass with
  | Some loc ->
      n.color <- Some loc
  | None ->
      n.color <- Some (find_slot !conflicts n.typ)

(* Extract the location of a node *)

let location_of_node n =
  match n.color with
  | None -> assert false
  | Some loc -> loc

(* Estimate spilling costs - TODO *)

let spill_costs f = Hashtbl.create 7

(* This is the entry point for graph coloring. *)

let graph_coloring (f: coq_function) (g: graph) (env: regenv) (regs: Regset.t)
                   : (reg -> loc) =
  init();
  Array.fill start_points 0 num_register_classes 0;
  let mapping = build g env (spill_costs f) in
  list_iter assign_color (nodeOrder []);
  fun r ->
    try location_of_node (getAlias (Hashtbl.find mapping r))
    with Not_found -> R IT1 (* any location *)
