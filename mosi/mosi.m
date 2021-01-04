--Directory based 3-Hop MSI protocol

-------------------------------------------------------------
-- Constants
-------------------------------------------------------------
const
  ProcCount: 3;     --number of processors
  ValueCount: 2;    --number of data values
  VC0: 0;
  VC1: 2;
  NumVCs: VC1 - VC0 + 1;
  NetMax: ProcCount+100;

------------------------------------------------------------
-- Types
------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   --unordered range of processors
  Value: scalarset(ValueCount);  --arbitary values for tracking coherence
  Home: enum { HomeType };      -- need enumeration for isMember calls
  Node: union { Home, Proc };

  VCType: VC0..NumVCs-1;
  CountType: 0..ProcCount;

  MessageType: enum {
                  data,
                  ackdata,

                  GetS,    --request for data (Move into Shared state)
                  PutS,    --ack for read request

                  GetM,   --request for write (move to modified state)
                  PutM,   --write ack 

                  ackCount,
                  PutO,

                  PutAck,
                  PutAckM,

                  OData,
                  Sack,
                  Mack,

                  FwdGetM,
                  FwdGetS,

                  Invreq,     --request to evict block/line
                  InvAck
              };

Message:
  Record
    mtype: MessageType;
    dst: Node;
    src: Node;
    --destination can be found by the net the packet is attached to
    vc: VCType;
    val: Value;
    fwd: Node;
    cnt: CountType;
  End;

HomeState:
  Record
    state: enum {
      H_Invalid, H_Shared, H_Modified, H_Owner,   --stable states
      H_SA, H_MA, H_OA          --transient
    };
    owner: Node;
    sharers: multiset [ProcCount] of Node;
    val: Value;
  End;

ProcState:
  Record
    state: enum{
        P_Invalid, P_Shared, P_Modified, P_Owner,              --stable states
        ISD, IMAD, IMA, SMAD, SMA, MIA, OMAC, OMA, OIA, SIA, IIA      --transient states
        };
    val: Value;
    cnt: CountType;
    totalacks: CountType;
  End;


------------------------------------------------------------------------
-- Variables
------------------------------------------------------------------------
var 
  HomeNode: HomeState;
  Procs: array[Proc] of ProcState;
  Net: array [Node] of multiset[NetMax] of Message;
  InBox: array [Node] of array [VCType] of Message; -- If a message is not processed, it is placed in InBox, blocking that virtual channel
  msg_processed: boolean;
  LastWrite: Value;

----------------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------------
Procedure Send(mtype: MessageType;
          dst: Node;
          src: Node;
          vc:VCType;
          val: Value;
          fwd: Node;
          cnt: CountType;
          );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.dst   := dst;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.fwd   := fwd;
  msg.cnt   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg: Message; n:Node);
Begin
  put "\n" ;
  put msg.src ;
  if msg.src = HomeType
  then
    put HomeNode.state;
  else
    put Procs[msg.src].state;
  endif;
  if n = HomeType
  then
    put HomeNode.state;
  else
    put Procs[n].state;
  endif;
  put msg.mtype;
  error "Unhandled message type!"; 
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Procedure ClearSharersList();
Begin
    for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
      then
        MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
    endif;
  endfor;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount (i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        Send(Invreq, n, HomeType, VC1, UNDEFINED, rqst, UNDEFINED);
      endif;
    endif;
  endfor;
End;


---------------------------------------------------------------------------
-- Home Communication
--------------------------------------------------------------------------

Procedure HomeReceive(msg: Message);
var cnt:0..ProcCount;   -- for counting sharers
Begin
  cnt := MultiSetCount(i:HomeNode.sharers, true);
  msg_processed :=  true;

  switch HomeNode.state
  case H_Invalid:
    switch msg.mtype

    case GetS:
      HomeNode.state  := H_SA;
      Send(ackdata, msg.src, HomeType, VC0, HomeNode.val, msg.src, UNDEFINED);
      AddToSharersList(msg.src);
    case GetM:
      HomeNode.state  := H_MA;
      HomeNode.owner  := msg.src;
      Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, cnt);
    case PutS:
      Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
    case PutM:
      if HomeNode.owner != msg.src
      then 
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
        endif;
    case PutO:
      if HomeNode.owner != msg.src
      then 
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
        endif;
    case Sack:
    case Mack:
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_Shared:
    switch msg.mtype
    case GetS:
      AddToSharersList(msg.src);
      Send(ackdata, msg.src, HomeType, VC0, HomeNode.val, msg.src, UNDEFINED);
      HomeNode.state := H_SA;
    case GetM:
      if (cnt = 1 & IsSharer(msg.src))
      then
        Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, 0);
        else
        if IsSharer(msg.src)
        then
          Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, cnt-1);
          else
          Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, cnt);
        endif;
      endif;
      SendInvReqToSharers(msg.src);
      ClearSharersList();
      HomeNode.owner  := msg.src;
      HomeNode.state := H_MA;
    case PutS:
      RemoveFromSharersList(msg.src);
      Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
      if cnt = 0
      then 
        HomeNode.state := H_Invalid;
      endif;
    case PutM:
      if HomeNode.owner != msg.src
      then 
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
      endif;
    case PutO:
      if HomeNode.owner != msg.src
      then 
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
      endif;
    case Sack:
    case Mack:
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_Owner:
    switch msg.mtype
    case GetS:
      Send(FwdGetS, HomeNode.owner, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
      AddToSharersList(msg.src);
      HomeNode.state := H_OA;
    case GetM:
      if HomeNode.owner != msg.src
      then
        Send(FwdGetM, HomeNode.owner, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
        if IsSharer(msg.src)
        then
          Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, cnt);
          else
          Send(ackCount, msg.src, HomeType, VC1, HomeNode.val, msg.src, cnt+1);
        endif;
        HomeNode.owner := msg.src;
        --HomeNode.state := H_Modified;
      else  
        Send(ackCount, msg.src, HomeType, VC1, UNDEFINED, msg.src, cnt);
      endif;
      HomeNode.state := H_MA;
      SendInvReqToSharers(msg.src);
      ClearSharersList();
    case PutS:
      RemoveFromSharersList(msg.src);
      Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
    case PutM:
      if HomeNode.owner = msg.src
      then
        HomeNode.state := H_Shared;
        HomeNode.val := msg.val;
        undefine HomeNode.owner
        else
          Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
      endif;
      --if HomeNode.owner = msg.src
      --then
      --  HomeNode.state := H_Shared;
      --  HomeNode.val := msg.val;
      --  undefine HomeNode.owner
      --endif;
      --RemoveFromSharersList(msg.src);
      --Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
    case PutO:
      if HomeNode.owner = msg.src
      then
        HomeNode.state := H_Shared;
        HomeNode.val := msg.val;
        undefine HomeNode.owner
      else
        RemoveFromSharersList(msg.src);
      endif;
      Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, msg.src, UNDEFINED);
    case Sack:
    case Mack:
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_Modified:
    switch msg.mtype
    case GetS:
      Send(FwdGetS, HomeNode.owner, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
      AddToSharersList(msg.src);
      HomeNode.state := H_OA;
    case GetM:
      --Send(ackCount, msg.src, HomeType, VC1, UNDEFINED, msg.src, cnt);
      Send(OData, HomeNode.owner, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
      HomeNode.owner := msg.src;
      HomeNode.state := H_MA;
    case PutS:
      Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
    case PutM:
      if HomeNode.owner != msg.src
      then 
        Send(OData, msg.src, HomeType, VC1, UNDEFINED, HomeNode.owner, UNDEFINED);
      else
        HomeNode.state := H_Invalid;
        Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
        HomeNode.val := msg.val;
        undefine HomeNode.owner
      endif;
    case PutO:
      Send(PutAck, msg.src, HomeType, VC0, UNDEFINED, msg.src, UNDEFINED);
    case InvAck:
    case Sack:
    case Mack:
    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_SA:
    switch msg.mtype
    case Sack:
      HomeNode.state := H_Shared;
    case GetM:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    case PutM:
      msg_processed := false;
    case PutS:
      msg_processed := false;
    case PutO:
      msg_processed := false;
    case Mack:
    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_MA:
    switch msg.mtype
    case Mack:
      HomeNode.state := H_Modified;
    case GetM:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    case PutM:
      msg_processed := false;
    case PutS:
      msg_processed := false;
    case PutO:
      msg_processed := false;
    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_OA:
    switch msg.mtype
    case Sack:
      HomeNode.state := H_Owner;
    case GetM:
      msg_processed := false;
    case GetS:
      msg_processed := false;
    case PutM:
      msg_processed := false;
    case PutS:
      msg_processed := false;
    case PutO:
      msg_processed := false;
    case Mack:
    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  endswitch;
End;

---------------------------------------------------------------------------
-- Processor Communication
--------------------------------------------------------------------------

Procedure ProcReceive(msg:Message; p:Proc);
var ncount : 0..ProcCount;                      --for counting total acks received
Begin
  msg_processed := true;
  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pc:Procs[p].cnt do
  alias pt:Procs[p].totalacks do
  switch ps

  case P_Invalid:
  switch msg.mtype
    case Invreq:
    case FwdGetM:
    case FwdGetS:
    case PutAckM:
      else
    ErrorUnhandledMsg(msg, p);
  endswitch;

  case ISD:
    switch msg.mtype
    case FwdGetM:
    case FwdGetS:
    case Invreq:
    	msg_processed := false; -- stall message in InBox
    case ackdata:
      Send(Sack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
      ps := P_Shared;
      pv := msg.val;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case IMAD:
  switch msg.mtype
    case FwdGetS:
      msg_processed := false; -- stall message in InBox
    case FwdGetM:
      msg_processed := false; -- stall message in InBox
    case OData:
      msg_processed := false; -- stall message in InBox
    case ackCount:
      pt := msg.cnt;
      if msg.cnt = 0
      then
        pv := msg.val;
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      else
        if pc = pt
        then
          ps := P_Modified;
          Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
          pt := 3;
          pc := 0;
        else
          ps := IMA;
        endif;
      endif;
    case ackdata:
      pv := msg.val;
      pc := pc + 1;
    case InvAck:
    case Invreq:

    else
    ErrorUnhandledMsg(msg, p);
  endswitch;

  case IMA:
  switch msg.mtype
    case FwdGetS:
      msg_processed := false; -- stall message in InBox
    case FwdGetM:
      msg_processed := false; -- stall message in InBox
    case OData:
      msg_processed := false; -- stall message in InBox
    case ackdata:                                --not sure about this, need to count inv acks from sharer list
      pc := pc + 1;
      if pc = pt
      then
        pv := msg.val;
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      endif;
    case InvAck:
  else
    ErrorUnhandledMsg(msg, p);
  endswitch;
    
  case P_Shared:
    switch msg.mtype
    case Invreq:
      ps := P_Invalid;
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      Undefine pv
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case SMAD:
    switch msg.mtype
    case FwdGetS:
      msg_processed := false; -- stall message in InBox
    case FwdGetM:
      msg_processed := false; -- stall message in InBox
    case OData:
      msg_processed := false; -- stall message in InBox
    case Invreq:
      ps := IMAD;
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      Undefine pv
    case InvAck:
    case ackCount:
      --pv := msg.val;
      pt := msg.cnt;
      if msg.cnt = 0
      then
        pv := msg.val;
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      else
        if pc = pt
        then
          ps := P_Modified;
          Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
          pt := 3;
          pc := 0;
        else
          ps := SMA;
        endif;
      endif;
    case ackdata:
      pv := msg.val;
      pc := pc + 1;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case SMA:
    switch msg.mtype
    case FwdGetS:
      msg_processed := false; -- stall message in InBox
    case FwdGetM:
      msg_processed := false; -- stall message in InBox
    case OData:
      msg_processed := false; -- stall message in InBox
    case Invreq:
      Send(ackdata, msg.fwd, p, VC1, msg.val, p, UNDEFINED);
    case InvAck:
    case ackdata:                                --not sure about this, need to count inv acks from sharer list
      pv := msg.val;
      pc := pc + 1;
      if pc = pt
      then
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      endif;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case P_Modified:
    switch msg.mtype
    case FwdGetS:
      Send(ackdata, msg.fwd, p, VC0, pv, p, UNDEFINED);
      ps := P_Owner;
    case FwdGetM:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := P_Invalid;
      Undefine pv;
    case OData:
      Send(ackCount, msg.fwd, p, VC1, pv, p, 0);
      ps := P_Invalid;
      Undefine pv;
    case  ackdata:
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  
  case MIA:
    switch msg.mtype
    case FwdGetS:
      Send(ackdata, msg.fwd, p, VC0, pv, p, UNDEFINED);
      ps := OIA;
    case FwdGetM:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := IIA;
    case PutAck:
      ps := P_Invalid;
      undefine pv;
    case PutAckM:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := P_Invalid;
      Undefine pv;
    case OData:
      Send(ackCount, msg.fwd, p, VC1, pv, p, 0);
      ps := IIA;
    case Invreq:
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case P_Owner:
    switch msg.mtype
    case FwdGetS:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
    case FwdGetM:
      ps := P_Invalid;
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      undefine pv
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case OMAC:
    switch msg.mtype
    case FwdGetS:
      --msg_processed := false;
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
    case FwdGetM:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := IMAD;
    case ackCount:
      pt := msg.cnt;
      if msg.cnt = 0
      then
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      else
        if pc = pt
        then
          ps := P_Modified;
          Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
          pt := 3;
          pc := 0;
        else
          ps := OMA;
        endif;
      endif;
    case ackdata:
      pc := pc + 1;
    case OData:
      msg_processed := false;
    case Invreq:
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case OMA:
    switch msg.mtype
    case FwdGetS:
      msg_processed := false;
      --Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
    case FwdGetM:
      msg_processed := false; 
    case ackdata:                                --not sure about this, need to count inv acks from sharer list
      pc := pc + 1;
      if pc = pt
      then
        ps := P_Modified;
        Send(Mack, HomeType, p, VC1, UNDEFINED, p, UNDEFINED);
        pt := 3;
        pc := 0;
      endif;
    case OData:
      msg_processed := false;
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case OIA:
    switch msg.mtype
    case FwdGetS:
      Send(ackdata, msg.fwd, p, VC0, pv, p, UNDEFINED);
    case FwdGetM:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := IIA;
    case OData:
    case PutAckM:
      ps := P_Invalid;
      undefine pv
    case PutAck:
      ps := P_Invalid;
      undefine pv
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

    case SIA:
    switch msg.mtype
    case Invreq:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
      ps := IIA;
    case FwdGetM:
    case PutAckM:
      ps := P_Invalid;
      undefine pv
    case PutAck:
      ps := P_Invalid;
      undefine pv
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  case IIA:
    switch msg.mtype
    case FwdGetS:
      Send(ackdata, msg.fwd, p, VC1, pv, p, UNDEFINED);
    case OData:
    case PutAck:
      ps := P_Invalid;
      undefine pv
    case PutAckM:
      ps := P_Invalid;
      undefine pv
    else
      ErrorUnhandledMsg(msg, p);
    endswitch

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();
  
  endswitch;
  endalias;
  endalias;
  endalias;
  endalias;
End;


---------------------------------------------------------------------------
-- Rules
---------------------------------------------------------------------------
-- Processor actions (challenge coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do

	ruleset v:Value Do
  	rule "store in M"
   	 (p.state = P_Modified)
    	==>
 		   p.val := v;      
 		   LastWrite := v;
  	endrule;
	endruleset;

  rule "store in O"
   	 (p.state = P_Owner)
    	==>
 		   Send(GetM, HomeType, n, VC0, UNDEFINED, n, UNDEFINED);
 		   p.state := OMAC;
  	endrule;

  rule "load in I"
    p.state = P_Invalid 
  ==>
    Send(GetS, HomeType, n, VC0, UNDEFINED, n, UNDEFINED);
    p.state := ISD;
  endrule;

  rule "store in I"
    p.state = P_Invalid
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, n, UNDEFINED);
    p.state := IMAD;
  endrule;

  rule "store in s"
    p.state = P_Shared
  ==>
    Send(GetM, HomeType, n, VC0, UNDEFINED, n, UNDEFINED);
    p.state := SMAD;
  endrule;

  rule "writeback from S"
    p.state = P_Shared
  ==>
    Send(PutS, HomeType, n, VC0, UNDEFINED, n, UNDEFINED);
    p.state := SIA;
  endrule;

  rule "writeback from M"
    p.state = P_Modified
  ==>
    Send(PutM, HomeType, n, VC0, p.val, n, UNDEFINED);
    p.state := MIA;
  endrule;

  rule "writeback from O"
    p.state = P_Owner
  ==>
    Send(PutO, HomeType, n, VC0, p.val, n, UNDEFINED);
    p.state := OIA;
  endrule;

  endalias;
endruleset;

--------------------------------------------------------------------------
-- Message delivery
--------------------------------------------------------------------------
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do
    alias box:InBox[n] do
    -- Pick a random message in the network and deliver it
    rule "receive-net"
			(isundefined(box[msg.vc].mtype))
    ==>
      if IsMember(n, Home)
      then
        HomeReceive(msg);
      else
        ProcReceive(msg, n);
			endif;

			if ! msg_processed
			then
				-- The node refused the message, stick it in the InBox to block the VC.
	  		box[msg.vc] := msg;
			endif;
	  
		  MultiSetRemove(midx, chan);
	  
    endrule;
  
    endalias
    endalias;
    endalias;
  endchoose;  
    
-- Try to deliver a message from a blocked VC; perhaps the node can handle it now
ruleset vc:VCType do
  rule "receive-blocked-vc"
    (! isundefined(InBox[n][vc].mtype))
  ==>
    if IsMember(n, Home)
    then
      HomeReceive(InBox[n][vc]);
    else
      ProcReceive(InBox[n][vc], n);
    endif;

    if msg_processed
    then
      -- Message has been handled, forget it
      undefine InBox[n][vc];
    endif;
  
  endrule;
endruleset;

endruleset;


----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

	For v:Value do
  -- home node initialization
  HomeNode.state := H_Invalid;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initialization
  for i:Proc do
    Procs[i].state := P_Invalid;
    undefine Procs[i].val;
    Procs[i].cnt := 0;
    Procs[i].totalacks := 3;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;




----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_Invalid
    ->
      IsUndefined(HomeNode.owner);

invariant "value in memory matches value of last write, when invalid"
     HomeNode.state = H_Invalid 
    ->
			HomeNode.val = LastWrite;
	
invariant "modified implies empty sharers list"
  HomeNode.state = H_Modified
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_Invalid
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "values in memory matches value of last write, when shared or invalid"
  Forall n : Proc Do	
     HomeNode.state = H_Shared | HomeNode.state = H_Invalid
    ->
			HomeNode.val = LastWrite
	end;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_Shared & Procs[n].state = P_Shared
    ->
			HomeNode.val = Procs[n].val
	end;

invariant "invalid means value doesn't exist in proc"
  Forall n : Proc Do	
     Procs[n].state = P_Invalid
     ->
      IsUndefined(Procs[n].val)
  end;












    