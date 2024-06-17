section \<open> Distributed Ring Buffer \<close>

theory RingBuffer                                               
  imports "ITree_UTP.ITree_Circus" "ITree_Simulation.ITree_Simulation"
begin lit_vars

no_notation conj  (infixr "&" 35) lit_vars

subsection \<open> Ring Process \<close>

type_synonym RingIndex = nat

definition "maxring = (5000 :: nat)"

abbreviation "maxbuff \<equiv> (maxring - 1)"

chantype chan =
  "rd" :: "RingIndex \<times> int"
  "wrt" :: "RingIndex \<times> int"
  "input" :: "int"
  "output" :: "int"

setup \<open> Show_Channel.mk_chan_show_inst "chan" ["rd", "wrt", "input", "output"] \<close>

zstore CellState =
  val :: int

definition Read :: "nat \<Rightarrow> (chan, CellState) action" where
"Read(i) = rd!((i,val)) \<rightarrow> Skip"

definition Write :: "nat \<Rightarrow> (chan, CellState) action" where
"Write(i) = wrt?(_,v):(set(map (\<lambda> v. (i, v)) [0,1,2,3])) \<rightarrow> val := v"

definition Cell :: "nat \<Rightarrow> chan process" where
"Cell(i) = process ([val \<leadsto> 0] :: CellState subst) (Write(i) ;; loop (Read(i) \<box> Write(i)))"

definition Ring :: "chan process" where
"Ring = foldl (\<interleave>) (Ret ()) (map (Cell \<circ> nat) [0..maxbuff])"

subsection \<open> Controller Process \<close>

zstore ControllerState =
  sz       :: nat
  ringsize :: int
  cache    :: int
  rtop     :: RingIndex
  rbot     :: RingIndex

definition InitController :: "ControllerState subst" where
"InitController = [sz \<leadsto> 0, rbot \<leadsto> 0, rtop \<leadsto> 0]"

definition CacheInput :: "int \<Rightarrow> (chan, ControllerState) action" where
"CacheInput x = (sz := 1 ;; cache := x)"

definition StoreInput :: "(chan, ControllerState) action" where
"StoreInput = (sz := (sz + 1) ;; rtop := ((rtop + 1) mod maxring))"

definition InputController :: "(chan, ControllerState) action" where
  "InputController = ((sz < maxbuff) & input?(x):(set [0,1,2,3]) \<rightarrow> 
                                (((sz = 0) & CacheInput x)
                                \<box> ((sz > 0) & wrt!((rtop, x)) \<rightarrow> StoreInput)))"

definition NoNewCache :: "(chan, ControllerState) action" where
"NoNewCache = (sz := 0)"

definition StoreNewCache :: "int \<Rightarrow> (chan, ControllerState) action" where
"StoreNewCache x = sz := (sz - 1) ;; cache := x ;; rbot := ((rbot + 1) mod maxring)"

definition OutputController :: "(chan, ControllerState) action" where 
  "OutputController = ((sz > 0) & output!(cache) \<rightarrow> 
                                  (((sz > 1) & rd?(_, x):(set (map (\<lambda> i. (rbot, i)) [0,1,2,3])) \<rightarrow> StoreNewCache x)
                                   \<box> ((sz = 1) & NoNewCache)))"

definition Controller :: "chan process" where
"Controller = anim_process (InitController :: ControllerState \<Rightarrow> ControllerState) (loop (InputController \<box> OutputController))"

definition CRing :: "chan process" where
  "CRing = hide (Controller 
           \<parallel>\<^bsub>set ([rd_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]] @ [wrt_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]])\<^esub> 
           Ring) (set ([rd_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]] @ [wrt_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]]))"

animate CRing

end