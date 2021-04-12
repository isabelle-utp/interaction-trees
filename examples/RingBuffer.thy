theory RingBuffer
  imports "../ITree_Circus" "HOL-Library.Code_Target_Nat" "HOL-Library.Code_Target_Int"
begin

no_notation conj  (infixr "&" 35)

lit_vars

type_synonym RingIndex = nat

definition "maxring = (5 :: nat)"

abbreviation "maxbuff \<equiv> (maxring - 1)"

chantype chan =
  "rd" :: "RingIndex \<times> integer"
  "wrt" :: "RingIndex \<times> integer"
  "input" :: "integer"
  "output" :: "integer"

alphabet CellState =
  val :: integer

instantiation CellState_ext :: (default) default
begin

definition default_CellState_ext :: "'a CellState_scheme" where
"default_CellState_ext = CellState.extend (CellState.make 0) default"

instance ..

end

definition "Read(i) = rd!((i,val)) \<rightarrow> Skip"

definition "Write(i) = wrt?(_,v):(map (\<lambda> v. (i, v)) [0,1,2,3]) \<rightarrow> val := v"

definition "IRingCell(i) = proc ([val \<leadsto> 0] :: CellState subst) (Write(i) \<Zcomp> loop (Read(i) \<box> Write(i)))"

definition "Ring = foldl (\<interleave>) (Ret ()) (map (IRingCell \<circ> nat) [0..maxbuff])"

alphabet ControllerState =
  sz :: nat
  ringsize :: integer
  cache :: integer
  rtop :: RingIndex
  rbot :: RingIndex

instantiation ControllerState_ext :: (default) default
begin

definition default_ControllerState_ext :: "'a ControllerState_scheme" where
"default_ControllerState_ext = ControllerState.extend (ControllerState.make 0 0 0 0 0) default"

instance ..

end


definition "InitController = [sz \<leadsto> 0, rbot \<leadsto> 0, rtop \<leadsto> 0]"

definition "CacheInput x = (sz := 1 \<Zcomp> cache := x)"

definition "StoreInput = (sz := (sz + 1) \<Zcomp> rtop := ((rtop + 1) mod maxring))"

definition "InputController = ((sz < maxbuff) & input?(x):[0,1,2,3] \<rightarrow> 
                                ((sz = 0) & CacheInput x 
                                \<box> (sz > 0) & wrt!((rtop, x)) \<rightarrow> StoreInput))"

definition "NoNewCache = (sz := 1)"

definition "StoreNewCache x = sz := (sz - 1) \<Zcomp> cache := x \<Zcomp> rbot := ((rbot + 1) mod maxring)"

definition "OutputController = (sz > 0) & output!(cache) \<rightarrow> 
                                  ((sz > 1) & rd?(_, x):(map (\<lambda> i. (rbot, i)) [0,1,2,3]) \<rightarrow> StoreNewCache x
                                   \<box> (sz = 1) & NoNewCache)"

definition "Controller = proc (InitController :: ControllerState \<Rightarrow> ControllerState) (loop (InputController \<box> OutputController))"

term "[Read_C (i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]] @ [Write_C (i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]]"

definition 
  "CRing = hide (Controller 
           \<parallel>\<^bsub>set ([rd_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]] @ [wrt_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]])\<^esub> 
           Ring) (set ([rd_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]] @ [wrt_C (nat i, v). i \<leftarrow> [0..maxbuff], v \<leftarrow> [0,1,2,3]]))"

export_code Ring Controller CRing in Haskell module_name RingBuffer (string_classes)

end