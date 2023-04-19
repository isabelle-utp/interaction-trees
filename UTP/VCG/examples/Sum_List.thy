section \<open> Summing a List \<close>

theory Sum_List
  imports "ITree_VCG.ITree_VCG"
begin 

zstore state =
  i :: nat
  x :: int
  a :: int

procedure sum_up "(xs :: int list)"
  = "i := 0; x := 0;
     while i < length xs 
       invariant x = sum_list (take i xs) 
       variant length xs - i do
       x := x + xs!i;
       i := i + 1
     od"

lemma sum_up_correct: "H[True] sum_up xs [x = sum_list xs]"
  apply vcg
  apply (smt (verit, del_insts) Cons_nth_drop_Suc append_take_drop_id sum_list.Cons sum_list_append)
  done

end