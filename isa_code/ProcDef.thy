theory ProcDef
  imports ResMapValid ProcHoleVars
begin
  
    (*
      ###### 1. defining well-typed process set ######
    *)
  
type_synonym proc_set = "p_exp state_env"

definition well_typed_proc_set where
  "well_typed_proc_set env delta p_map p_set = (disj_nres_map p_map \<and> (\<forall> u. case p_set u of
    None \<Rightarrow> True
    | Some e \<Rightarrow> (case p_map u of
      None \<Rightarrow> False
      | Some r_s \<Rightarrow> (\<exists> rx r_s2. well_typed env delta r_s e UnitTy r_s2 rx))
  ))"

    (*
      ###### 2. defining system reduction / well-typed system  ######
    *)
  
datatype red_act =
  ThreadAct
  | ForkAct
  | SendAct    
  
fun red_proc_set :: "p_state \<times> proc_set \<Rightarrow> red_act \<Rightarrow> p_state \<times> proc_set \<Rightarrow> bool" where
  "red_proc_set (s1, ps1) ThreadAct (s2, ps2) = (\<exists> are u e1 e2 ax. ps1 u = Some e1 \<and>
    full_red_exp are (s1, e1) ax (s2, e2) \<and> ps2 = add_env ps1 u e2)"
(*\<exists> are u h e1 e2 ax. ps1 u = Some (app_hole h e1) \<and> wf_hole h \<and>
    app_red_exp are (s1, e1) ax (s2, e2) \<and> ps2 = add_env ps1 u (app_hole h e2)*)
| "red_proc_set (s1, ps1) ForkAct (s2, ps2) = (\<exists> u h e v. ps1 u = Some (app_hole h (AppExp (ConstExp ForkConst) e)) \<and>
    wf_hole h \<and> is_value e \<and> ps2 = add_env (add_env ps1 u (app_hole h (ConstExp UnitConst))) v (AppExp e (ConstExp UnitConst)) \<and>
  fresh_var ps1 v \<and> s1 = s2)"
| "red_proc_set (s1, ps1) SendAct (s2, ps2) = (\<exists> u1 u2 h1 h2 x_s x_r v.
    ps1 u1 = Some (app_hole h1 (AppExp (AppExp (ConstExp SendConst) (VarExp (LocType x_s))) v)) \<and>
    ps1 u2 = Some (app_hole h2 (AppExp (ConstExp RecvConst) (VarExp (LocType x_r)))) \<and>
    u1 \<noteq> u2 \<and> wf_hole h1 \<and> wf_hole h2 \<and> is_value v \<and>
    s1 x_s = Some ChanSValue \<and> s1 x_r = Some (ChanRValue x_s) \<and>
    ps2 = add_env (add_env ps1 u1 (app_hole h1 (ConstExp UnitConst))) u2 (app_hole h2 v) \<and> s1 = s2)"

definition well_typed_system where
  "well_typed_system env delta p_map s p_set = (well_typed_state s env delta \<and> well_typed_proc_set env delta p_map p_set \<and> sub_nres_map s p_map)"
  
fun fork_reduce where
  "fork_reduce (s1, AppExp (ConstExp ForkConst) e) ax (s2, ConstExp UnitConst) = (s1 = s2 \<and> ax = NoAct)"
| "fork_reduce (s1, e1) ax (s2, e2) = False"    
  
end