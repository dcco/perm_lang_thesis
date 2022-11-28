theory ReduceExp
  imports ReduceSetOwn
begin
  
    (* 
      ####################################
        P3. reduction
      ####################################
    *)  
 
    (* memory values *)
  
datatype mem_value =
  ArrValue "p_exp list"
  | ChanSValue
  | ChanRValue string
  
type_synonym p_state = "mem_value state_env"  
  
fun app_op :: "p_op \<Rightarrow> p_const \<Rightarrow> p_exp \<Rightarrow> bool" where
  "app_op (I2Op f2) c e' = (\<exists> i. c = IConst i \<and> e' = OpExp (I1Op (f2 i)))"
| "app_op (I1Op f1) c e' = (\<exists> i. c = IConst i \<and> e' = ConstExp (IConst (f1 i)))"
| "app_op (C2Op f2) c e' = (\<exists> i. c = IConst i \<and> e' = OpExp (C1Op (f2 i)))"
| "app_op (C1Op f1) c e' = (\<exists> i. c = IConst i \<and> e' = ConstExp (BConst (f1 i)))"
| "app_op (R2Op f2) c e' = (\<exists> b. c = BConst b \<and> e' = OpExp (R1Op (f2 b)))"
| "app_op (R1Op f1) c e' = (\<exists> b. c = BConst b \<and> e' = ConstExp (BConst (f1 b)))"
  
fun new_array_dat :: "int \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "new_array_dat i v = (if i \<le> 0 then [] else v # (new_array_dat (i - 1) v))"  
  
definition new_array :: "int \<Rightarrow> p_exp \<Rightarrow> mem_value" where
  "new_array i v = (ArrValue (new_array_dat i v))"    
  
fun read_array where
  "read_array [] i = None"
| "read_array (v # t) i = (if i = 0 then Some v else read_array t (i - 1))"
  
fun write_array where
  "write_array [] i v' = None"
| "write_array (v # t) i v' = (if i = 0 then Some (v' # t) else (case (write_array t (i - 1) v') of
    None \<Rightarrow> None
  | Some t' \<Rightarrow> Some (v # t')
  ))"
  
    (* in order to ensure that ownership transfer is safe, we require aggressive removal of permissions once
      they are no longer needed. for this reason, every use is tracked as an action.  *)
datatype p_act =
    (* - nothing *)
  NoAct
    (* - new resource, ##resources consumed to create the resource *)
  | MakeAct string (*"string set"*)
  | Mk2Act string string
    (* - resource used, ##resources transferred to the resource *)
  | UseAct string (*"string set"*)
  
fun ext_list where
  "ext_list [] v = [v]"
| "ext_list (v' # t) v = v' # (ext_list t v)"  
  
fun new_arr_value :: "nat \<Rightarrow> p_exp list" where
  "new_arr_value 0 = []"
| "new_arr_value n = ((ConstExp NullConst) # (new_arr_value (n - 1)))"
  
fun app_con :: "p_state \<Rightarrow> p_const \<Rightarrow> p_exp \<Rightarrow> p_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> bool" where
  "app_con s NewArrayConst v ax (s', e') = (\<exists> i a. ax = MakeAct a \<and> v = ConstExp (IConst i) \<and>
    e' = VarExp (LocType a) \<and> s' = add_env s a (ArrValue (new_arr_value (nat i))) \<and> fresh_var s a
  )"
| "app_con s NewChanConst v ax (s', e') = (\<exists> c_s c_r. ax = Mk2Act c_s c_r \<and> v = ConstExp UnitConst \<and>
    e' = (PairExp (VarExp (LocType c_s)) (VarExp (LocType c_r))) \<and> s' = add_env (add_env s c_s ChanSValue) c_r (ChanRValue c_s) \<and>
    fresh_var s c_s \<and> fresh_var s c_r \<and> c_s \<noteq> c_r)"
| "app_con s UnpackConst v ax (s', e') = (\<exists> v1 v2 f. ax = NoAct \<and> v = PairExp v1 v2 \<and> s' = s \<and>
    e' = (LamExp f (AppExp (AppExp (VarExp (VarType f)) v1) v2)) \<and> f \<notin> free_vars v \<and> f \<notin> ref_vars v)"
| "app_con s c v a (s', e') = False"
  
definition unit_exp where
  "unit_exp = ConstExp UnitConst"  
  
fun app_cv :: "p_state \<Rightarrow> p_const \<Rightarrow> p_exp \<Rightarrow> p_exp \<Rightarrow> p_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> bool" where
  "app_cv s ReadConst e ix ax (s', e') = (\<exists> a i v arr. e = VarExp (LocType a) \<and> ix = ConstExp (IConst i) \<and>
    ax = UseAct a \<and> s a = Some (ArrValue arr) \<and>
    read_array arr i = Some v \<and> e' = v \<and> s' = s)"(*
| "app_cv s ExtArrayConst e v ax (s', e') = (\<exists> a arr. e = VarExp (LocType a) \<and>
    ax = UseAct a \<and> s a = Some (ArrValue arr) \<and>
    e' = e \<and> s' = add_env s a (ArrValue (ext_list arr v)))"*)
| "app_cv s WriteConst e p ax (s', e') = (\<exists> a i v arr arr'. e = VarExp (LocType a) \<and>
    p = PairExp (ConstExp (IConst i)) v \<and> ax = UseAct a \<and>
    s a = Some (ArrValue arr) \<and> Some arr' = write_array arr i v \<and>
    e' = unit_exp \<and> s' = add_env s a (ArrValue arr'))"
| "app_cv s c v1 v2 ax (s', e') = False"  
  
  
datatype app_act =
  LamApp
  | FixApp
  | ConstApp
  | OpApp
  | IfApp1
  | IfApp2
  | CVApp
  (*| UnpackApp*)
  
fun app_red_exp :: "app_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> p_act \<Rightarrow> p_state \<times> p_exp \<Rightarrow> bool" where
  "app_red_exp LamApp (s, e) a (s', e') = (\<exists> x ex v.
    e = AppExp (LamExp x ex) v \<and> a = NoAct \<and> is_value v \<and> safe_subst_exp ex x v e' \<and> s = s')"
| "app_red_exp FixApp (s, e) a (s', e') = (\<exists> x ex. e = AppExp (ConstExp FixConst) (LamExp x ex) \<and>
  a = NoAct \<and> safe_subst_exp ex x (AppExp (ConstExp FixConst) (LamExp x ex)) e' \<and> s = s')"
| "app_red_exp OpApp (s, e) a (s', e') = (\<exists> xop c. e = AppExp (OpExp xop) (ConstExp c) \<and>
  a = NoAct \<and> app_op xop c e' \<and> s = s')"
| "app_red_exp ConstApp (s, e) a (s', e') = (\<exists> c v. e = AppExp (ConstExp c) v \<and>
  is_value v \<and> app_con s c v a (s', e'))"
| "app_red_exp CVApp (s, e) a (s', e') = (\<exists> c v1 v2. e = AppExp (AppExp (ConstExp c) v1) v2 \<and>
  bin_const c \<and> is_value v1 \<and> is_value v2 \<and> app_cv s c v1 v2 a (s', e'))"
| "app_red_exp IfApp1 (s, e) a (s', e') = (\<exists> e1 e2. e = IfExp (ConstExp (BConst True)) e1 e2 \<and>
  a = NoAct \<and> e' = e1 \<and> s = s')"
| "app_red_exp IfApp2 (s, e) a (s', e') = (\<exists> e1 e2. e = IfExp (ConstExp (BConst False)) e1 e2 \<and>
  a = NoAct \<and> e' = e2 \<and> s = s')"
  
end