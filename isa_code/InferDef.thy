theory InferDef
  imports AltFlatLemma InferVar
begin
    
    (* type inferencing constraints *)
  
datatype perm_crn =
  UnifyCrn s_type s_type
  (*| MemValCrn s_type s_type*)
  | LeqCrn x_perm s_perm
  | LeqTypeCrn s_type s_perm
  (*| EqTypeCrn s_type s_perm*)
  | DisjCrn x_perm x_perm
  | SemiDisjCrn x_perm x_perm
  
    (* constant / op "types":  *)
  
fun list_contain where
  "list_contain [] x = False"  
| "list_contain (y # t) x = (x = y \<or> list_contain t x)"    
                                                                                                
fun fresh_in_list where
  "fresh_in_list [] = True"
| "fresh_in_list (x # t) = (\<not> list_contain t x \<and> fresh_in_list t)"  
  
definition fresh_list where
  "fresh_list ds l = (fresh_in_list l \<and> (\<forall> x. list_contain l x \<longrightarrow> x \<notin> ds))" 
  
fun const_scheme :: "p_const \<Rightarrow> nat set \<Rightarrow> s_type \<Rightarrow> perm_crn list \<Rightarrow> nat set \<Rightarrow> bool" where
  "const_scheme UnitConst ds tau c_list ds' = (tau = UnitScheme \<and> c_list = [] \<and> ds' = ds)"
| "const_scheme (IConst i) ds tau c_list ds' = (tau = IntScheme \<and> c_list = [] \<and> ds' = ds)"
| "const_scheme (BConst b) ds tau c_list ds' = (tau = BoolScheme \<and> c_list = [] \<and> ds' = ds)"
| "const_scheme FixConst ds tau c_list ds' = (\<exists> t t1 t2 p q. tau = pure_fun_s (pure_fun_s t t (AffVar q)) t (AffConst Prim) \<and>
  t = FunScheme (VarScheme t1) (VarScheme t2) (SVar p) (AffVar q) \<and> c_list = [LeqTypeCrn t (SPerm UsePerm)] \<and>
  fresh_list ds [t1, t2, p, q] \<and> ds' =  {t1, t2, p, q} \<union> ds )"
(*| "const_scheme EmptyArrayConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s UnitScheme (ArrayScheme (VarScheme t)) (AffConst Prim) \<and>
  c_list = [LeqTypeCrn (VarScheme t) (SPerm UsePerm)] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme ExtArrayConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s (ArrayScheme (VarScheme t))
  (FunScheme (VarScheme t) (ArrayScheme (VarScheme t)) (SPerm OwnPerm) (AffConst Ref)) (AffConst Prim) \<and>
  c_list = [LeqTypeCrn (VarScheme t) (SPerm UsePerm)] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"*)
| "const_scheme NewArrayConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s IntScheme (ArrayScheme (VarScheme t)) (AffConst Prim) \<and>
  c_list = [LeqTypeCrn (VarScheme t) (SPerm UsePerm)] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme NullConst ds tau c_list ds' = (\<exists> t. tau = VarScheme t \<and> c_list = [] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds )"
| "const_scheme ReadConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s (ArrayScheme (VarScheme t)) (pure_fun_s IntScheme (VarScheme t) (AffConst Ref)) (AffConst Prim) \<and>
  c_list = [LeqTypeCrn (VarScheme t) (SPerm UsePerm)] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme WriteConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s (ArrayScheme (VarScheme t))
  (FunScheme (PairScheme IntScheme (VarScheme t) (SPerm OwnPerm)) UnitScheme (SPerm OwnPerm) (AffConst Ref)) (AffConst Prim) \<and>
  c_list = [LeqTypeCrn (VarScheme t) (SPerm UsePerm)] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme UnpackConst ds tau c_list ds' = (\<exists> t1 t2 tx p p'. tau = FunScheme (PairScheme (VarScheme t1) (VarScheme t2) (SVar p)) (FunScheme
  (FunScheme (VarScheme t1) (FunScheme (VarScheme t2) (VarScheme tx) (SVar p) (AffVar p'))
    (SVar p) (AffVar p')) (VarScheme tx) (SVar p') (AffVar p)) (SVar p) (AffConst Prim) \<and>
  c_list = [LeqCrn (XPerm (SVar p)) (SVar p')] \<and> fresh_list ds [t1, t2, tx, p, p'] \<and> ds' = {t1, t2, tx, p, p'} \<union> ds)"
| "const_scheme NewChanConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s UnitScheme (PairScheme (ChanScheme (VarScheme t) SEnd) (ChanScheme (VarScheme t) REnd)
  (SPerm OwnPerm)) (AffConst Prim) \<and> c_list = [] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme SendConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s (ChanScheme (VarScheme t) SEnd) (FunScheme (VarScheme t) UnitScheme
  (SPerm OwnPerm) (AffConst Ref)) (AffConst Prim) \<and> c_list = [] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme RecvConst ds tau c_list ds' = (\<exists> t. tau = pure_fun_s (ChanScheme (VarScheme t) REnd) (VarScheme t) (AffConst Prim) \<and>
    c_list = [] \<and> t \<notin> ds \<and> ds' = {t} \<union> ds)"
| "const_scheme ForkConst ds tau c_list ds' = (\<exists> p. tau = FunScheme (FunScheme UnitScheme UnitScheme (SPerm UsePerm) (AffVar p))
  UnitScheme (SPerm OwnPerm) (AffConst Prim) \<and> c_list = [] \<and> p \<notin> ds \<and> ds' = {p} \<union> ds)"
  
fun op_scheme :: "p_op \<Rightarrow> s_type" where
  "op_scheme (I2Op xop) = pure_fun_s IntScheme (pure_fun_s IntScheme IntScheme (AffConst Prim)) (AffConst Prim)"
| "op_scheme (I1Op xop) = pure_fun_s IntScheme IntScheme (AffConst Prim)"
| "op_scheme (C2Op xop) = pure_fun_s IntScheme (pure_fun_s IntScheme BoolScheme (AffConst Prim)) (AffConst Prim)"
| "op_scheme (C1Op xop) = pure_fun_s IntScheme BoolScheme (AffConst Prim)"
| "op_scheme (R2Op xop) = pure_fun_s BoolScheme (pure_fun_s BoolScheme BoolScheme (AffConst Prim)) (AffConst Prim)"
| "op_scheme (R1Op xop) = pure_fun_s BoolScheme BoolScheme (AffConst Prim)"

    (* inferencing definition *)
  
definition finite_dom where
  "finite_dom r_s l = (\<forall> x. r_s x \<noteq> XPerm (SPerm NoPerm) \<longrightarrow> list_contain l x)"    
  
fun disj_crn where
  "disj_crn r_s1 r_s2 [] = []"
| "disj_crn r_s1 r_s2 (x # t) = (DisjCrn (r_s1 x) (r_s2 x)) # (disj_crn r_s1 r_s2 t)"  
  
fun semi_disj_crn where
  "semi_disj_crn r_s1 r_s2 [] = []"
| "semi_disj_crn r_s1 r_s2 (x # t) = (SemiDisjCrn (r_s1 x) (r_s2 x)) # (semi_disj_crn r_s1 r_s2 t)"    
  
fun fresh_in_type where
  "fresh_in_type (VarScheme b) a = (a \<noteq> b)"
| "fresh_in_type (ArrayScheme tau) a = (fresh_in_type tau a)"
| "fresh_in_type (PairScheme t1 t2 p) a = (fresh_in_type t1 a \<and> fresh_in_type t2 a)"
| "fresh_in_type (FunScheme t1 t2 p1 p2) a = (fresh_in_type t1 a \<and> fresh_in_type t2 a)"
| "fresh_in_type (ChanScheme tau c_end) a = (fresh_in_type tau a)"
| "fresh_in_type tau a = True"
  
definition fresh_tvar where
  "fresh_tvar env a = (\<forall> x. case env x of
    None \<Rightarrow> True
    | Some tau \<Rightarrow> fresh_in_type tau a
  )"  
  
fun aff_crn where
  "aff_crn r_s a [] = Nil"
| "aff_crn r_s a (x # t) = (LeqCrn (r_s x) a) # (aff_crn r_s a t)"    
  (*
fun var_val_crn where
  "var_val_crn (VarType x) tau tau_x = []"  
| "var_val_crn (LocType x) tau tau_x = [MemValCrn tau tau_x]"  *)
  
fun infer_type :: "nat res_env \<Rightarrow> nat set \<Rightarrow> p_exp \<Rightarrow> s_type \<Rightarrow> perm_var_env \<Rightarrow> perm_var_env \<Rightarrow> perm_var_env \<Rightarrow> perm_crn list \<Rightarrow> nat set \<Rightarrow> bool" where
  "infer_type env ds (ConstExp c) tau r_s r_x r_m c_list ds' =
  (const_scheme c ds tau c_list ds' \<and> r_s = empty_var_env \<and> r_x = empty_var_env \<and> r_m = empty_var_env)"
| "infer_type env ds (OpExp xop) tau r_s r_x r_m c_list ds' = (tau = op_scheme xop \<and>
  r_s = empty_var_env \<and> r_x = empty_var_env \<and> r_m = empty_var_env \<and> c_list = [] \<and> ds = ds')"  
| "infer_type env ds (VarExp x) tau r_s r_x r_m c_list ds' = (\<exists> x' a b. x = VarType x' \<and> env (Var x') = Some a \<and> tau = VarScheme a \<and> env (Var x') = Some b \<and>
  r_s = one_var_env (Var x') (XType b) \<and> r_x = r_s \<and> r_m = r_s \<and> c_list = [] \<and> ds' = ds)"
  (*c_list = [LeqTypeCrn (VarScheme b) (SVar p)] @ (var_val_crn x tau (VarScheme b)) \<and>
  p \<notin> ds \<and> ds' = {p} \<union> ds)*)
| "infer_type env ds (PairExp e1 e2) tau r_s r_x r_m c_list ds' = (\<exists> t1 t2 p d r_s1 r_s2 r_x1 r_x2 r_m1 r_m2 cl1 cl2 ds2 ds3.
    infer_type env ds e1 t1 r_s1 r_x1 r_m1 cl1 ds2 \<and> infer_type env ds2 e2 t2 r_s2 r_x2 r_m2 cl2 ds3 \<and> tau = PairScheme t1 t2 (SVar p) \<and>
    r_s = comp_var_env (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p))) \<and>
    r_x = ifz_var_env (XPerm (SVar p)) (comp_var_env (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p))) \<and>
    r_m = comp_var_env r_m1 r_m2 \<and> finite_dom r_s d \<and>
    c_list = [LeqTypeCrn t1 (SVar p), LeqTypeCrn t2 (SVar p)] @(*
    (disj_crn (comp_var_env r_s1 (lift_var_env r_x1 (SVar p))) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p))) d) @ cl1 @ cl2 \<and>*)
    (disj_crn (lift_var_env r_x1 (SVar p)) (lift_var_env r_x2 (SVar p)) d) @ (semi_disj_crn r_m2 r_x1 d) @ (semi_disj_crn r_m1 r_s2 d)
    (*(semi_disj_crn r_m2 (lift_var_env r_x1 (SVar p)) d) @ (semi_disj_crn r_m1 (comp_var_env r_s2 (lift_var_env r_x2 (SVar p))) d)*) @ cl1 @ cl2 \<and>
    p \<notin> ds3 \<and> ds' = {p} \<union> ds3
  )"
| "infer_type env ds (IfExp e1 e2 e3) tau r_s r_x r_m c_list ds' = (\<exists> t1 t2 t3 d r_s1 r_s2 r_s3 r_x1 r_x2 r_x3 r_m1 r_m2 r_m3 cl1 cl2 cl3 ds2 ds3.
    infer_type env ds e1 t1 r_s1 r_x1 r_m1 cl1 ds2 \<and> infer_type env ds2 e2 t2 r_s2 r_x2 r_m2 cl2 ds3 \<and> infer_type env ds3 e3 t3 r_s3 r_x3 r_m3 cl3 ds' \<and>
    r_s = comp_var_env r_s1 (comp_var_env r_s2 r_s3) \<and> r_x = comp_var_env r_x2 r_x3 \<and> r_m = comp_var_env r_m1 (comp_var_env r_m2 r_m3) \<and>
    finite_dom r_s d \<and> tau = t2 \<and>
    c_list = [UnifyCrn t1 BoolScheme, UnifyCrn t2 t3] @ (semi_disj_crn r_m1 (comp_var_env r_s2 r_s3) d) @ cl1 @ cl2 @ cl3)"
| "infer_type env ds (LamExp x e) tau r_s r_x r_m c_list ds' = (\<exists> t2 a p q d r_s' r_x' r_m' cl ds2.
  infer_type (add_env env (Var x) a) (ds \<union> {a}) e t2 r_s' r_x' r_m' cl ds2 \<and> tau = FunScheme (VarScheme a) t2 (SVar p) (AffVar q) \<and>
  r_s = rem_var_env r_s' (Var x) \<and> r_x = r_s \<and> r_m = empty_var_env \<and> x \<notin> ref_vars e \<and>
  finite_dom r_s d \<and> c_list = [LeqCrn (r_s' (Var x)) (SVar p)] @ (aff_crn r_s (SVar q) d) @ cl \<and>
  a \<notin> ds \<and> p \<noteq> q \<and> p \<notin> ds2 \<and> q \<notin> ds2 \<and> ds' = {p, q} \<union> ds2)"
| "infer_type env ds (AppExp e1 e2) tau r_s r_x r_m c_list ds' = (\<exists> tau_f t1 a p q d r_s1 r_s2 r_x1 r_x2 r_m1 r_m2 cl1 cl2 ds2 ds3.
    infer_type env ds e1 tau_f r_s1 r_x1 r_m1 cl1 ds2 \<and> infer_type env ds2 e2 t1 r_s2 r_x2 r_m2 cl2 ds3 \<and>
    tau = VarScheme a \<and> r_s = comp_var_env (comp_var_env r_s1 r_x1) (comp_var_env r_s2 (lift_var_env r_x2 (SVar p))) \<and>
    (*r_x = back_lift_var_env (SVar px) (comp_var_env r_s1 (lift_var_env r_s2 (SVar p))) \<and>*)
    r_x = ifz_var_env (XType a) (comp_var_env r_x1 (lift_var_env r_x2 (SVar p))) \<and>
    r_m = comp_var_env (comp_var_env r_m1 r_x1) (comp_var_env r_m2 (lift_var_env r_x2 (SVar p))) \<and> finite_dom r_s d \<and>
    c_list = [UnifyCrn (FunScheme t1 tau (SVar p) (AffVar q)) tau_f (*, EqTypeCrn (VarScheme a) (SVar p_a)*) ] @
    (disj_crn r_x1 (lift_var_env r_x2 (SVar p)) d) @ (semi_disj_crn r_m2 r_x1 d) @ (semi_disj_crn r_m1 r_s2 d) @ cl1 @ cl2 \<and>
    fresh_list ds3 [a, p, q] \<and> ds' = {a, p, q} \<union> ds3
  )"

    (* solution satisfaction *)
  
fun mini_disj_perm where
  "mini_disj_perm p q = (p = OwnPerm \<longrightarrow> q = NoPerm)"
  
fun mem_val_type where
  "mem_val_type (ArrayTy tau) = True"  
| "mem_val_type (ChanTy tau c_end) = True"  
| "mem_val_type tau = False"  
  
fun dir_sol_crn :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> perm_crn \<Rightarrow> bool" where
  "dir_sol_crn t_sub p_sub (UnifyCrn t1 t2) = (\<exists> tau_x. dir_subst_type t_sub p_sub t1 tau_x \<and> dir_subst_type t_sub p_sub t2 tau_x)"
(*| "dir_sol_crn t_sub p_sub (MemValCrn tau tau_x) = (\<exists> t' tx'.
  dir_subst_type t_sub p_sub tau_x tx' \<and> dir_subst_type t_sub p_sub tau t' \<and> req_type tx' = Ref \<and> req_type t' = Ref)"*)
| "dir_sol_crn t_sub p_sub (LeqCrn p1 p2) = (leq_perm (dir_subst_permx t_sub p_sub p1) (sol_subst_perm p_sub p2))"  
| "dir_sol_crn t_sub p_sub (LeqTypeCrn tau p) = (\<exists> tau_x.
  dir_subst_type t_sub p_sub tau tau_x \<and> aff_leq (req_type tau_x) (sol_subst_perm p_sub p))"
| "dir_sol_crn t_sub p_sub (DisjCrn p1 p2) = (mini_disj_perm (dir_subst_permx t_sub p_sub p1) (dir_subst_permx t_sub p_sub p2) \<and>
  mini_disj_perm (dir_subst_permx t_sub p_sub p2) (dir_subst_permx t_sub p_sub p1))"
| "dir_sol_crn t_sub p_sub (SemiDisjCrn p1 p2) = (mini_disj_perm (dir_subst_permx t_sub p_sub p1) (dir_subst_permx t_sub p_sub p2))"
  
fun dir_sol_sat :: "dir_type_subst \<Rightarrow> perm_subst \<Rightarrow> perm_crn list \<Rightarrow> bool" where
  "dir_sol_sat t_sub p_sub [] = True"  
| "dir_sol_sat t_sub p_sub (c # c_t) = (dir_sol_crn t_sub p_sub c \<and> dir_sol_sat t_sub p_sub c_t)"  

  
lemma sol_sat_append2: "\<lbrakk> dir_sol_sat t_sub p_sub (cl1 @ cl2) \<rbrakk> \<Longrightarrow> dir_sol_sat t_sub p_sub cl2"    
  apply (induct cl1)
   apply (auto)
  done

lemma sol_sat_append1: "\<lbrakk> dir_sol_sat t_sub p_sub (cl1 @ cl2) \<rbrakk> \<Longrightarrow> dir_sol_sat t_sub p_sub cl1"
  apply (induct cl1)
   apply (auto)
  done
  
lemma sol_sat_disj_crn_elem: "\<lbrakk> dir_sol_sat t_sub p_sub (disj_crn r_x r_s d); list_contain d x \<rbrakk> \<Longrightarrow>
  mini_disj_perm (dir_subst_permx t_sub p_sub (r_x x)) (dir_subst_permx t_sub p_sub (r_s x))
  \<and> mini_disj_perm (dir_subst_permx t_sub p_sub (r_s x)) (dir_subst_permx t_sub p_sub (r_x x))"    
  apply (induct d)
   apply (auto)
  done
  
lemma sol_sat_disj_use_env: "\<lbrakk> dir_sol_sat t_sub p_sub (disj_crn r_x r_s d); finite_dom r_x d; finite_dom r_s d \<rbrakk> \<Longrightarrow>
  disj_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub r_s)"
  apply (simp add: disj_use_env_def)
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: finite_dom_def)
  apply (auto)
   apply (case_tac "r_s x = XPerm (SPerm NoPerm)")
    apply (simp add: dir_subst_penv_def)
   apply (cut_tac p_sub="p_sub" and d="d" and x="x" in sol_sat_disj_crn_elem)
     apply (auto)
      apply (simp add: dir_subst_penv_def)
     apply (simp add: dir_subst_penv_def)
    apply (simp add: dir_subst_penv_def)
   apply (simp add: dir_subst_penv_def)
  apply (case_tac "r_x x = XPerm (SPerm NoPerm)")
   apply (simp add: dir_subst_penv_def)
  apply (cut_tac p_sub="p_sub" and d="d" and x="x" in sol_sat_disj_crn_elem)
    apply (auto)
     apply (simp add: dir_subst_penv_def)
    apply (simp add: dir_subst_penv_def)
   apply (simp add: dir_subst_penv_def)
  apply (simp add: dir_subst_penv_def)
  done

lemma sol_sat_mini_disj_crn_elem: "\<lbrakk> dir_sol_sat t_sub p_sub (semi_disj_crn r_x r_s d); list_contain d x \<rbrakk> \<Longrightarrow>
  mini_disj_perm (dir_subst_permx t_sub p_sub (r_x x)) (dir_subst_permx t_sub p_sub (r_s x))"    
  apply (induct d)
   apply (auto)
  done    
    
lemma sol_sat_mini_disj_use_env: "\<lbrakk> dir_sol_sat t_sub p_sub (semi_disj_crn r_x r_s d); finite_dom r_x d; finite_dom r_s d \<rbrakk> \<Longrightarrow>
  mini_disj_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub r_s)"
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: finite_dom_def)
  apply (auto)
  apply (case_tac "r_s x = XPerm (SPerm NoPerm)")
   apply (simp add: dir_subst_penv_def)
  apply (cut_tac p_sub="p_sub" and d="d" and x="x" in sol_sat_mini_disj_crn_elem)
    apply (auto)
   apply (simp add: dir_subst_penv_def)
  apply (simp add: dir_subst_penv_def)
  done
    
lemma sol_sat_aff_crn_elem: "\<lbrakk> dir_sol_sat t_sub p_sub (aff_crn r_s (SVar q) d); list_contain d x \<rbrakk> \<Longrightarrow>
  leq_perm (dir_subst_permx t_sub p_sub (r_s x)) (sol_subst_perm p_sub (SVar q))"    
  apply (induct d)
   apply (auto)
  done
    
lemma sol_sat_aff_use_env: "\<lbrakk> dir_sol_sat t_sub p_sub (aff_crn r_s (SVar q) d); finite_dom r_s d \<rbrakk> \<Longrightarrow>
  aff_use_env (dir_subst_penv t_sub p_sub r_s) (sol_subst_aff p_sub (AffVar q))"
  apply (simp add: aff_use_env_def)
  apply (simp add: finite_dom_def)
  apply (case_tac "sol_subst_aff p_sub (AffVar q)")
    apply (auto)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (cut_tac p_sub="p_sub" and q="q" and x="x" in sol_sat_aff_crn_elem)
     apply (auto)
    apply (simp add: dir_subst_penv_def)
    apply (case_tac "r_s x")
       apply (auto)
    apply (case_tac x1)
     apply (auto)
   apply (simp add: dir_subst_penv_def)
   apply (case_tac "p_sub q")
     apply (auto)
  apply (simp add: null_use_env_def)
  apply (auto)
  apply (case_tac "r_s x = XPerm (SPerm NoPerm)")
   apply (simp add: dir_subst_penv_def)
  apply (cut_tac p_sub="p_sub" and q="q" and x="x" in sol_sat_aff_crn_elem)
    apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (case_tac "p_sub q")
    apply (auto)
  apply (case_tac "dir_subst_permx t_sub p_sub (r_s x)")
    apply (auto)
  done
 
lemma sol_sat_aff_use_envx: "\<lbrakk> dir_sol_sat t_sub p_sub (aff_crn r_s (SVar q) d); finite_dom r_s d \<rbrakk> \<Longrightarrow>
  aff_use_env (dir_subst_penv t_sub p_sub r_s) (as_aff (p_sub q))"
  apply (simp add: aff_use_env_def)
  apply (simp add: finite_dom_def)
  apply (case_tac "sol_subst_aff p_sub (AffVar q)")
    apply (auto)
   apply (simp add: weak_use_env_def)
   apply (auto)
   apply (cut_tac p_sub="p_sub" and q="q" and x="x" in sol_sat_aff_crn_elem)
     apply (auto)
    apply (simp add: dir_subst_penv_def)
    apply (case_tac "r_s x")
       apply (auto)
    apply (case_tac x1)
     apply (auto)
   apply (simp add: dir_subst_penv_def)
   apply (case_tac "p_sub q")
     apply (auto)
  apply (simp add: null_use_env_def)
  apply (auto)
  apply (case_tac "r_s x = XPerm (SPerm NoPerm)")
   apply (simp add: dir_subst_penv_def)
  apply (cut_tac p_sub="p_sub" and q="q" and x="x" in sol_sat_aff_crn_elem)
    apply (auto)
  apply (simp add: dir_subst_penv_def)
  apply (case_tac "p_sub q")
    apply (auto)
  apply (case_tac "dir_subst_permx t_sub p_sub (r_s x)")
    apply (auto)
  done
(*
lemma sol_subst_var_type: "sol_subst_var_full t_sub p_sub tau_n a = sol_subst_type_full t_sub p_sub tau_n (VarScheme a)"    
  apply (simp add: sol_subst_var_full_def)
  apply (simp add: sol_subst_type_full_def)
  apply (simp add: sol_subst_var_def)
  done    
  *)  
    (* ##### sub-domain lemmas *)
  
definition sub_dom where
  "sub_dom r_x r_s = (\<forall> x. r_s x = XPerm (SPerm NoPerm) \<longrightarrow> r_x x =  XPerm (SPerm NoPerm))"  
  
lemma finite_sub_dom: "\<lbrakk> finite_dom r_s d; sub_dom r_x r_s \<rbrakk> \<Longrightarrow> finite_dom r_x d"    
  apply (induct d)
   apply (auto)
   apply (simp add: sub_dom_def)
   apply (simp add: finite_dom_def)
  apply (simp add: sub_dom_def)
  apply (simp add: finite_dom_def)
  apply (auto)
  done
  
lemma id_sub_dom: "sub_dom r_s r_s"    
  apply (simp add: sub_dom_def)
  done
  
lemma lift_sub_dom: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom (lift_var_env r_x p) r_s"    
  apply (simp add: sub_dom_def)
  apply (simp add: lift_var_env_def)
  done

lemma lift_sub_dom2: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom r_x (lift_var_env r_s p)"    
  apply (simp add: sub_dom_def)
  apply (simp add: lift_var_env_def)
  done

lemma dist_lift_sub_dom: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom (lift_var_env r_x p) (lift_var_env r_s p)"    
  apply (simp add: sub_dom_def)
  apply (simp add: lift_var_env_def)
  done
    
lemma dist_comp_sub_dom: "\<lbrakk> sub_dom r_xa r_s; sub_dom r_xb r_s \<rbrakk> \<Longrightarrow> sub_dom (comp_var_env r_xa r_xb) r_s"    
  apply (simp add: sub_dom_def)
  apply (simp add: comp_var_env_def)
  done
    
lemma comp_sub_dom1: "\<lbrakk> sub_dom r_x r_sa \<rbrakk> \<Longrightarrow> sub_dom r_x (comp_var_env r_sa r_sb)"     
  apply (simp add: sub_dom_def)
  apply (simp add: comp_var_env_def)
  done
    
lemma comp_sub_dom2: "\<lbrakk> sub_dom r_x r_sb \<rbrakk> \<Longrightarrow> sub_dom r_x (comp_var_env r_sa r_sb)"     
  apply (simp add: sub_dom_def)
  apply (simp add: comp_var_env_def)
  done
    
lemma dist_rem_sub_dom: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom (rem_var_env r_x x) (rem_var_env r_s x)"    
  apply (simp add: sub_dom_def)
  apply (simp add: rem_var_env_def)
  done

lemma if_zero_sub_dom: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom (ifz_var_env q r_x) r_s"    
  apply (simp add: sub_dom_def)
  apply (simp add: ifz_var_env_def)
  done
    
lemma if_zero_sub_dom2: "\<lbrakk> sub_dom r_x r_s \<rbrakk> \<Longrightarrow> sub_dom r_x (ifz_var_env q r_s)"    
  apply (simp add: sub_dom_def)
  apply (simp add: ifz_var_env_def)
  done    
  
lemma infer_x_sub_dom: "\<lbrakk> infer_type env ds e tau r_s r_x r_m c_list ds' \<rbrakk> \<Longrightarrow> sub_dom r_x r_s"    
  apply (induct e arbitrary: env ds tau r_s r_x r_m c_list ds')
        apply (auto)
    (* const + op + var case *)
        apply (rule_tac id_sub_dom)
       apply (rule_tac id_sub_dom)
      apply (rule_tac id_sub_dom)
    (* pair case *)
     apply (rule_tac if_zero_sub_dom)
     apply (rule_tac dist_comp_sub_dom)
      apply (rule_tac comp_sub_dom1)
      apply (rule_tac comp_sub_dom2)
      apply (rule_tac id_sub_dom)
     apply (rule_tac comp_sub_dom2)
     apply (rule_tac comp_sub_dom2)
     apply (rule_tac id_sub_dom)
    (* if case *)
    apply (rule_tac comp_sub_dom2)
    apply (rule_tac dist_comp_sub_dom)
     apply (rule_tac comp_sub_dom1)
     apply (simp)
    apply (rule_tac comp_sub_dom2)
    apply (simp)
    (* lam case *)
   apply (rule_tac dist_rem_sub_dom)
   apply (rule_tac id_sub_dom)
    (* app case *)
  apply (rule_tac if_zero_sub_dom)
  apply (rule_tac dist_comp_sub_dom)
   apply (rule_tac comp_sub_dom1)
   apply (rule_tac comp_sub_dom2)
   apply (rule_tac id_sub_dom)
  apply (rule_tac comp_sub_dom2)
  apply (rule_tac comp_sub_dom2)
  apply (rule_tac id_sub_dom)
  done    

lemma infer_m_sub_dom: "\<lbrakk> infer_type env ds e tau r_s r_x r_m c_list ds' \<rbrakk> \<Longrightarrow> sub_dom r_m r_s"    
  apply (induct e arbitrary: env ds tau r_s r_x r_m c_list ds')
        apply (auto)
    (* const + op + var case *)
        apply (rule_tac id_sub_dom)
       apply (rule_tac id_sub_dom)
      apply (rule_tac id_sub_dom)
    (* pair case *)
     apply (rule_tac dist_comp_sub_dom)
      apply (rule_tac comp_sub_dom1)
      apply (rule_tac comp_sub_dom1)
      apply (simp)
     apply (rule_tac comp_sub_dom2)
     apply (rule_tac comp_sub_dom1)
     apply (simp)
    (* if case *)
    apply (rule_tac dist_comp_sub_dom)
     apply (rule_tac comp_sub_dom1)
     apply (simp)
    apply (rule_tac dist_comp_sub_dom)
     apply (rule_tac comp_sub_dom2)
     apply (rule_tac comp_sub_dom1)
     apply (simp)
    apply (rule_tac comp_sub_dom2)
    apply (rule_tac comp_sub_dom2)
    apply (simp)
    (* lam case *)
   apply (simp add: sub_dom_def)
   apply (simp add: empty_var_env_def)
    (* app case *)
  apply (rule_tac dist_comp_sub_dom)
   apply (rule_tac comp_sub_dom1)
   apply (rule_tac dist_comp_sub_dom)
    apply (rule_tac comp_sub_dom1)
    apply (simp)
   apply (rule_tac comp_sub_dom2)
   apply (rule_tac id_sub_dom)
  apply (rule_tac comp_sub_dom2)
  apply (rule_tac dist_comp_sub_dom)
   apply (rule_tac comp_sub_dom1)
   apply (simp)
  apply (rule_tac comp_sub_dom2)
  apply (rule_tac id_sub_dom)
  done    
    
    (* ##### general inferencing lemmas *)
    
lemma infer_x_leq_use_env: "\<lbrakk> infer_type env ds e tau r_s r_x r_m c_list ds' \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub r_x) (dir_subst_penv t_sub p_sub r_s)"    
  apply (induct e arbitrary: env ds tau r_s r_x r_m c_list ds')
        apply (auto)
    (* const + op + var cases *)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
    (* pair case *)
     apply (rule_tac if_zero_leq_var_env)
     apply (rule_tac dist_comp_leq_var_env)
      apply (rule_tac comp_leq_var_env1)
      apply (rule_tac comp_leq_var_env2)
      apply (rule_tac id_leq_use_env)
     apply (rule_tac comp_leq_var_env2)
     apply (rule_tac comp_leq_var_env2)
     apply (rule_tac id_leq_use_env)
    (* if case *)
    apply (rule_tac comp_leq_var_env2)
    apply (rule_tac dist_comp_leq_var_env)
     apply (rule_tac comp_leq_var_env1)
     apply (auto)
    apply (rule_tac comp_leq_var_env2)
    apply (auto)
    (* lam + app case *)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac if_zero_leq_var_env)
  apply (rule_tac dist_comp_leq_var_env)
   apply (rule_tac comp_leq_var_env1)
   apply (rule_tac comp_leq_var_env2)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac comp_leq_var_env2)
  apply (rule_tac comp_leq_var_env2)
  apply (rule_tac id_leq_use_env)
  done    
  
lemma infer_m_leq_use_env: "\<lbrakk> infer_type env ds e tau r_s r_x r_m c_list ds' \<rbrakk> \<Longrightarrow>
  leq_use_env (dir_subst_penv t_sub p_sub r_m) (dir_subst_penv t_sub p_sub r_s)"
  apply (induct e arbitrary: env ds tau r_s r_x r_m c_list ds')
        apply (auto)
    (* const + op + var cases *)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac id_leq_use_env)
      apply (rule_tac id_leq_use_env)
    (* pair case *)
     apply (rule_tac dist_comp_leq_var_env)
      apply (rule_tac comp_leq_var_env1)
      apply (rule_tac comp_leq_var_env1)
      apply (auto)
     apply (rule_tac comp_leq_var_env2)
     apply (rule_tac comp_leq_var_env1)
     apply (auto)
    (* if case *)
    apply (rule_tac dist_comp_leq_var_env)
     apply (rule_tac comp_leq_var_env1)
     apply (auto)
    apply (rule_tac dist_comp_leq_var_env)
     apply (rule_tac comp_leq_var_env2)
     apply (rule_tac comp_leq_var_env1)
     apply (auto)
    apply (rule_tac comp_leq_var_env2)
    apply (rule_tac comp_leq_var_env2)
    apply (auto)
    (* lam + app case *)
   apply (rule_tac empty_leq_var_env)
  apply (rule_tac dist_comp_leq_var_env)
   apply (rule_tac comp_leq_var_env1)
   apply (rule_tac dist_comp_leq_var_env)
    apply (rule_tac comp_leq_var_env1)
    apply (auto)
   apply (rule_tac comp_leq_var_env2)
   apply (rule_tac id_leq_use_env)
  apply (rule_tac comp_leq_var_env2)
  apply (rule_tac dist_comp_leq_var_env)
   apply (rule_tac comp_leq_var_env1)
   apply (auto)
  apply (rule_tac comp_leq_var_env2)
  apply (rule_tac id_leq_use_env)
  done
    
    (* ##### special comp lemma *)

    (*
definition anti_norm_use_env where
  "anti_norm_use_env r_s r_x = (\<lambda> x. if r_x x \<noteq> NoPerm then NoPerm else r_s x)"
    *)
definition sub_norm_use_env where
  "sub_norm_use_env r_s r_x = (\<lambda> x. if r_x x = OwnPerm then NoPerm else r_s x)"  
  
lemma decomp_use_env: "comp_use_env r_s r_x = comp_use_env r_s (sub_norm_use_env r_x r_s)"  
  apply (case_tac "\<forall> x. comp_use_env r_s r_x x = comp_use_env r_s (sub_norm_use_env r_x r_s) x")
   apply (auto)
  apply (simp add: comp_use_env_def)
  apply (simp add: sub_norm_use_env_def)
  apply (auto)
  done
 
lemma mini_disj_sub_norm_use_env: "mini_disj_use_env r_s (sub_norm_use_env r_x r_s)"    
  apply (simp add: mini_disj_use_env_def)
  apply (simp add: sub_norm_use_env_def)
  done
    
lemma well_typed_comp_perms_prec: "\<lbrakk> well_typed env delta r_s e tau (diff_use_env r_s r_ex) rx \<rbrakk> \<Longrightarrow>
  well_typed env delta (comp_use_env r_s r_x) e tau (diff_use_env (comp_use_env r_s r_x) r_ex) rx"    
  apply (cut_tac r_s="r_s" and r_x="r_x" in decomp_use_env)
  apply (auto)
  apply (rule_tac r_c="comp_use_env (diff_use_env r_s r_ex) (sub_norm_use_env r_x r_s)" in well_typed_decr_end_perm)
    apply (rule_tac well_typed_comp_perms_gen)
     apply (simp)
    apply (rule_tac mini_disj_sub_norm_use_env)
   apply (rule_tac lhs_dist_dcl_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac self_diff_leq_use_env)
  apply (rule_tac r_sb="diff_use_env r_s r_ex" in trans_leq_use_env)
   apply (rule_tac dist_diff_leq_use_env)
   apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac well_typed_perm_leqx)
  apply (auto)
  done

lemma well_typed_comp_perms_prec2: "\<lbrakk> well_typed env delta r_s e tau (diff_use_env r_s r_ex) rx  \<rbrakk> \<Longrightarrow>
  well_typed env delta (comp_use_env r_x r_s) e tau (diff_use_env (comp_use_env r_x r_s) r_ex) rx"   
  apply (simp add: comm_comp_use_env)
  apply (rule_tac well_typed_comp_perms_prec)
   apply (auto)
  done
  
    (* ##### special lifting lemma *)

lemma spec_diff_comp_leq_use_env: "\<lbrakk> leq_use_env r_x r_sb; leq_use_env r_x (diff_use_env (comp_use_env r_sa r_sb) r_ex) \<rbrakk> \<Longrightarrow>
  leq_use_env r_x (diff_use_env r_sb r_ex)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: diff_use_env_def)
  apply (simp add: comp_use_env_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (case_tac "r_x x")
    apply (auto)
   apply (case_tac "r_ex x")
     apply (auto)
  apply (case_tac "r_ex x")
    apply (auto)
  done
    
lemma wtclp_leq_use_env: "\<lbrakk> leq_use_env r_xb r_sb;
  leq_use_env (comp_use_env r_xa r_xb) (diff_use_env (comp_use_env r_sa r_sb) r_ex) \<rbrakk>
    \<Longrightarrow> leq_use_env (comp_use_env r_xa (lift_use_env r_xb r))
        (diff_use_env (comp_use_env r_sa (lift_use_env r_sb r)) r_ex)"
  apply (rule_tac dist_comp_leq_use_env)
   apply (rule_tac r_sb="diff_use_env (comp_use_env r_sa r_sb) r_ex" in trans_leq_use_env)
    apply (rule_tac dist_diff_leq_use_env)
    apply (rule_tac dist_comp_leq_use_env)
     apply (rule_tac self_comp_leq_use_env1)
    apply (rule_tac comp_leq_use_env2)
    apply (rule_tac self_lift_leq_use_env)
   apply (rule_tac r_sb="comp_use_env r_xa r_xb" in trans_leq_use_env)
    apply (simp)
   apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac rhs_dist_dcl_use_env)
  apply (rule_tac comp_leq_use_env2)
  apply (simp add: lift_diff_use_env)
  apply (rule_tac dist_lift_leq_use_env)
  apply (rule_tac r_sa="r_sa" in spec_diff_comp_leq_use_env)
   apply (simp)
  apply (rule_tac r_sb="comp_use_env r_xa r_xb" in trans_leq_use_env)
   apply (auto)
  apply (rule_tac self_comp_leq_use_env2)
  done
    
lemma simp_lift_comp_leq_use_env: "\<lbrakk> leq_use_env r_x (comp_use_env r_sa r_sb) \<rbrakk> \<Longrightarrow> leq_use_env r_x (comp_use_env r_sa (lift_use_env r_sb r))"    
  apply (rule_tac r_sb="comp_use_env r_sa r_sb" in trans_leq_use_env)
   apply (rule_tac dist_comp_leq_use_env)
    apply (rule_tac self_comp_leq_use_env1)
   apply (rule_tac comp_leq_use_env2)
   apply (rule_tac self_lift_leq_use_env)
  apply (simp)
  done
  
lemma well_typed_comp_lift_perms: "\<lbrakk> well_typed env delta (comp_use_env r_sa r_sb) e tau (comp_use_env r_xa r_xb) rx; leq_use_env r_xb r_sb \<rbrakk> \<Longrightarrow>
  well_typed env delta (comp_use_env r_sa (lift_use_env r_sb r)) e tau (comp_use_env r_xa (lift_use_env r_xb r)) rx"
  apply (induct e arbitrary: env r_sa r_sb tau r_xa r_xb rx)  
        apply (auto)
    (* const + op cases *)
           apply (rule_tac dist_comp_leq_use_env)
            apply (rule_tac simp_lift_comp_leq_use_env)
            apply (rule_tac r_sb="comp_use_env r_xa r_xb" in trans_leq_use_env)
             apply (simp)
            apply (rule_tac self_comp_leq_use_env1)
           apply (rule_tac comp_leq_use_env2)
           apply (rule_tac dist_lift_leq_use_env)
           apply (simp)
          apply (rule_tac simp_lift_comp_leq_use_env)
          apply (simp)
         apply (rule_tac dist_comp_leq_use_env)
          apply (rule_tac simp_lift_comp_leq_use_env)
          apply (rule_tac r_sb="comp_use_env r_xa r_xb" in trans_leq_use_env)
           apply (simp)
          apply (rule_tac self_comp_leq_use_env1)
         apply (rule_tac comp_leq_use_env2)
         apply (rule_tac dist_lift_leq_use_env)
         apply (simp)
        apply (rule_tac simp_lift_comp_leq_use_env)
        apply (simp)
    (* var cases *)
       apply (rule_tac simp_lift_comp_leq_use_env)
       apply (simp)
      apply (rule_tac x="r_ex" in exI)
      apply (auto)
        apply (rule_tac wtclp_leq_use_env)
         apply (auto)
       apply (rule_tac simp_lift_comp_leq_use_env)
       apply (simp)
      apply (rule_tac simp_lift_comp_leq_use_env)
      apply (simp)
    (* pair case *)
     apply (cut_tac r_sc="r_xb" and r_sb="comp_use_env r_xa r_xb" and r_sa="r_s3" in trans_leq_use_env)
       apply (rule_tac r_sb="diff_use_env r_s3 r_ex" in trans_leq_use_env)
        apply (rule_tac self_diff_leq_use_env)
       apply (simp)
      apply (rule_tac self_comp_leq_use_env2)
     apply (cut_tac r_sc="r_xb" and r_sb="r_s3" and r_sa="r_s2" in trans_leq_use_env)
       apply (rule_tac well_typed_perm_leq)
       apply (auto)    
     apply (rule_tac x="comp_use_env r_s2 (lift_use_env r_xb r)" in exI)
     apply (rule_tac x="comp_use_env r_s3 (lift_use_env r_xb r)" in exI)
     apply (rule_tac x="rx1" in exI)
     apply (auto)
      apply (case_tac "\<not> well_typed env delta (comp_use_env r_sa r_sb) e1 t1 (comp_use_env r_s2 r_xb) rx1")
       apply (cut_tac r_s="r_s2" and r_x="r_xb" in cancel_comp_use_env2)
        apply (auto)
     apply (rule_tac x="rx2" in exI)
     apply (auto)
        apply (case_tac "\<not> well_typed env delta (comp_use_env r_s2 r_xb) e2 t2 (comp_use_env r_s3 r_xb) rx2")
         apply (cut_tac r_s="r_s3" and r_x="r_xb" in cancel_comp_use_env2)
          apply (simp_all)
         apply (cut_tac env="env" and r_c="comp_use_env r_s2 r_xb" and ?r_s1.0="r_s2" and e="e2" in well_typed_incr_start_perm)
           apply (auto)
         apply (rule_tac self_comp_leq_use_env1)
        apply (cut_tac r="r_xb" in id_leq_use_env)
        apply (auto)
       apply (rule_tac comp_leq_use_env1)
       apply (simp)
      apply (rule_tac comp_leq_use_env1)
      apply (simp)
     apply (rule_tac x="r_ex" in exI)
     apply (auto)
       apply (rule_tac wtclp_leq_use_env)
        apply (rule_tac id_leq_use_env)
       apply (rule_tac rhs_dist_dcl_use_env)
       apply (rule_tac comp_leq_use_env1)
       apply (simp)
      apply (rule_tac simp_lift_comp_leq_use_env)
      apply (simp)
     apply (rule_tac simp_lift_comp_leq_use_env)
     apply (simp)
    (* if case *)
    apply (rule_tac x="rx'" in exI)
    apply (rule_tac x="comp_use_env r_s2 (lift_use_env r_xb r)" in exI)
    apply (auto)
     apply (case_tac "\<not> well_typed env delta (comp_use_env r_sa r_sb) e1 BoolTy (comp_use_env r_s2 r_xb) rx'")
      apply (cut_tac r_s="r_s2" and r_x="r_xb" in cancel_comp_use_env2)
       apply (rule_tac r_sb="comp_use_env r_xa r_xb" in trans_leq_use_env)
        apply (rule_tac well_typed_perm_leq)
        apply (auto)
     apply (rule_tac self_comp_leq_use_env2)
    apply (cut_tac r="r_xb" in id_leq_use_env)
    apply (cut_tac r_s="r_s2" and r_x="r_xb" in self_comp_leq_use_env1)
    apply (rule_tac x="rx1" in exI)
    apply (auto)
     apply (cut_tac env="env" and ?r_s1.0="r_s2" and r_c="comp_use_env r_s2 r_xb" and e="e2" in well_typed_incr_start_perm)
       apply (auto)
    apply (rule_tac x="rx2" in exI)
    apply (auto)
    apply (cut_tac env="env" and ?r_s1.0="r_s2" and r_c="comp_use_env r_s2 r_xb" and e="e3" in well_typed_incr_start_perm)
      apply (auto)
    (* lam case *)
   apply (rule_tac x="rxa" in exI)
   apply (auto)
    apply (rule_tac simp_lift_comp_leq_use_env)
    apply (simp)
   apply (rule_tac x="r_ex" in exI)
   apply (auto)
     apply (rule_tac wtclp_leq_use_env)
      apply (auto)
    apply (rule_tac simp_lift_comp_leq_use_env)
    apply (simp)
   apply (rule_tac simp_lift_comp_leq_use_env)
   apply (simp)
    (* app case *)
  apply (cut_tac r_sc="r_xb" and r_sb="comp_use_env r_xa r_xb" and r_sa="r_s3" in trans_leq_use_env)
    apply (rule_tac r_sb="diff_use_env r_s3 (comp_use_env (comp_use_env rx1 (lift_use_env rx2 ra)) r_ex)" in trans_leq_use_env)
     apply (rule_tac self_diff_leq_use_env)
    apply (simp)
   apply (rule_tac self_comp_leq_use_env2)
  apply (cut_tac r_sc="r_xb" and r_sb="r_s3" and r_sa="r_s2" in trans_leq_use_env)
    apply (rule_tac well_typed_perm_leq)
    apply (auto)
  apply (cut_tac r="r_xb" in id_leq_use_env)
  apply (rule_tac x="t1" in exI)
  apply (rule_tac x="ra" in exI)
  apply (rule_tac x="a" in exI)
  apply (rule_tac x="comp_use_env r_s2 (lift_use_env r_xb r)" in exI)
  apply (rule_tac x="rx1" in exI)
  apply (auto)
   apply (case_tac "\<not> well_typed env delta (comp_use_env r_sa r_sb) e1 (FunTy t1 tau ra a) (comp_use_env r_s2 r_xb) rx1")
    apply (cut_tac r_s="r_s2" and r_x="r_xb" in cancel_comp_use_env2)
     apply (auto)
  apply (rule_tac x="rx2" in exI)
  apply (rule_tac x="comp_use_env r_s3 (lift_use_env r_xb r)" in exI)
  apply (auto)
   apply (case_tac "\<not> well_typed env delta (comp_use_env r_s2 r_xb) e2 t1 (comp_use_env r_s3 r_xb) rx2")
    apply (cut_tac r_s="r_s3" and r_x="r_xb" in cancel_comp_use_env2)
     apply (auto)
   apply (cut_tac env="env" and ?r_s1.0="r_s2" and r_c="comp_use_env r_s2 r_xb" and e="e2" in well_typed_incr_start_perm)
     apply (auto)
   apply (rule_tac self_comp_leq_use_env1)
  apply (rule_tac x="r_ex" in exI)
  apply (auto)
     apply (rule_tac wtclp_leq_use_env)
      apply (auto)
     apply (rule_tac rhs_dist_dcl_use_env)
     apply (rule_tac comp_leq_use_env1)
     apply (simp)
    apply (rule_tac comp_leq_use_env1)
    apply (simp)
   apply (rule_tac simp_lift_comp_leq_use_env)
   apply (simp)
  apply (rule_tac simp_lift_comp_leq_use_env)
  apply (simp)
  done        
    

    
definition set_dom :: "string set \<Rightarrow> string list \<Rightarrow> bool" where
  "set_dom ds l = (\<forall> x. x \<in> ds \<longrightarrow> list_contain l x)"    
  
fun max_length where
  "max_length [] = 0"
| "max_length (x # t) = max (length x) (max_length t)"

  (* how can we prove that the "nu-string" is not contained in l? inductively, we know that the lesser*)
  
lemma m_list_ex: "\<lbrakk> length x > max_length l \<rbrakk> \<Longrightarrow> \<not> list_contain l x"
  apply (induct l)
   apply (auto)
  done
    
lemma string_of_length: "\<exists> s :: string. length s = i"
  apply (rule_tac Ex_list_of_length)
  done
    
lemma fresh_list_ex_gen: "\<lbrakk> set_dom ds l; fresh_list ds t \<rbrakk> \<Longrightarrow> \<exists> a. fresh_list ds (a # t)"
  apply (simp add: fresh_list_def)
  apply (auto)
  apply (cut_tac i="(max (max_length l) (max_length t)) + 1" in string_of_length)
  apply (auto)
  apply (rule_tac x="s" in exI)
  apply (auto)
    (* t does not contain a by construction *)
   apply (cut_tac l="t" and x="s" in m_list_ex)
    apply (auto)
    (* l does not contain a by construction as well *)
  apply (simp add: set_dom_def)
  apply (erule_tac x="s" in allE)
  apply (cut_tac l="l" and x="s" in m_list_ex)
   apply (auto)
  done
    
lemma fresh_list_ex1: "\<lbrakk> set_dom ds l \<rbrakk> \<Longrightarrow> \<exists> a. fresh_list ds [a]"
  apply (rule_tac fresh_list_ex_gen)
   apply (auto)
  apply (simp add: fresh_list_def)
  done

lemma fresh_list_exl: "\<lbrakk> set_dom ds l \<rbrakk> \<Longrightarrow> \<exists> l'. fresh_list ds l' \<and> length l' = i"
  apply (induct i)
   apply (auto)
   apply (simp add: fresh_list_def)
  apply (cut_tac ds="ds" and t="l'" in fresh_list_ex_gen)
    apply (auto)
  done
    
lemma fresh_list_ex4: "\<lbrakk> set_dom ds l \<rbrakk> \<Longrightarrow> \<exists> a b c d. fresh_list ds [a, b, c, d]"
  apply (cut_tac ds="ds" and l="l" and i="4" in fresh_list_exl)
   apply (auto)
  apply (case_tac l')
   apply (auto)
  apply (case_tac list)
   apply (auto)
  apply (case_tac lista)
   apply (auto)
  apply (case_tac list)
   apply (auto)
  done

end