theory SolverP3
  imports SolverP2 InferVar
begin
  
fun lbound_perm where
  "lbound_perm (SVar r) = UsePerm"
| "lbound_perm (SPerm p) = p"  
  
fun lbound_permx where
  "lbound_permx (XPerm p) = lbound_perm p"
| "lbound_permx (XType a) = NoPerm"
| "lbound_permx (XComp px qx) = union_perm (lbound_permx px) (lbound_permx qx)"
| "lbound_permx (XLift px q) = (if lbound_perm q = OwnPerm \<and> lbound_permx px \<noteq> NoPerm then OwnPerm else lbound_permx px)"
| "lbound_permx (XIfZero px qx) = (if lbound_permx px = NoPerm then NoPerm else lbound_permx qx)"    
    
fun owner_crn where
  "owner_crn (LeqCrn2 px q) = (lbound_permx px = OwnPerm)"
| "owner_crn (DisjCrn2 px qx) = False"
| "owner_crn (MiniDisjCrn2 px qx) = False"  
  
definition use_semi_env where
  "use_semi_env = (\<lambda> x. UsePerm)"  
  
function complete_sol_calc_f where
  "complete_sol_calc_f c_list = (case select_list owner_crn c_list of
    None \<Rightarrow> Some use_semi_env
    | Some (c, c_t) \<Rightarrow> (case c of
      LeqCrn2 px q \<Rightarrow> (case q of
        SPerm p \<Rightarrow> if p = OwnPerm then complete_sol_calc_f c_t else None 
        | SVar r \<Rightarrow> (case complete_sol_calc_f (sub1_crn_list c_t r) of
          None \<Rightarrow> None
          | Some o_sub \<Rightarrow> Some (\<lambda> r'. if r' = r then OwnPerm else o_sub r')
        )
      )
      | other \<Rightarrow> None
    )
  )" by auto  
termination
  apply (relation "measure length")
   apply (auto)
   apply (rule_tac select_less_length)
   apply (auto)
  apply (rule_tac t="length (sub1_crn_list b x2a)" and s="length b" in subst)
   apply (rule_tac sub1_same_length)
  apply (rule_tac select_less_length)
  apply (auto)
  done
    
definition complete_sol_calc where
  "complete_sol_calc c_list = complete_sol_calc_f c_list"    
  
lemma select_sol_sat_crn: "\<lbrakk> sol_sat2 p_sub c_list; select_list f c_list = Some (c, c_t) \<rbrakk> \<Longrightarrow> sol_sat_crn2 p_sub c"  
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done

lemma select_sol_sat: "\<lbrakk> sol_sat2 p_sub c_list; select_list f c_list = Some (c, c_t) \<rbrakk> \<Longrightarrow> sol_sat2 p_sub c_t"      
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done    
  
lemma select_sol_sat_split: "\<lbrakk> select_list f c_list = Some (c, c_t); sol_sat_crn2 p_sub c; sol_sat2 p_sub c_t \<rbrakk> \<Longrightarrow> sol_sat2 p_sub c_list"      
  apply (induct c_list arbitrary: c_t)
   apply (auto)
   apply (case_tac "f a")
    apply (auto)
   apply (case_tac "select_list f c_list")
    apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done     
    
    (*
definition nz_sub where
  "nz_sub p_sub px = (\<forall> x. x \<in> pvar_set px \<longrightarrow> p_sub x \<noteq> NoPerm)"
    *)

definition nz_sub where
  "nz_sub p_sub ds = (\<forall> x. x \<in> ds \<longrightarrow> p_sub x \<noteq> NoPerm)"
    
lemma lbound_eval_perm: "\<lbrakk> nz_sub p_sub (pvar_set_perm p) \<rbrakk> \<Longrightarrow> leq_perm (lbound_perm p) (eval_perm p_sub p)"     
  apply (case_tac p)
   apply (auto)
   apply (case_tac x1)
     apply (auto)
  apply (simp add: nz_sub_def)
  apply (case_tac "p_sub x2")
    apply (auto)
  done
  
lemma lbound_eval_permx: "\<lbrakk> nz_sub p_sub (pvar_set px) \<rbrakk> \<Longrightarrow> leq_perm (lbound_permx px) (eval_permx p_sub px)"      
  apply (induct px)
      apply (auto)
    (* perm case *)
         apply (rule_tac lbound_eval_perm)
         apply (simp)
    (* comp case *)
        apply (rule_tac dist_union_leq_perm)
         apply (rule_tac union_leq_perm1)
         apply (simp add: nz_sub_def)
        apply (rule_tac union_leq_perm2)
        apply (simp add: nz_sub_def)
    (* lift cases 1-4 *)
       apply (case_tac x2a)
        apply (auto)
      apply (simp add: nz_sub_def)
      apply (case_tac "lbound_permx px")
        apply (auto)
     apply (simp add: nz_sub_def)
    apply (simp add: nz_sub_def)
    (* if zero cases 1-2 *)
   apply (case_tac "\<not> nz_sub p_sub (pvar_set px1)")
    apply (simp add: nz_sub_def)
   apply (auto)
   apply (case_tac "lbound_permx px1")
     apply (auto)
  apply (simp add: nz_sub_def)
  done    
    
    (* only true assuming that for every var in px, p_sub is in Use *)
lemma own_lbound_eval_permx: "\<lbrakk> nz_sub p_sub (pvar_set px); lbound_permx px = OwnPerm \<rbrakk> \<Longrightarrow> eval_permx p_sub px = OwnPerm"   
  apply (cut_tac px="px" and p_sub="p_sub" in lbound_eval_permx)
   apply (auto)
  apply (case_tac "eval_permx p_sub px")
    apply (auto)
  done
    
fun pvar_crn2 where
 "pvar_crn2 (LeqCrn2 px q) = (pvar_set px \<union> pvar_set_perm q)"
| "pvar_crn2 (DisjCrn2 px qx) = (pvar_set px \<union> pvar_set qx)" 
| "pvar_crn2 (MiniDisjCrn2 px qx) = (pvar_set px \<union> pvar_set qx)"

fun pvar_crn_list2 where
  "pvar_crn_list2 [] = {}"
| "pvar_crn_list2 (c # c_t) = (pvar_crn2 c \<union> pvar_crn_list2 c_t)"  
  (*
fun nz_sub_crn where
  "nz_sub_crn p_sub (LeqCrn2 px q) = (nz_sub p_sub px \<and> nz_sub p_sub (XPerm q))"  
| "nz_sub_crn p_sub (DisjCrn2 px qx) = (nz_sub p_sub px \<and> nz_sub p_sub qx)"  
| "nz_sub_crn p_sub (MiniDisjCrn2 px qx) = (nz_sub p_sub px \<and> nz_sub p_sub qx)"
  
fun nz_sub_crn_list where
  "nz_sub_crn_list p_sub [] = True"
| "nz_sub_crn_list p_sub (c # c_t) = (nz_sub_crn p_sub c \<and> nz_sub_crn_list p_sub c_t)"
  *)
  
lemma subset_nz_sub: "\<lbrakk> nz_sub p_sub ds'; ds \<subseteq> ds' \<rbrakk> \<Longrightarrow> nz_sub p_sub ds"  
  apply (simp add: nz_sub_def)
  apply (auto)
  done
    
lemma union_nz_sub: "\<lbrakk> nz_sub p_sub ds; nz_sub p_sub ds' \<rbrakk> \<Longrightarrow> nz_sub p_sub (ds \<union> ds')"  
  apply (simp add: nz_sub_def)
  done    
  
lemma select_nz_sub_crn: "\<lbrakk> select_list f c_list = Some (c, c_t); nz_sub p_sub (pvar_crn_list2 c_list) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_crn2 c)"
  apply (induct c_list arbitrary: c c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
   apply (rule_tac subset_nz_sub)
    apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  apply (cut_tac p_sub="p_sub" and ds="pvar_crn_list2 c_list" and ds'="pvar_crn2 a \<union> pvar_crn_list2 c_list" in subset_nz_sub)
    apply (auto)
  done

lemma select_nz_sub_crn_list: "\<lbrakk> select_list f c_list = Some (c, c_t); nz_sub p_sub (pvar_crn_list2 c_list) \<rbrakk> \<Longrightarrow>
  nz_sub p_sub (pvar_crn_list2 c_t)"    
  apply (induct c_list arbitrary: c c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
   apply (rule_tac subset_nz_sub)
    apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  apply (rule_tac union_nz_sub)
   apply (rule_tac subset_nz_sub)
    apply (auto)
  apply (cut_tac p_sub="p_sub" and ds="pvar_crn_list2 c_list" and ds'="pvar_crn2 a \<union> pvar_crn_list2 c_list" in subset_nz_sub)
    apply (auto)
  done

lemma sub1_pvar_set_perm: "pvar_set_perm (sub1_perm p r) \<subseteq> pvar_set_perm p"     
  apply (case_tac p)
   apply (auto)
  done
    
lemma sub1_pvar_set: "pvar_set (sub1_permx px r) \<subseteq> pvar_set px"    
  apply (induct px)
      apply (auto)
   apply (case_tac x)
    apply (auto)
   apply (case_tac "x2 = r")
    apply (auto)
  apply (case_tac "x2a")
   apply (auto)
  apply (case_tac "x2 = r")
   apply (auto)
  done
  
lemma sub1_pvar_crn: "pvar_crn2 (sub1_crn c r) \<subseteq> pvar_crn2 c"    
  apply (case_tac c)
    apply (auto)
       apply (cut_tac px="x11" and r="r" in sub1_pvar_set)
       apply (auto)
      apply (cut_tac p="x12" and r="r" in sub1_pvar_set_perm)
      apply (auto)
     apply (cut_tac px="x21" and r="r" in sub1_pvar_set)
     apply (auto)
    apply (cut_tac px="x22" and r="r" in sub1_pvar_set)
    apply (auto)
   apply (cut_tac px="x31" and r="r" in sub1_pvar_set)
   apply (auto)
  apply (cut_tac px="x32" and r="r" in sub1_pvar_set)
  apply (auto)
  done
    
lemma sub1_pvar_crn_list: "pvar_crn_list2 (sub1_crn_list c_list r) \<subseteq> pvar_crn_list2 c_list"    
  apply (induct c_list)
   apply (auto)
  apply (cut_tac c="a" and r="r" in sub1_pvar_crn)
  apply (auto)
  done

lemma sub1_nz_sub_crn_list: "\<lbrakk> nz_sub p_sub (pvar_crn_list2 c_list) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_crn_list2 (sub1_crn_list c_list r))"
  apply (rule_tac subset_nz_sub)
   apply (simp)
  apply (rule_tac sub1_pvar_crn_list)
  done    
    
lemma sub1_eval_permx: "\<lbrakk> p_sub r = OwnPerm \<rbrakk> \<Longrightarrow> eval_permx p_sub px = eval_permx p_sub (sub1_permx px r)"    
  apply (induct px)
      apply (auto)
    apply (case_tac x)
     apply (auto)
   apply (case_tac x2a)
    apply (auto)
   apply (case_tac "x2 = r")
    apply (auto)
  apply (case_tac x2a)
   apply (auto)
  apply (case_tac "x2 = r")
   apply (auto)
  done

lemma sub1_sol_sat_crn: "\<lbrakk> sol_sat_crn2 p_sub c; p_sub r = OwnPerm \<rbrakk> \<Longrightarrow> sol_sat_crn2 p_sub (sub1_crn c r)"    
  apply (case_tac c)
    apply (auto)
            apply (cut_tac p_sub="p_sub" and px="x11" and r="r" in sub1_eval_permx)
             apply (auto)
            apply (case_tac x12)
             apply (auto)
           apply (cut_tac p_sub="p_sub" and px="x21" and r="r" in sub1_eval_permx)
            apply (auto)
          apply (cut_tac p_sub="p_sub" and px="x22" and r="r" in sub1_eval_permx)
           apply (auto)
         apply (cut_tac p_sub="p_sub" and px="x21" and r="r" in sub1_eval_permx)
          apply (auto)
        apply (cut_tac p_sub="p_sub" and px="x21" and r="r" in sub1_eval_permx)
         apply (auto)
       apply (cut_tac p_sub="p_sub" and px="x22" and r="r" in sub1_eval_permx)
        apply (auto)
      apply (cut_tac p_sub="p_sub" and px="x22" and r="r" in sub1_eval_permx)
       apply (auto)
     apply (cut_tac p_sub="p_sub" and px="x22" and r="r" in sub1_eval_permx)
      apply (auto)
    apply (cut_tac p_sub="p_sub" and px="x22" and r="r" in sub1_eval_permx)
     apply (auto)
   apply (cut_tac p_sub="p_sub" and px="x31" and r="r" in sub1_eval_permx)
    apply (auto)
  apply (cut_tac p_sub="p_sub" and px="x32" and r="r" in sub1_eval_permx)
   apply (auto)
  done
    
lemma sub1_sol_sat: "\<lbrakk> sol_sat2 p_sub c_list; p_sub r = OwnPerm \<rbrakk> \<Longrightarrow> sol_sat2 p_sub (sub1_crn_list c_list r)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac sub1_sol_sat_crn)
   apply (auto)
  done
  
    (* unsat proof *)
  
lemma cscu_ih: "\<lbrakk> \<And>c_lista. \<lbrakk> length c_lista < length c_list; complete_sol_calc c_lista = None; nz_sub p_sub (pvar_crn_list2 c_lista) \<rbrakk> \<Longrightarrow> \<not> sol_sat2 p_sub c_lista;
   length c_lista < length c_list; complete_sol_calc c_lista = None; nz_sub p_sub (pvar_crn_list2 c_lista) \<rbrakk> \<Longrightarrow> \<not> sol_sat2 p_sub c_lista"
  apply (auto)
  done
    
lemma complete_sol_calc_unsat: "\<lbrakk> complete_sol_calc c_list = None; nz_sub p_sub (pvar_crn_list2 c_list) \<rbrakk> \<Longrightarrow>  \<not> sol_sat2 p_sub c_list"    
  apply (induct "length c_list" arbitrary: c_list rule: less_induct)
  apply (auto)
    (* unroll algorithm definition *)
  apply (case_tac "\<not> (case select_list owner_crn c_list of None \<Rightarrow> Some use_semi_env
                | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = OwnPerm then complete_sol_calc_f c_t else None
                | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
                    (case complete_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some o_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then OwnPerm else o_sub r'))
                | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x) =
               None")
   apply (simp add: complete_sol_calc_def)
  apply (auto)
    (* attempt to select from list *)
  apply (case_tac "select_list owner_crn c_list")
   apply (auto)
  apply (case_tac a)
    apply (auto)
    apply (case_tac x12)
     apply (auto)
    (* inequality over permission constant. case where p \<noteq> 1 *)
     apply (case_tac "x1 \<noteq> OwnPerm")
      apply (auto)
      apply (cut_tac f="owner_crn" and c="LeqCrn2 x11 (SPerm x1)" in select_sol_sat_crn)
        apply (auto)
      apply (cut_tac f="owner_crn" and c="LeqCrn2 x11 (SPerm x1)" in select_cond_sat)
       apply (auto)
      apply (cut_tac p_sub="p_sub" and px="x11" in own_lbound_eval_permx)
        apply (cut_tac p_sub="p_sub" and c="LeqCrn2 x11 (SPerm x1)" and c_list="c_list" in select_nz_sub_crn)
          apply (auto)
      apply (case_tac x1)
        apply (auto)
    (* - inductive case where p = 1 *)
     apply (cut_tac c_lista="b" and c_list="c_list" in cscu_ih)
         apply (auto)
        apply (rule_tac select_less_length)
        apply (simp)
       apply (simp add: complete_sol_calc_def)
      apply (rule_tac select_nz_sub_crn_list)
       apply (auto)
     apply (cut_tac c_list="c_list" and c_t="b" in select_sol_sat)
       apply (auto)
    (* inequality over permission var *)
    apply (cut_tac c_lista="sub1_crn_list b x2" and c_list="c_list" in cscu_ih)
        apply (auto)
       apply (rule_tac t="length (sub1_crn_list b x2)" and s="length b" in subst)
        apply (rule_tac sub1_same_length)
       apply (rule_tac select_less_length)
       apply (simp)
      apply (case_tac "case select_list owner_crn (sub1_crn_list b x2) of None \<Rightarrow> Some use_semi_env
              | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = OwnPerm then complete_sol_calc_f c_t else None
              | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
                  (case complete_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some o_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then OwnPerm else o_sub r'))
              | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x")
       apply (auto)
      apply (simp add: complete_sol_calc_def)
     apply (rule_tac sub1_nz_sub_crn_list)
     apply (rule_tac select_nz_sub_crn_list)
      apply (simp_all)
    (* we know that p_sub does not assign r (x2) to 0 *)
    apply (case_tac "p_sub x2 = NoPerm")
     apply (cut_tac p_sub="p_sub" and c="LeqCrn2 x11 (SVar x2)" in select_nz_sub_crn)
       apply (auto)
     apply (simp add: nz_sub_def)
     apply (auto)
    (* if the constraints are solvable, then the solution assigns either 1 or * to r. we know an assignment of * will fail. an assignment of 1
        means sub1_crn_list should be solvable, a contradiction *)
    apply (case_tac "p_sub x2")
      apply (auto)
     apply (cut_tac p_sub="p_sub" and c="LeqCrn2 x11 (SVar x2)" in select_sol_sat_crn)
       apply (auto)
     apply (cut_tac f="owner_crn" and c="LeqCrn2 x11 (SVar x2)" in select_cond_sat)
      apply (auto)
     apply (cut_tac p_sub="p_sub" and px="x11" in lbound_eval_permx)
      apply (cut_tac p_sub="p_sub" and c="LeqCrn2 x11 (SVar x2)" in select_nz_sub_crn)
        apply (auto)
      apply (rule_tac ds'="insert x2 (pvar_set x11)" in subset_nz_sub)
       apply (auto)
     apply (case_tac "eval_permx p_sub x11")
       apply (auto)
    apply (cut_tac p_sub="p_sub" and c_list="b" and r="x2" in sub1_sol_sat)
      apply (auto)
    apply (rule_tac select_sol_sat)
     apply (auto)
    (* disjointness cases, should never happen *)
   apply (cut_tac f="owner_crn" and c="DisjCrn2 x21 x22" in select_cond_sat)
    apply (auto)
  apply (cut_tac f="owner_crn" and c="MiniDisjCrn2 x31 x32" in select_cond_sat)
   apply (auto)
  done
    
lemma add_eval_perm: "eval_perm p_sub (sub1_perm p r) = eval_perm (\<lambda>r'. if r' = r then OwnPerm else p_sub r') p"       
  apply (case_tac p)
   apply (auto)
  done
  
lemma add_eval_permx: "eval_permx p_sub (sub1_permx px r) = eval_permx (\<lambda>r'. if r' = r then OwnPerm else p_sub r') px"       
  apply (induct px)
      apply (auto)
    apply (case_tac x)
     apply (auto)
   apply (case_tac x2a)
    apply (auto)
   apply (case_tac "x2 = r")
    apply (auto)
  apply (case_tac x2a)
   apply (auto)
  apply (case_tac "x2 = r")
   apply (auto)
  done
  
lemma add_sol_sat_crn: "\<lbrakk> sol_sat_crn2 p_sub (sub1_crn c r) \<rbrakk> \<Longrightarrow> sol_sat_crn2 (\<lambda>r'. if r' = r then OwnPerm else p_sub r') c"   
  apply (case_tac c)
    apply (auto)
            apply (simp add: add_eval_permx)
            apply (simp add: add_eval_perm)
           apply (simp_all add: add_eval_permx)
  done
  
lemma add_sol_sat: "\<lbrakk> sol_sat2 p_sub (sub1_crn_list c_list r) \<rbrakk> \<Longrightarrow> sol_sat2 (\<lambda>r'. if r' = r then OwnPerm else p_sub r') c_list"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac add_sol_sat_crn)
  apply (simp)
  done    
    
lemma step3_solve_iter: "\<lbrakk> select_list owner_crn c_list = Some (LeqCrn2 px (SVar r), c_t);
  sol_sat2 p_sub (sub1_crn_list c_t r) \<rbrakk> \<Longrightarrow> sol_sat2 (\<lambda>r'. if r' = r then OwnPerm else  p_sub r') c_list"
  apply (rule_tac select_sol_sat_split)
    apply (auto)
  apply (rule_tac add_sol_sat)
  apply (auto)
  done    

fun apply_zero_perm where
  "apply_zero_perm f_sub (SPerm p) = (SPerm p)"
| "apply_zero_perm f_sub (SVar r) = (if f_sub r then SVar r else SPerm NoPerm)"  
  
fun apply_zero_permx where    
  "apply_zero_permx f_sub (XPerm p) = XPerm (apply_zero_perm f_sub p)"
| "apply_zero_permx f_sub (XType a) = XType a"
| "apply_zero_permx f_sub (XComp px qx) = XComp (apply_zero_permx f_sub px) (apply_zero_permx f_sub qx)"
| "apply_zero_permx f_sub (XLift px q) = XLift (apply_zero_permx f_sub px) (apply_zero_perm f_sub q)"
| "apply_zero_permx f_sub (XIfZero px qx) = XIfZero (apply_zero_permx f_sub px) (apply_zero_permx f_sub qx)"  
  
fun apply_zero_crn where
  "apply_zero_crn f_sub (LeqCrn2 px q) = LeqCrn2 (apply_zero_permx f_sub px) (apply_zero_perm f_sub q)"
| "apply_zero_crn f_sub (DisjCrn2 px qx) = DisjCrn2 (apply_zero_permx f_sub px) (apply_zero_permx f_sub qx)"
| "apply_zero_crn f_sub (MiniDisjCrn2 px qx) = MiniDisjCrn2 (apply_zero_permx f_sub px) (apply_zero_permx f_sub qx)"
  
fun apply_zero_crn_list where
  "apply_zero_crn_list f_sub [] = []"
| "apply_zero_crn_list f_sub (c # c_t) = (apply_zero_crn f_sub c # apply_zero_crn_list f_sub c_t)"
     
definition final_sub where
  "final_sub f_sub o_sub = (\<lambda> x. if f_sub x then o_sub x else NoPerm)"
  
lemma none_eval_permx: "\<lbrakk> lbound_permx px = NoPerm \<rbrakk> \<Longrightarrow> eval_permx use_semi_env px = NoPerm"   
  apply (induct px)
      apply (auto)
    (* base case *)
      apply (case_tac x)
       apply (auto)
    (* comp case *)
     apply (case_tac "lbound_permx px1")
       apply (auto)
      apply (case_tac "lbound_permx px2")
        apply (auto)
     apply (case_tac "lbound_permx px2")
       apply (auto)
    (* lift case 1 *)
    apply (case_tac "lbound_perm x2a = OwnPerm \<and> lbound_permx px \<noteq> NoPerm")
     apply (auto)
    (* lift case 2 *)
   apply (case_tac "lbound_perm x2a = OwnPerm \<and> lbound_permx px \<noteq> NoPerm")
    apply (auto)
    (* if zero case *)
  apply (case_tac "lbound_permx px1 = NoPerm")
   apply (auto)
  done

lemma use_eval_permx: "\<lbrakk> lbound_permx px \<noteq> OwnPerm \<rbrakk> \<Longrightarrow> eval_permx use_semi_env px \<noteq> OwnPerm"  
  apply (induct px)
      apply (auto)
    (* base case *)
      apply (case_tac x)
       apply (auto)
      apply (simp add: use_semi_env_def)
    (* comp case *)
     apply (case_tac "lbound_permx px1 = OwnPerm")
      apply (simp)
     apply (case_tac "lbound_permx px2 = OwnPerm")
      apply (auto)
      apply (case_tac "lbound_permx px1")
        apply (auto)
     apply (case_tac "eval_permx use_semi_env px1")
       apply (auto)
      apply (case_tac "eval_permx use_semi_env px2")
        apply (auto)
     apply (case_tac "eval_permx use_semi_env px2")
       apply (auto)
    (* lift case 1. q (x2a) \<noteq> 1, a contradiction *)
    apply (case_tac "lbound_perm x2a = OwnPerm")
     apply (auto)
     apply (case_tac "lbound_permx px \<noteq> NoPerm")
      apply (auto)
     apply (rule_tac none_eval_permx)
     apply (simp)
    apply (case_tac x2a)
     apply (auto)
    apply (simp add: use_semi_env_def)
    (* lift case 2. *)
   apply (case_tac "lbound_perm x2a = OwnPerm \<and> lbound_permx px \<noteq> NoPerm")
    apply (auto)
    (* if zero case *)
  apply (case_tac "lbound_permx px1 = NoPerm")
   apply (auto)
  apply (cut_tac px="px1" in none_eval_permx)
   apply (auto)
  done
    
lemma non_owner_crn_sat: "\<lbrakk> \<not> owner_crn c; sol_sat_crn2 p_sub c; nz_sub p_sub (pvar_crn2 c) \<rbrakk> \<Longrightarrow> sol_sat_crn2 use_semi_env c"  
  apply (case_tac c)
    apply (auto)
    (* inequality case. we must show that (USE)rho \<le> (USE)p given (sigma)rho \<le> (sigma)p, and rho has a non-1 lower bound.
      we first consider (sigma)p = 0. in this case sigma(rho) = 0, and rho's lower bound must be 0, meaning (USE)rho = 0
    *)
            apply (case_tac "eval_perm p_sub x12 = NoPerm")
             apply (case_tac "eval_permx p_sub x11")
               apply (auto)
             apply (cut_tac p_sub="p_sub" and px="x11" in lbound_eval_permx)
              apply (rule_tac subset_nz_sub)
               apply (auto)
             apply (cut_tac px="x11" in none_eval_permx)
              apply (auto)
             apply (case_tac "lbound_permx x11")
               apply (auto)
    (* - otherwise, since (sigma)p != 0, we know that (USE)p !=  0 *)
            apply (case_tac "eval_perm use_semi_env x12 = NoPerm")
             apply (case_tac x12)
              apply (case_tac x1)
                apply (auto)
             apply (simp add: use_semi_env_def)
    (* - since the lower bound of rho \<noteq> 1, (USE)rho \<noteq> 1, and our equality holds *)
            apply (cut_tac px="x11" in use_eval_permx)
             apply (auto)
            apply (case_tac "eval_perm use_semi_env x12")
              apply (auto)
            apply (case_tac "eval_permx use_semi_env x11")
              apply (auto)
    (* disjointness cases hold because of lower bounds *)
           apply (cut_tac p_sub="p_sub" and px="x21" in lbound_eval_permx)
            apply (rule_tac subset_nz_sub)
             apply (auto)
           apply (case_tac "lbound_permx x21 = OwnPerm")
            apply (case_tac "eval_permx p_sub x21")
              apply (auto)
           apply (cut_tac px="x21" in use_eval_permx)
            apply (auto)
    (* - ex case 1 *)
          apply (cut_tac p_sub="p_sub" and px="x22" in lbound_eval_permx)
           apply (rule_tac subset_nz_sub)
            apply (auto)
          apply (cut_tac px="x22" in use_eval_permx)
           apply (auto)
          apply (case_tac "eval_permx p_sub x22")
            apply (auto)
    (* - ex case 2 *)
          apply (cut_tac p_sub="p_sub" and px="x21" in lbound_eval_permx)
           apply (rule_tac subset_nz_sub)
            apply (auto)
         apply (cut_tac px="x21" in none_eval_permx)
          apply (auto)
         apply (case_tac "lbound_permx x21")
           apply (auto)
    (* - ex case 3 *)
        apply (cut_tac p_sub="p_sub" and px="x21" in lbound_eval_permx)
         apply (rule_tac subset_nz_sub)
          apply (auto)
        apply (cut_tac px="x21" in none_eval_permx)
         apply (auto)
        apply (case_tac "lbound_permx x21")
          apply (auto)
    (* - case 2 *)
       apply (cut_tac p_sub="p_sub" and px="x22" in lbound_eval_permx)
        apply (rule_tac subset_nz_sub)
         apply (auto)
       apply (case_tac "lbound_permx x22")
         apply (auto)
       apply (rule_tac none_eval_permx)
       apply (auto)
    (* - ex case 4 *)
      apply (cut_tac p_sub="p_sub" and px="x22" in lbound_eval_permx)
       apply (rule_tac subset_nz_sub)
        apply (auto)
      apply (cut_tac px="x22" in use_eval_permx)
       apply (auto)
    (* - ex case 5 *)
     apply (cut_tac p_sub="p_sub" and px="x21" in lbound_eval_permx)
      apply (rule_tac subset_nz_sub)
       apply (auto)
     apply (cut_tac px="x21" in use_eval_permx)
      apply (auto)
    apply (case_tac "eval_permx p_sub x21")
      apply (auto)
    (* - ex case 5 *)
    apply (cut_tac p_sub="p_sub" and px="x21" in lbound_eval_permx)
     apply (rule_tac subset_nz_sub)
      apply (auto)
    apply (case_tac "lbound_permx x21")
      apply (auto)
    apply (rule_tac none_eval_permx)
    apply (auto)
    (* - case 3 *)
   apply (cut_tac p_sub="p_sub" and px="x31" in lbound_eval_permx)
    apply (rule_tac subset_nz_sub)
     apply (auto)
   apply (case_tac "lbound_permx x31 = OwnPerm")
    apply (case_tac "eval_permx p_sub x31")
      apply (auto)
   apply (cut_tac px="x31" in use_eval_permx)
    apply (auto)
    (* - case 3 *)
  apply (cut_tac p_sub="p_sub" and px="x32" in lbound_eval_permx)
   apply (rule_tac subset_nz_sub)
    apply (auto)
  apply (case_tac "lbound_permx x32")
    apply (auto)
  apply (rule_tac none_eval_permx)
  apply (auto)
  done
  
  (*
      this lemma states that if no more ownership constraints can be taken - if the constraint set
      is solvable (with a non-zero solution), it is solvable with only use permissions. 
  *)
lemma step3_solve_end: "\<lbrakk> select_list owner_crn c_list = None; sol_sat2 p_sub c_list;
  nz_sub p_sub (pvar_crn_list2 c_list) \<rbrakk> \<Longrightarrow> sol_sat2 use_semi_env c_list"
  apply (induct c_list)
   apply (auto)
    (* prove constraint is valid *)
   apply (case_tac "owner_crn a")
    apply (auto)
   apply (rule_tac non_owner_crn_sat)
     apply (auto)
   apply (rule_tac subset_nz_sub)
    apply (auto)
    (* induction *)
  apply (case_tac "owner_crn a")
   apply (auto)
  apply (case_tac "select_list owner_crn c_list")
   apply (auto)
  apply (cut_tac ds="pvar_crn_list2 c_list" and p_sub="p_sub" in subset_nz_sub)
    apply (auto)
  done

lemma final_sub_eval_perm: "eval_perm o_sub (apply_zero_perm f_sub p) = eval_perm (final_sub f_sub o_sub) p"    
  apply (case_tac p)
   apply (auto)
   apply (simp add: final_sub_def)
  apply (simp add: final_sub_def)
  done

lemma final_sub_eval_permx: "eval_permx o_sub (apply_zero_permx f_sub px) = eval_permx (final_sub f_sub o_sub) px"    
  apply (induct px)
      apply (auto)
    apply (simp add: final_sub_eval_perm)
   apply (simp add: final_sub_eval_perm)
  apply (simp add: final_sub_eval_perm)
  done

lemma final_sub_sol_crn: "\<lbrakk> sol_sat_crn2 o_sub (apply_zero_crn f_sub c) \<rbrakk> \<Longrightarrow> sol_sat_crn2 (final_sub f_sub o_sub) c"    
  apply (case_tac c)
    apply (auto)
            apply (simp add: final_sub_eval_permx)
            apply (simp add: final_sub_eval_perm)
           apply (simp_all add: final_sub_eval_permx)
  done
    
lemma final_sub_sol_sat: "\<lbrakk> sol_sat2 o_sub (apply_zero_crn_list f_sub c_list) \<rbrakk> \<Longrightarrow> sol_sat2 (final_sub f_sub o_sub) c_list"    
  apply (induct c_list)
   apply (auto)
  apply (simp add: final_sub_sol_crn)
  done

    
lemma apply_zero_eval_perm: "leq_perm (eval_perm p_sub (apply_zero_perm f_sub p)) (eval_perm p_sub p)"    
  apply (case_tac p)
   apply (auto)
   apply (case_tac x1)
     apply (auto)
  apply (case_tac "p_sub x2")
    apply (auto)
  done

lemma apply_zero_eval_permx: "leq_perm (eval_permx p_sub (apply_zero_permx f_sub px)) (eval_permx p_sub px)"    
  apply (induct px)
      apply (auto)
      apply (rule_tac apply_zero_eval_perm)
     apply (rule_tac dist_union_leq_perm)
      apply (rule_tac union_leq_perm1)
      apply (simp)
     apply (rule_tac union_leq_perm2)
     apply (simp)
    apply (cut_tac p_sub="p_sub" and f_sub="f_sub" and p="x2a" in apply_zero_eval_perm)
    apply (case_tac "eval_perm p_sub x2a")
      apply (auto)
   apply (case_tac " eval_permx p_sub (apply_zero_permx f_sub px)")
     apply (auto)
  apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub px1)")
    apply (auto)
  done
    
lemma none_apply_zero_eval_permx: "\<lbrakk> \<not> semi_sol_permx f_sub px \<rbrakk> \<Longrightarrow> eval_permx p_sub (apply_zero_permx f_sub px) = NoPerm"    
  apply (induct px)
      apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (case_tac "x1 = NoPerm")
   apply (auto)
  done
 
lemma apply_zero_eval_perm_rev: "\<lbrakk> semi_sol_perm f_sub p \<rbrakk> \<Longrightarrow>
  leq_perm (eval_perm p_sub p) (eval_perm p_sub (apply_zero_perm f_sub p))"        
  apply (case_tac p)
   apply (auto)
   apply (case_tac x1)
     apply (auto)
  apply (case_tac "p_sub x2")
    apply (auto)
  done
    
lemma apply_zero_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub c; sol_sat_crn2 p_sub c \<rbrakk> \<Longrightarrow> sol_sat_crn2 p_sub (apply_zero_crn f_sub c)"    
  apply (case_tac c)
    apply (auto)
             apply (simp add: none_apply_zero_eval_permx)
            apply (rule_tac q="eval_permx p_sub x11" in trans_leq_perm)
             apply (rule_tac apply_zero_eval_permx)
            apply (rule_tac q="eval_perm p_sub x12" in trans_leq_perm)
             apply (simp)
            apply (rule_tac apply_zero_eval_perm_rev)
            apply (simp)
           apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x21" in apply_zero_eval_permx)
           apply (auto)
           apply (case_tac "eval_permx p_sub x21")
             apply (auto)
          apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x22" in apply_zero_eval_permx)
          apply (auto)
          apply (case_tac "eval_permx p_sub x22")
            apply (auto)
         apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x21" in apply_zero_eval_permx)
         apply (auto)
        apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x21" in apply_zero_eval_permx)
        apply (auto)
        apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub x21)")
          apply (auto)
       apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x22" in apply_zero_eval_permx)
       apply (auto)
       apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub x22)")
         apply (auto)
      apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x22" in apply_zero_eval_permx)
      apply (auto)
     apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x22" in apply_zero_eval_permx)
     apply (auto)
     apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub x22)")
       apply (auto)
    apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x21" in apply_zero_eval_permx)
    apply (auto)
    apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub x21)")
      apply (auto)
   apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x31" in apply_zero_eval_permx)
   apply (auto)
   apply (case_tac "eval_permx p_sub x31")
     apply (auto)
  apply (cut_tac f_sub="f_sub" and p_sub="p_sub" and px="x32" in apply_zero_eval_permx)
  apply (auto)
  apply (case_tac "eval_permx p_sub (apply_zero_permx f_sub x32)")
    apply (auto)
  done
    
lemma apply_zero_sol_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list; sol_sat2 p_sub c_list \<rbrakk> \<Longrightarrow> sol_sat2 p_sub (apply_zero_crn_list f_sub c_list)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac apply_zero_sol_crn)
   apply (auto)
  done

lemma apply_zero_nz_sub_perm: "\<lbrakk> leq_semi_env f_sub (semi_sol_corr p_sub) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_set_perm (apply_zero_perm f_sub p))"    
  apply (case_tac p)
   apply (auto)
    apply (simp add: nz_sub_def)
   apply (simp add: nz_sub_def)
   apply (simp add: leq_semi_env_def)
   apply (simp add: semi_sol_corr_def)
   apply (erule_tac x="x2" in allE)
   apply (auto)
  apply (simp add: nz_sub_def)
  done
    
lemma apply_zero_nz_sub_permx: "\<lbrakk> leq_semi_env f_sub (semi_sol_corr p_sub) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_set (apply_zero_permx f_sub px))"    
  apply (induct px)
      apply (auto)
      apply (rule_tac apply_zero_nz_sub_perm)
      apply (simp)
     apply (simp add: nz_sub_def)
    apply (rule_tac union_nz_sub)
     apply (auto)
   apply (rule_tac union_nz_sub)
    apply (auto)
   apply (rule_tac apply_zero_nz_sub_perm)
   apply (simp)
  apply (rule_tac union_nz_sub)
   apply (auto)
  done
    
lemma apply_zero_nz_sub_crn: "\<lbrakk> leq_semi_env f_sub (semi_sol_corr p_sub) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_crn2 (apply_zero_crn f_sub c))"    
  apply (case_tac c)
    apply (auto)
    apply (rule_tac union_nz_sub)
     apply (rule_tac apply_zero_nz_sub_permx)
     apply (simp)
    apply (rule_tac apply_zero_nz_sub_perm)
    apply (simp)
   apply (rule_tac union_nz_sub)
    apply (rule_tac apply_zero_nz_sub_permx)
    apply (simp)
   apply (rule_tac apply_zero_nz_sub_permx)
   apply (simp)
  apply (rule_tac union_nz_sub)
   apply (rule_tac apply_zero_nz_sub_permx)
   apply (simp)
  apply (rule_tac apply_zero_nz_sub_permx)
  apply (simp)
  done
    
lemma apply_zero_nz_sub_clist: "\<lbrakk> leq_semi_env f_sub (semi_sol_corr p_sub) \<rbrakk> \<Longrightarrow> nz_sub p_sub (pvar_crn_list2 (apply_zero_crn_list f_sub c_list))"    
  apply (induct c_list)
   apply (auto)
   apply (simp add: nz_sub_def)
  apply (rule_tac union_nz_sub)
   apply (auto)
  apply (rule_tac apply_zero_nz_sub_crn)
  apply (simp)
  done
    
lemma apply_zero_same_length: "length (apply_zero_crn_list f_sub c_list) = length c_list"
  apply (induct c_list)
   apply (auto)
  done

lemma apply_zero_semi_sol_permx_rev: "\<lbrakk> semi_sol_permx p_sub (apply_zero_permx f_sub px) \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub px"    
  apply (induct px)
      apply (auto)
  apply (case_tac x)
   apply (auto)
  apply (case_tac "f_sub x2")
   apply (auto)
  done
    
lemma apply_zero_semi_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub c \<rbrakk> \<Longrightarrow> semi_sol_crn2 f_sub (apply_zero_crn f_sub c)"    
  apply (case_tac c)
    apply (auto)
   apply (cut_tac f_sub="f_sub" and px="x11" in apply_zero_semi_sol_permx_rev)
    apply (auto)
  apply (case_tac x12)
   apply (auto)
  done
    
lemma apply_zero_semi_sol_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list \<rbrakk> \<Longrightarrow> semi_sol_sat2 f_sub (apply_zero_crn_list f_sub c_list)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac apply_zero_semi_sol_crn)
  apply (auto)
  done

lemma double_apply_zero_permx: "apply_zero_permx f_sub (apply_zero_permx f_sub px) = apply_zero_permx f_sub px"    
  apply (induct px)
      apply (auto)
   apply (case_tac x)
    apply (auto)
  apply (case_tac x2a)
   apply (auto)
  done
    
lemma double_apply_zero_crn: "apply_zero_crn f_sub (apply_zero_crn f_sub c) = apply_zero_crn f_sub c"    
  apply (case_tac c)
   apply (auto)
       apply (rule_tac double_apply_zero_permx)
      apply (case_tac x12)
       apply (auto)
     apply (rule_tac double_apply_zero_permx)
    apply (rule_tac double_apply_zero_permx)
   apply (rule_tac double_apply_zero_permx)
  apply (rule_tac double_apply_zero_permx)
  done
    
lemma double_apply_zero_crn_list: "apply_zero_crn_list f_sub (apply_zero_crn_list f_sub c_list) = apply_zero_crn_list f_sub c_list"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac double_apply_zero_crn)
  done

lemma select_apply_zero_crn_list: "\<lbrakk> select_list f (apply_zero_crn_list f_sub c_list) = Some (c, c_t) \<rbrakk> \<Longrightarrow> apply_zero_crn_list f_sub c_t = c_t"    
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f (apply_zero_crn f_sub a)")
   apply (auto)
   apply (rule_tac double_apply_zero_crn_list)
  apply (case_tac "select_list f (apply_zero_crn_list f_sub c_list)")
   apply (auto)
  apply (rule_tac double_apply_zero_crn)
  done

lemma select_apply_zero_crn: "\<lbrakk> select_list f (apply_zero_crn_list f_sub c_list) = Some (c, c_t) \<rbrakk> \<Longrightarrow> apply_zero_crn f_sub c = c"        
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f (apply_zero_crn f_sub a)")
   apply (auto)
   apply (rule_tac double_apply_zero_crn)
  apply (case_tac "select_list f (apply_zero_crn_list f_sub c_list)")
   apply (auto)
  done
    
lemma comm_sub1_apply_zero_permx: "\<lbrakk> f_sub x \<rbrakk> \<Longrightarrow>
  sub1_permx (apply_zero_permx f_sub px) x = apply_zero_permx f_sub (sub1_permx px x)"        
  apply (induct px)
      apply (auto)
   apply (case_tac xa)
    apply (auto)
  apply (case_tac x2a)
   apply (auto)
  done
    
lemma comm_sub1_apply_zero_crn: "\<lbrakk> f_sub x \<rbrakk> \<Longrightarrow>
  sub1_crn (apply_zero_crn f_sub c) x = apply_zero_crn f_sub (sub1_crn c x)"    
  apply (case_tac c)
    apply (auto)
       apply (simp_all add: comm_sub1_apply_zero_permx)
  apply (case_tac x12)
   apply (auto)
  done

lemma comm_sub1_apply_zero_crn_list: "\<lbrakk> f_sub x \<rbrakk> \<Longrightarrow>
  sub1_crn_list (apply_zero_crn_list f_sub c_list) x = apply_zero_crn_list f_sub (sub1_crn_list c_list x)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac comm_sub1_apply_zero_crn)
  apply (simp)
  done  
  
lemma cscs_ih: "\<lbrakk> \<And>c_lista f_sub o_sub p_sub.
           \<lbrakk>length c_lista < length c_list; semi_sol_sat2 f_sub c_lista; leq_semi_env f_sub (semi_sol_corr p_sub);
            complete_sol_calc (apply_zero_crn_list f_sub c_lista) = Some o_sub; sol_sat2 p_sub c_lista\<rbrakk>
           \<Longrightarrow> sol_sat2 o_sub (apply_zero_crn_list f_sub c_lista); length c_lista < length c_list; semi_sol_sat2 f_sub c_lista; leq_semi_env f_sub (semi_sol_corr p_sub);
            complete_sol_calc (apply_zero_crn_list f_sub c_lista) = Some o_sub; sol_sat2 p_sub c_lista \<rbrakk> \<Longrightarrow>
    sol_sat2 o_sub (apply_zero_crn_list f_sub c_lista)"
  apply (auto)
  done

lemma complete_sol_calc_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list; leq_semi_env f_sub (semi_sol_corr p_sub);
  complete_sol_calc (apply_zero_crn_list f_sub c_list) = Some o_sub; sol_sat2 p_sub c_list \<rbrakk> \<Longrightarrow> sol_sat2 o_sub (apply_zero_crn_list f_sub c_list)"
  apply (induct "length c_list" arbitrary: c_list f_sub o_sub p_sub rule: less_induct)
  apply (case_tac "\<not> (case select_list owner_crn (apply_zero_crn_list f_sub c_list) of None \<Rightarrow> Some use_semi_env
         | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = OwnPerm then complete_sol_calc_f c_t else None
         | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
             (case complete_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some o_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then OwnPerm else o_sub r'))
         | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x) =
        Some o_sub")
   apply (simp add: complete_sol_calc_def)
  apply (auto)
  apply (case_tac "select_list owner_crn (apply_zero_crn_list f_sub c_list)")
   apply (auto)
    (* base case. *)
   apply (rule_tac p_sub="p_sub" in step3_solve_end)
     apply (auto)
    apply (rule_tac apply_zero_sol_sat)
     apply (simp_all)
   apply (rule_tac apply_zero_nz_sub_clist)
   apply (simp)
    (* case analysis over constraint *)
  apply (case_tac a)
    apply (auto)
  apply (case_tac x12)
   apply (auto)
    (* - inequality constraint. permission case *)
   apply (cut_tac c_list="c_list" and c_lista="b" and p_sub="p_sub" and f_sub="f_sub" and o_sub="o_sub" in cscs_ih)
        apply (auto)
       apply (rule_tac t="length c_list" and s="length (apply_zero_crn_list f_sub c_list)" in subst)
        apply (rule_tac apply_zero_same_length)
       apply (rule_tac select_less_length)
       apply (auto)
      apply (rule_tac select_semi_sol)
       apply (auto)
      apply (rule_tac apply_zero_semi_sol_sat)
      apply (auto)
     apply (simp add: select_apply_zero_crn_list)
     apply (simp add: complete_sol_calc_def)
     apply (case_tac "x1 = OwnPerm")
      apply (auto)
    apply (rule_tac select_sol_sat)
     apply (auto)
    apply (rule_tac apply_zero_sol_sat)
     apply (auto)
   apply (rule_tac f="owner_crn" and c="LeqCrn2 x11 (SPerm x1)" and c_t="b" in select_sol_sat_split)
     apply (auto)
    apply (case_tac "x1 = OwnPerm")
     apply (auto)
   apply (simp add: select_apply_zero_crn_list)
    (* - inequality constraint. var case *)
  apply (case_tac "case select_list owner_crn (sub1_crn_list b x2) of None \<Rightarrow> Some use_semi_env
              | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = OwnPerm then complete_sol_calc_f c_t else None
              | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
                  (case complete_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some o_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then OwnPerm else o_sub r'))
              | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x")
   apply (auto)
    (* - given a as the solution for b[1/x2], we want to show that a + {x2: 1} is the solution for c_list. *)
  apply (rule_tac px="x11" and c_t="b" in step3_solve_iter)
   apply (simp)
    (* - to accurately say that a is the solution for b[1/x2], we need to know that b is still in a gamma applied form.
        we can do this because x2 is not a variable in f_sub *)
  apply (rule_tac t="b" and s="apply_zero_crn_list f_sub b" in subst)
   apply (simp add: select_apply_zero_crn_list)
  apply (cut_tac c_list="c_list" and c="LeqCrn2 x11 (SVar x2)" in select_apply_zero_crn)
   apply (simp_all)
  apply (case_tac "f_sub x2")
   apply (auto)
  apply (simp add: comm_sub1_apply_zero_crn_list)
    (* with this we are able to induct on b[1/x2] *)
  apply (rule_tac cscs_ih)
       apply (auto)
    (* - decreasing length *)
     apply (rule_tac t="length (sub1_crn_list b x2)" and s="length b" in subst)
      apply (rule_tac sub1_same_length)
     apply (rule_tac t="length c_list" and s="length (apply_zero_crn_list f_sub c_list)" in subst)
      apply (rule_tac apply_zero_same_length) 
     apply (rule_tac select_less_length)
     apply (auto)
    (* - proving f_sub is still a semi-solution *)
    apply (rule_tac sub1_semi_sol_sat)
     apply (rule_tac select_semi_sol)
      apply (auto)
    apply (rule_tac apply_zero_semi_sol_sat)
    apply (auto)
    (* - reversing the identities used toa pply induction to show that a is the solution to b[1/x2] *)
   apply (rule_tac t="apply_zero_crn_list f_sub (sub1_crn_list b x2)"
      and s="sub1_crn_list (apply_zero_crn_list f_sub b) x2" in subst)
    apply (rule_tac comm_sub1_apply_zero_crn_list)
    apply (simp)
   apply (simp add: select_apply_zero_crn_list)
   apply (simp add: complete_sol_calc_def)
    (* - lastly, we must show that p_sub is a solution to b[1/x2]. to do this, we must show that p_sub x2 = Own. *)
  apply (case_tac "p_sub x2 \<noteq> OwnPerm")
   apply (cut_tac p_sub="p_sub" and c_list="apply_zero_crn_list f_sub c_list" and c="LeqCrn2 x11 (SVar x2)" in select_sol_sat_crn)
     apply (auto)
    apply (rule_tac apply_zero_sol_sat)
     apply (simp_all)
   apply (cut_tac f="owner_crn" and c="LeqCrn2 x11 (SVar x2)" in select_cond_sat)
    apply (auto)
   apply (cut_tac p_sub="p_sub" and px="x11" in lbound_eval_permx)
    (* > to prove that p_sub is non-zero over x11, we appeal to the fact that it is in C after the semi-solution is applied *)
    apply (rule_tac ds'="pvar_crn2 (LeqCrn2 x11 (SVar x2))" in subset_nz_sub)
     apply (rule_tac select_nz_sub_crn)
      apply (auto)
    apply (rule_tac apply_zero_nz_sub_clist)
    apply (simp)
   apply (case_tac "eval_permx p_sub x11")
     apply (auto)
   apply (case_tac "p_sub x2")
     apply (auto)
    (* since p_sub x2 = Own, the evaluation will be the same *)
  apply (rule_tac sub1_sol_sat)
   apply (auto)
  apply (rule_tac c_list="apply_zero_crn_list f_sub c_list" in select_sol_sat)
   apply (rule_tac apply_zero_sol_sat)
    apply (simp_all)
  done
    
    
definition full_sol_crn2 where
  "full_sol_crn2 c_list = (case min_semi_sol_calc c_list of
    None \<Rightarrow> None
    | Some f_sub \<Rightarrow> (case complete_sol_calc (apply_zero_crn_list f_sub c_list) of
      None \<Rightarrow> None
      | Some o_sub \<Rightarrow> Some (final_sub f_sub o_sub)
  ))"
  
lemma full_sol_unsat: "\<lbrakk> full_sol_crn2 c_list = None \<rbrakk> \<Longrightarrow> \<not> sol_sat2 p_sub c_list"
    (* if C is satisfiable by some p_sub, p_sub also semi-solves it *)
  apply (simp add: full_sol_crn2_def)
  apply (auto)
  apply (cut_tac p_sub="p_sub" and c_list="c_list" in corr_semi_sol)
   apply (simp_all)
    (* if our algorithm fails at the minimal semi-solution calc, it is unsatisfiable *)
  apply (case_tac "min_semi_sol_calc c_list")
   apply (auto)
   apply (cut_tac f_sub="semi_sol_corr p_sub" and c_list="c_list" in min_semi_sol_calc_unsat)
    apply (auto)
    (* otherwise we have f_sub, the minimal semi-solution *)
  apply (cut_tac f_sub="a" and c_list="c_list" in min_semi_sol_calc_sat)
   apply (simp)
    (* if our algorithm fails at the completion calc, f_sub(C) is unsatisfiable *)
  apply (case_tac "complete_sol_calc (apply_zero_crn_list a c_list)")
   apply (auto)
  apply (cut_tac p_sub="p_sub" and c_list="apply_zero_crn_list a c_list" in complete_sol_calc_unsat)
    apply (simp)
   apply (rule_tac apply_zero_nz_sub_clist)
   apply (simp add: min_semi_sol_def)
    (* if f_sub(C) is unsatisfiable, C is also unsatisfiable since f_sub semi-solves. *)
  apply (cut_tac p_sub="p_sub" and f_sub="a" and c_list="c_list" in apply_zero_sol_sat)
    apply (simp add: min_semi_sol_def)
   apply (simp_all)
  done
    
lemma full_sol_sat: "\<lbrakk> full_sol_crn2 c_list = Some p_sub; sol_sat2 p_subx c_list \<rbrakk> \<Longrightarrow> sol_sat2 p_sub c_list"  
  apply (simp add: full_sol_crn2_def)
  apply (case_tac "min_semi_sol_calc c_list")
   apply (auto)
  apply (case_tac "complete_sol_calc (apply_zero_crn_list a c_list)")
   apply (auto)
    (* f_sub (a) is the minimal semi-solution of c_list *)
  apply (cut_tac f_sub="a" and c_list="c_list" in min_semi_sol_calc_sat)
   apply (simp)
    (* the final substitution is the same as applying f_sub and then applying o_sub, which we can solve using csc_sat *)
  apply (rule_tac final_sub_sol_sat)
  apply (rule_tac p_sub="p_subx" in complete_sol_calc_sat)
     apply (simp add: min_semi_sol_def)
    apply (simp add: min_semi_sol_def)
    apply (auto)
  apply (erule_tac x="semi_sol_corr p_subx" in allE)
  apply (auto)
  apply (cut_tac p_sub="p_subx" and c_list="c_list" in corr_semi_sol)
   apply (auto)
  done
    
    
definition solve_crn_list where
  "solve_crn_list c_list = (case reduce_crn_list c_list of
    None \<Rightarrow> False
    | Some c_listx \<Rightarrow> (case full_sol_crn2 c_listx of
      None \<Rightarrow> False
      | Some p_sub \<Rightarrow> sol_sat2 p_sub c_listx
    )
  )"

lemma solve_crn_list_unsat: "\<lbrakk> \<not> solve_crn_list c_list; no_mv_crn c_list \<rbrakk> \<Longrightarrow> \<not> dir_sol_sat t_sub p_sub c_list"  
  apply (simp add: solve_crn_list_def)
  apply (case_tac "reduce_crn_list c_list")
   apply (auto)
   apply (cut_tac reduce_crn_list_unsat)
    apply (auto)
  apply (cut_tac p_sub="p_sub" and c_list="c_list" in reduce_crn_list_sat)
     apply (auto)
  apply (case_tac "full_sol_crn2 a")
   apply (auto)
   apply (cut_tac full_sol_unsat)
    apply (auto)
  apply (cut_tac p_sub="aa" and c_list="a" in full_sol_sat)
    apply (auto)
  done
    
lemma solve_crn_list_sat: "\<lbrakk> solve_crn_list c_list; no_mv_crn c_list \<rbrakk> \<Longrightarrow> (\<exists> t_sub p_sub. dir_sol_sat t_sub p_sub c_list)"
  apply (simp add: solve_crn_list_def)
  apply (case_tac "reduce_crn_list c_list")
   apply (auto)
  apply (case_tac "full_sol_crn2 a")
   apply (auto)
    (* if the solver returns a "checked" solution, since it means the original constraints must be solvable *)
  apply (cut_tac c_list="c_list" and c_listx="a" and p_sub="aa" in reduce_crn_list_satx)
     apply (auto)
  done
    
end