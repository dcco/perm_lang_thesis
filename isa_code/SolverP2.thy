theory SolverP2
  imports SolverP1b
begin
  
    (* phase 2: zero/non-zero solving *)  
 
fun semi_sol_perm where
  "semi_sol_perm f_sub (SPerm p) = (if p = NoPerm then False else True)"  
| "semi_sol_perm f_sub (SVar r) = f_sub r"  
  
fun semi_sol_permx where
  "semi_sol_permx f_sub (XPerm p) = semi_sol_perm f_sub p"
| "semi_sol_permx f_sub (XType a) = False"
| "semi_sol_permx f_sub (XComp px qx) = (semi_sol_permx f_sub px \<or> semi_sol_permx f_sub qx)"  
| "semi_sol_permx f_sub (XLift px q) = (semi_sol_permx f_sub px)"  
| "semi_sol_permx f_sub (XIfZero px qx) = (semi_sol_permx f_sub px \<and> semi_sol_permx f_sub qx)"  

fun semi_sol_crn2 where
  "semi_sol_crn2 f_sub (LeqCrn2 px q) = (semi_sol_permx f_sub px \<longrightarrow> semi_sol_perm f_sub q)"  
| "semi_sol_crn2 f_sub (DisjCrn2 px qx) = True"    
| "semi_sol_crn2 f_sub (MiniDisjCrn2 px qx) = True"
  
fun semi_sol_sat2 where
  "semi_sol_sat2 f_sub [] = True"  
| "semi_sol_sat2 f_sub (c # c_t) = (semi_sol_crn2 f_sub c \<and> semi_sol_sat2 f_sub c_t)"    
  
    (* - semi-sol correspondence *)
  
definition semi_sol_corr where
  "semi_sol_corr p_sub = (\<lambda> q. if p_sub q = NoPerm then False else True)"  
  
    (* - semi-sol ordering / minimality *)
  
definition empty_semi_env where
  "empty_semi_env = (\<lambda> x. False)"  
  
definition leq_semi_env where
  "leq_semi_env f_sub f_sub' = (\<forall> x. f_sub x \<longrightarrow> f_sub' x)"

definition min_semi_sol where
  "min_semi_sol f_sub c_list = (semi_sol_sat2 f_sub c_list \<and> (\<forall> f_sub'. semi_sol_sat2 f_sub' c_list \<longrightarrow> leq_semi_env f_sub f_sub'))"   
  
    (* - semi-sol correspondence [left] *)
  
lemma corr_semi_sol_perm: "(eval_perm p_sub p \<noteq> NoPerm) = (semi_sol_perm (semi_sol_corr p_sub) p)"  
  apply (case_tac p)
   apply (auto)
   apply (simp add: semi_sol_corr_def)
  apply (simp add: semi_sol_corr_def)
  done
    
lemma corr_semi_sol_permx: "(eval_permx p_sub p \<noteq> NoPerm) = (semi_sol_permx (semi_sol_corr p_sub) p)" 
  apply (induct p)
      apply (auto)
       apply (simp add: corr_semi_sol_perm)
      apply (cut_tac p="x" in corr_semi_sol_perm)
      apply (auto)
     apply (case_tac "eval_permx p_sub p1")
       apply (auto)
     apply (case_tac "eval_permx p_sub p2")
       apply (auto)
    apply (case_tac "eval_permx p_sub p1")
      apply (auto)
    apply (case_tac "eval_permx p_sub p2")
      apply (auto)
   apply (case_tac "eval_permx p_sub p1")
     apply (auto)
  apply (case_tac "eval_permx p_sub p2")
    apply (auto)
  done
    
lemma corr_semi_sol_crn: "\<lbrakk> sol_sat_crn2 p_sub c \<rbrakk> \<Longrightarrow> semi_sol_crn2 (semi_sol_corr p_sub) c"  
  apply (case_tac c)
   apply (auto)
  apply (cut_tac p="x12" in corr_semi_sol_perm)
   apply (auto)
  apply (case_tac "eval_permx p_sub x11")
    apply (auto)
  apply (cut_tac p="x11" in corr_semi_sol_permx)
   apply (auto)
  done
    
    (* if the constraints can be solved, they can be semi-solved *)
lemma corr_semi_sol: "\<lbrakk> sol_sat2 p_sub c_list \<rbrakk> \<Longrightarrow> semi_sol_sat2 (semi_sol_corr p_sub) c_list"  
  apply (induct c_list)
   apply (auto)
  apply (rule_tac corr_semi_sol_crn)
   apply (auto)
  done
  
    (* - minimal semi-solution existence *)

definition semi_sol_bound :: "('a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bool" where
  "semi_sol_bound f_sub i = (\<exists> l. (\<forall> r. f_sub r \<longrightarrow> list_contain l r) \<and> length l = i)"
    
fun list_remove where
  "list_remove [] y = []"
| "list_remove (x # t) y = (if x = y then t else x # (list_remove t y))"
  
lemma remove_list_contain: "\<lbrakk> list_contain l x; x \<noteq> y \<rbrakk> \<Longrightarrow> list_contain (list_remove l y) x"  
  apply (induct l)
   apply (auto)
  done
    
lemma remove_less_length: "\<lbrakk> list_contain l x \<rbrakk> \<Longrightarrow> length (list_remove l x) < length l"    
  apply (induct l)
   apply (auto)
  done

lemma decr_semi_sol_bound: "\<lbrakk> semi_sol_bound f_sub i; leq_semi_env f_subx f_sub; f_subx \<noteq> f_sub \<rbrakk> \<Longrightarrow> (\<exists> j. semi_sol_bound f_subx j \<and> j < i)"  
  apply (simp add: semi_sol_bound_def)
  apply (auto)
    (* if f_subx \<le> f_sub and f_subx \<noteq> f_sub, then there must be some r \<in> f_sub, r \<notin> f_subx *)
  apply (case_tac "\<forall> r. f_sub r \<longrightarrow> f_subx r")
   apply (simp add: leq_semi_env_def)
   apply (auto)
    (* we can remove this from l to construct a smaller list *)
  apply (rule_tac x="length (list_remove l r)" in exI)
  apply (auto)
   apply (rule_tac x="list_remove l r" in exI)
   apply (auto)
   apply (rule_tac remove_list_contain)
    apply (auto)
   apply (simp add: leq_semi_env_def)
  apply (rule_tac remove_less_length)
  apply (auto)
  done
 
fun all_var_perm where
  "all_var_perm (SPerm p) = []"
| "all_var_perm (SVar r) = [r]"    
  
fun all_var_permx where
  "all_var_permx (XPerm p) = all_var_perm p"
| "all_var_permx (XType a) = []"
| "all_var_permx (XComp px qx) = all_var_permx px @ all_var_permx qx"  
| "all_var_permx (XLift px q) = all_var_permx px @ all_var_perm q"  
| "all_var_permx (XIfZero px qx) = all_var_permx px @ all_var_permx qx"  
  
fun all_var_crn where
  "all_var_crn (LeqCrn2 px q) = all_var_permx px @ all_var_perm q"
| "all_var_crn (DisjCrn2 px qx) = all_var_permx px @ all_var_permx qx"
| "all_var_crn (MiniDisjCrn2 px qx) = all_var_permx px @ all_var_permx qx"      
  
fun all_var_list where
  "all_var_list [] = []"
| "all_var_list (c # c_t) = all_var_crn c @ all_var_list c_t"
    
definition restr_semi_sol where  
  "restr_semi_sol f_sub l = (\<lambda> r. if list_contain l r then f_sub r else False)"

  
lemma restr_semi_sol_perm: "\<lbrakk> semi_sol_perm f_sub p; sub_list (all_var_perm p) r_list \<rbrakk> \<Longrightarrow>
  semi_sol_perm (restr_semi_sol f_sub r_list) p"  
  apply (case_tac p)
   apply (auto)
  apply (simp add: restr_semi_sol_def)
  apply (simp add: sub_list_def)
  done
  
lemma restr_semi_sol_perm_rev: "\<lbrakk> semi_sol_perm (restr_semi_sol f_sub r_list) p;
  sub_list (all_var_perm p) r_list \<rbrakk> \<Longrightarrow> semi_sol_perm f_sub p"      
  apply (case_tac p)
   apply (auto)
  apply (simp add: restr_semi_sol_def)
  apply (simp add: sub_list_def)
  done
    
lemma restr_semi_sol_permx: "\<lbrakk> semi_sol_permx f_sub px; sub_list (all_var_permx px) r_list \<rbrakk> \<Longrightarrow>
  semi_sol_permx (restr_semi_sol f_sub r_list) px"     
  apply (induct px)
     apply (auto)
       apply (rule_tac restr_semi_sol_perm)
        apply (auto)
      apply (cut_tac ?l1.0="all_var_permx px1" and lx="r_list" in append_sub_list1)
       apply (auto)
     apply (cut_tac ?l2.0="all_var_permx px2" and lx="r_list" in append_sub_list2)
      apply (auto)
    apply (cut_tac ?l1.0="all_var_permx px" and lx="r_list" in append_sub_list1)
     apply (auto)
   apply (cut_tac ?l1.0="all_var_permx px1" and lx="r_list" in append_sub_list1)
    apply (auto)
  apply (cut_tac ?l2.0="all_var_permx px2" and lx="r_list" in append_sub_list2)
   apply (auto)
  done

lemma restr_semi_sol_permx_rev: "\<lbrakk> semi_sol_permx (restr_semi_sol f_sub r_list) px;
  sub_list (all_var_permx px) r_list \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub px"     
  apply (induct px)
     apply (auto)
       apply (rule_tac restr_semi_sol_perm_rev)
        apply (auto)
      apply (cut_tac ?l1.0="all_var_permx px1" and lx="r_list" in append_sub_list1)
       apply (auto)
     apply (cut_tac ?l2.0="all_var_permx px2" and lx="r_list" in append_sub_list2)
      apply (auto)
    apply (cut_tac ?l1.0="all_var_permx px" and lx="r_list" in append_sub_list1)
     apply (auto)
   apply (cut_tac ?l1.0="all_var_permx px1" and lx="r_list" in append_sub_list1)
    apply (auto)
  apply (cut_tac ?l2.0="all_var_permx px2" and lx="r_list" in append_sub_list2)
   apply (auto)
  done
    
lemma restr_semi_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub c; sub_list (all_var_crn c) r_list \<rbrakk> \<Longrightarrow>
  semi_sol_crn2 (restr_semi_sol f_sub r_list) c"  
  apply (case_tac c)
   apply (auto)
   apply (cut_tac f_sub="f_sub" and px="x11" in restr_semi_sol_permx_rev)
     apply (auto)
   apply (rule_tac append_sub_list1)
   apply (auto)
  apply (cut_tac f_sub="f_sub" and p="x12" in restr_semi_sol_perm)
    apply (auto)
  apply (rule_tac append_sub_list2)
  apply (auto)
  done
    
lemma restr_semi_sol_sat_ih: "\<lbrakk> semi_sol_sat2 f_sub c_list; sub_list (all_var_list c_list) r_list \<rbrakk> \<Longrightarrow>
  semi_sol_sat2 (restr_semi_sol f_sub r_list) c_list"  
  apply (induct c_list)
   apply (auto)
   apply (rule_tac restr_semi_sol_crn)
    apply (simp)
   apply (rule_tac append_sub_list1)
   apply (auto)
  apply (cut_tac ?l2.0="all_var_list c_list" and lx="r_list" in append_sub_list2)
   apply (auto)
  done
    
lemma restr_semi_sol_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list\<rbrakk> \<Longrightarrow>
  semi_sol_sat2 (restr_semi_sol f_sub (all_var_list c_list)) c_list"    
  apply (rule_tac restr_semi_sol_sat_ih)
    apply (auto)
  apply (rule_tac id_sub_list)
  done
    
lemma finite_semi_sol_exists: "\<lbrakk> semi_sol_sat2 f_sub c_list \<rbrakk> \<Longrightarrow> (\<exists> f_sub' i. semi_sol_sat2 f_sub' c_list \<and> semi_sol_bound f_sub' i)" 
  apply (rule_tac x="restr_semi_sol f_sub (all_var_list c_list)" in exI)
  apply (rule_tac x="length (all_var_list c_list)" in exI)
  apply (auto)
   apply (rule_tac restr_semi_sol_sat)
   apply (simp)
  apply (simp add: semi_sol_bound_def)
  apply (rule_tac x="all_var_list c_list" in exI)
  apply (auto)
  apply (simp add: restr_semi_sol_def)
  apply (case_tac "list_contain (all_var_list c_list) r")
   apply (auto)
  done
    
lemma lmsse_ih: "\<lbrakk> semi_sol_sat2 f_sub c_list; semi_sol_bound f_sub i \<rbrakk> \<Longrightarrow> (\<exists> f_sub' j. semi_sol_sat2 f_sub' c_list \<and>
  semi_sol_bound f_sub' j \<and> (\<forall> f_subx. (semi_sol_sat2 f_subx c_list \<and> f_subx \<noteq> f_sub') \<longrightarrow> \<not> leq_semi_env f_subx f_sub'))"
  apply (induct i arbitrary: f_sub rule: less_induct)
    (* say that f_sub has no lesser semi-solution. then f_sub itself can be used *)
  apply (case_tac "\<forall> f_subx. (semi_sol_sat2 f_subx c_list \<and> f_subx \<noteq> f_sub) \<longrightarrow> \<not> leq_semi_env f_subx f_sub")
   apply (rule_tac x="f_sub" in exI)
   apply (auto)
    (* otherwise, there exists some lesser f_subx semi-solution. in this case, the bound must be less *)
  apply (cut_tac f_sub="f_sub" and i="x" and f_subx="f_subx" in decr_semi_sol_bound)
     apply (auto)
  done    
    
lemma local_min_semi_sol_exists: "\<lbrakk> semi_sol_sat2 f_sub c_list \<rbrakk> \<Longrightarrow> (\<exists> f_sub' i.  semi_sol_sat2 f_sub' c_list \<and>
  (\<forall> f_subx. (semi_sol_sat2 f_subx c_list \<and> f_subx \<noteq> f_sub') \<longrightarrow> \<not> leq_semi_env f_subx f_sub'))"
    (* from f_sub, we derive finite semi-solution f_sub' *)
  apply (cut_tac c_list="c_list" in finite_semi_sol_exists)
   apply (auto)
    (* from the induction, we know that f_sub' can obtain a local minima f_sub'a *)
  apply (cut_tac f_sub="f_sub'" and i="i" and c_list="c_list" in lmsse_ih)
    apply (auto)
  done
    
definition inter_semi_sol where
  "inter_semi_sol f_sub f_sub' = (\<lambda> r. f_sub r \<and> f_sub' r)"

lemma inter_semi_sol_perm1: "\<lbrakk> semi_sol_perm (inter_semi_sol f_sub f_subx) p \<rbrakk> \<Longrightarrow> semi_sol_perm f_sub p"
  apply (case_tac p)
   apply (auto)
  apply (simp add: inter_semi_sol_def)
  done
    
lemma inter_semi_sol_perm2: "\<lbrakk> semi_sol_perm (inter_semi_sol f_sub f_subx) p \<rbrakk> \<Longrightarrow> semi_sol_perm f_subx p"
  apply (case_tac p)
   apply (auto)
  apply (simp add: inter_semi_sol_def)
  done

lemma inter_semi_sol_permx1: "\<lbrakk> semi_sol_permx (inter_semi_sol f_sub f_subx) p \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub p"
  apply (induct p)
      apply (auto)
  apply (rule_tac inter_semi_sol_perm1)
  apply (simp)
  done
    
lemma inter_semi_sol_permx2: "\<lbrakk> semi_sol_permx (inter_semi_sol f_sub f_subx) p \<rbrakk> \<Longrightarrow> semi_sol_permx f_subx p"
  apply (induct p)
     apply (auto)
  apply (rule_tac inter_semi_sol_perm2)
  apply (simp)
  done
    
lemma inter_semi_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub c; semi_sol_crn2 f_subx c \<rbrakk> \<Longrightarrow> semi_sol_crn2 (inter_semi_sol f_sub f_subx) c"    
  apply (case_tac c)
   apply (auto)
     apply (cut_tac inter_semi_sol_permx1)
      apply (auto)
    apply (cut_tac inter_semi_sol_permx1)
     apply (auto)
   apply (cut_tac inter_semi_sol_permx2)
    apply (auto)
  apply (case_tac x12)
   apply (auto)
  apply (simp add: inter_semi_sol_def)
  done
    
lemma inter_semi_sol_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list; semi_sol_sat2 f_subx c_list \<rbrakk> \<Longrightarrow> semi_sol_sat2 (inter_semi_sol f_sub f_subx) c_list"  
  apply (induct c_list)
   apply (auto)
  apply (rule_tac inter_semi_sol_crn)
   apply (auto)
  done
    
lemma eq_leq_semi_env: "\<lbrakk> \<forall> x. inter_semi_sol f_sub f_subx x = f_sub x \<rbrakk> \<Longrightarrow> leq_semi_env f_sub f_subx"    
  apply (simp add: leq_semi_env_def)
  apply (auto)
  apply (simp add: inter_semi_sol_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma inter_leq_semi_env1: "\<lbrakk> leq_semi_env f_sub f_subx \<rbrakk> \<Longrightarrow> leq_semi_env (inter_semi_sol f_sub f_sub') f_subx"    
  apply (simp add: leq_semi_env_def)
  apply (simp add: inter_semi_sol_def)
  done

lemma inter_leq_semi_env2: "\<lbrakk> leq_semi_env f_sub' f_subx \<rbrakk> \<Longrightarrow> leq_semi_env (inter_semi_sol f_sub f_sub') f_subx"    
  apply (simp add: leq_semi_env_def)
  apply (simp add: inter_semi_sol_def)
  done    
  
lemma min_semi_sol_exists: "\<lbrakk> semi_sol_sat2 f_sub c_list \<rbrakk> \<Longrightarrow> (\<exists> m_sub. min_semi_sol m_sub c_list)"
    (* if we have a semi-solution, we should be able to find a semi-solution that has no solution lesser than it. *)
  apply (cut_tac f_sub="f_sub" and c_list="c_list" in local_min_semi_sol_exists)
   apply (auto)
    (* if every semi-solution is lesser, then it counts as a min *)
  apply (case_tac "\<forall> f_subx. \<not> semi_sol_sat2 f_subx c_list \<or> leq_semi_env f_sub' f_subx")
   apply (rule_tac x="f_sub'" in exI)
   apply (simp add: min_semi_sol_def)
  apply (auto)
    (* otherwise we have two "sibling" semi-solutions. we argue combining them creates a new semi-solution. *)
  apply (erule_tac x="inter_semi_sol f_sub' f_subx" in allE)
  apply (auto)
    apply (rule_tac inter_semi_sol_sat)
     apply (auto)
    (* the combination cannot be equal to f_sub', since then f_sub' \<le> f_subx *)
   apply (cut_tac f_sub="f_sub'" and f_subx="f_subx" in  eq_leq_semi_env)
    apply (auto)
    (* however this is a lesser solution, which is a contradiction *)
  apply (cut_tac f_sub="f_sub'" and f_subx="f_sub'" in inter_leq_semi_env1)
   apply (auto)
  apply (simp add: leq_semi_env_def)
  done
    
    (* min semi-sol algorithm *)
    
fun non_zero_perm where
  "non_zero_perm (SVar r) = False"
| "non_zero_perm (SPerm p) = (p \<noteq> NoPerm)"  
  
fun non_zero_permx where
  "non_zero_permx (XPerm p) = non_zero_perm p"
| "non_zero_permx (XType a) = False"
| "non_zero_permx (XComp p q) = ((non_zero_permx p) \<or> (non_zero_permx q))"
| "non_zero_permx (XLift p q) = (non_zero_permx p)"
| "non_zero_permx (XIfZero px q) = ((non_zero_permx px) \<and> (non_zero_permx q))"    
    
fun concrete_crn where
  "concrete_crn (LeqCrn2 px q) = non_zero_permx px"
| "concrete_crn (DisjCrn2 px qx) = False"
| "concrete_crn (MiniDisjCrn2 px qx) = False"  
  
fun conc_crn_total :: "perm_crn2 list \<Rightarrow> nat" where
  "conc_crn_total [] = 0"
| "conc_crn_total (c # c_t) = (conc_crn_total c_t + (if concrete_crn c then 1 else 0))"      

fun select_list where
  "select_list f [] = None"  
| "select_list f (c # c_t) = (if f c then Some (c, c_t) else (case select_list f c_t of
    None \<Rightarrow> None
    | Some (cx, c_tx) \<Rightarrow> Some (cx, c # c_tx)
  ))"   
  
lemma select_less_length: "\<lbrakk> select_list f c_l = Some (c, c_t) \<rbrakk> \<Longrightarrow> length c_t < length c_l"  
  apply (induct c_l arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_l")
   apply (auto)
  done
  
fun sub1_perm where
  "sub1_perm (SPerm p) r = SPerm p"
| "sub1_perm (SVar r') r = (if r' = r then SPerm OwnPerm else SVar r')"    
 
fun sub1_permx where
  "sub1_permx (XPerm p) r = XPerm (sub1_perm p r)"
| "sub1_permx (XType a) r = XType a"
| "sub1_permx (XComp px qx) r = XComp (sub1_permx px r) (sub1_permx qx r)"  
| "sub1_permx (XLift px q) r = XLift (sub1_permx px r) (sub1_perm q r)"  
| "sub1_permx (XIfZero px qx) r = XIfZero (sub1_permx px r) (sub1_permx qx r)"  
  
fun sub1_crn where
  "sub1_crn (LeqCrn2 px q) r = LeqCrn2 (sub1_permx px r) (sub1_perm q r)"
| "sub1_crn (DisjCrn2 px qx) r = DisjCrn2 (sub1_permx px r) (sub1_permx qx r)"
| "sub1_crn (MiniDisjCrn2 px qx) r = MiniDisjCrn2 (sub1_permx px r) (sub1_permx qx r)"    
  
fun sub1_crn_list where
  "sub1_crn_list [] r = []"
| "sub1_crn_list (c # c_t) r = sub1_crn c r # sub1_crn_list c_t r"    
  
lemma sub1_same_length: "length c_list = length (sub1_crn_list c_list r)"  
  apply (induct c_list)
   apply (auto)
  done
  
    (* takes a constraint list and returns the "minimum" semi-solution *)
    
function min_semi_sol_calc_f where
  "min_semi_sol_calc_f c_list = (case select_list concrete_crn c_list of
    None \<Rightarrow> Some empty_semi_env
    | Some (c, c_t) \<Rightarrow> (case c of
      LeqCrn2 px q \<Rightarrow> (case q of
        SPerm p \<Rightarrow> if p = NoPerm then None else min_semi_sol_calc_f c_t
        | SVar r \<Rightarrow> (case min_semi_sol_calc_f (sub1_crn_list c_t r) of
          None \<Rightarrow> None
          | Some f_sub \<Rightarrow> Some (\<lambda> r'. if r' = r then True else f_sub r')
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
    
definition min_semi_sol_calc where
  "min_semi_sol_calc c_list = min_semi_sol_calc_f c_list"  


lemma select_cond_sat: "\<lbrakk> select_list f c_list = Some (c, c_t) \<rbrakk> \<Longrightarrow> f c"  
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done
  
lemma select_semi_sol_crn: "\<lbrakk> semi_sol_sat2 f_sub c_list; select_list f c_list = Some (c, c_t) \<rbrakk> \<Longrightarrow> semi_sol_crn2 f_sub c"  
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done

lemma select_semi_sol: "\<lbrakk> semi_sol_sat2 f_sub c_list; select_list f c_list = Some (c, c_t) \<rbrakk> \<Longrightarrow> semi_sol_sat2 f_sub c_t"      
  apply (induct c_list arbitrary: c_t)
   apply (auto)
  apply (case_tac "f a")
   apply (auto)
  apply (case_tac "select_list f c_list")
   apply (auto)
  done
    
lemma nz_semi_sol_perm: "\<lbrakk> non_zero_perm p \<rbrakk> \<Longrightarrow> semi_sol_perm f_sub p"    
  apply (case_tac p)
   apply (auto)
  done
    
lemma nz_semi_sol_permx: "\<lbrakk> non_zero_permx p \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub p"    
  apply (induct p)
     apply (auto)
  apply (rule_tac nz_semi_sol_perm)
  apply (simp)
  done
   
lemma zero_semi_sol_perm: "\<lbrakk> \<not> non_zero_perm p \<rbrakk> \<Longrightarrow> \<not> semi_sol_perm empty_semi_env p"
  apply (simp add: empty_semi_env_def)
  apply (case_tac p)
   apply (auto)
  done
    
lemma zero_semi_sol_permx: "\<lbrakk> \<not> non_zero_permx p \<rbrakk> \<Longrightarrow> \<not> semi_sol_permx empty_semi_env p"    
  apply (induct p)
      apply (auto)
  apply (simp add: zero_semi_sol_perm)
  done    
    
lemma sub1_semi_sol_perm: "\<lbrakk> f_sub x \<rbrakk> \<Longrightarrow> semi_sol_perm f_sub p = semi_sol_perm f_sub (sub1_perm p x)"    
  apply (case_tac p)
   apply (auto)
  done
    
lemma sub1_semi_sol_permx: "\<lbrakk> f_sub x \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub px = semi_sol_permx f_sub (sub1_permx px x)"   
  apply (induct px)
      apply (auto)
   apply (cut_tac f_sub="f_sub" and p="xa" in sub1_semi_sol_perm)
    apply (auto)
  apply (cut_tac f_sub="f_sub" and p="xa" in sub1_semi_sol_perm)
   apply (auto)
  done
    
lemma sub1_semi_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub c; f_sub x \<rbrakk> \<Longrightarrow> semi_sol_crn2 f_sub (sub1_crn c x)"    
  apply (case_tac c)
   apply (auto)
   apply (cut_tac f_sub="f_sub" and px="x11" in sub1_semi_sol_permx)
    apply (auto)
  apply (cut_tac f_sub="f_sub" and p="x12" in sub1_semi_sol_perm)
   apply (auto)
  done
    
lemma sub1_semi_sol_sat: "\<lbrakk> semi_sol_sat2 f_sub c_list; f_sub x \<rbrakk> \<Longrightarrow> semi_sol_sat2 f_sub (sub1_crn_list c_list x)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac sub1_semi_sol_crn)
   apply (auto)
  done
  

lemma msscu_ih: "\<lbrakk> \<And>c_lista. \<lbrakk>length c_lista < length c_list; min_semi_sol_calc c_lista = None\<rbrakk> \<Longrightarrow> \<not> semi_sol_sat2 f_sub c_lista; 
  length c_lista < length c_list; min_semi_sol_calc c_lista = None \<rbrakk> \<Longrightarrow> \<not> semi_sol_sat2 f_sub c_lista"    
  apply (auto)
  done

    (* we want to prove two things. first - if mini semi-solution returns a semi-solution, it is actually the minimal semi-solution.
      second - if mini semi-solution does not return a semi-solution, there is no solution. *)    
    
lemma min_semi_sol_calc_unsat: "\<lbrakk> min_semi_sol_calc c_list = None \<rbrakk> \<Longrightarrow>  \<not> semi_sol_sat2 f_sub c_list"    
  apply (induct "length c_list" arbitrary: c_list rule: less_induct)
  apply (auto)
    (* unroll algorithm definition *)
  apply (case_tac "\<not> (case select_list concrete_crn c_list of None \<Rightarrow> Some empty_semi_env
         | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = NoPerm then None else min_semi_sol_calc_f c_t
         | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
             (case min_semi_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some f_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then True else f_sub r'))
         | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x) =
        None")
   apply (simp add: min_semi_sol_calc_def)
  apply (auto)
    (* attempt to select from list *)
  apply (case_tac "select_list concrete_crn c_list")
   apply (auto)
  apply (case_tac a)
    apply (auto)
    apply (case_tac x12)
     apply (auto)
    (* inequality over permission constant. case where p = 0 *)
    apply (case_tac "x1 = NoPerm")
      apply (auto)
      apply (cut_tac f_sub="f_sub" and c="LeqCrn2 x11 (SPerm NoPerm)" in select_semi_sol_crn)
        apply (auto)
      apply (cut_tac f="concrete_crn" and c="LeqCrn2 x11 (SPerm NoPerm)" in select_cond_sat)
       apply (auto)
      apply (cut_tac f_sub="f_sub" and p="x11" in nz_semi_sol_permx)
       apply (auto)
    (* - inductive case where p \<noteq> 0 *)
     apply (cut_tac c_lista="b" and c_list="c_list" in msscu_ih)
        apply (auto)
       apply (rule_tac select_less_length)
       apply (simp)
      apply (simp add: min_semi_sol_calc_def)
     apply (cut_tac c_list="c_list" and c_t="b" in select_semi_sol)
       apply (auto)
    (* inequality over permission var *)
    apply (cut_tac c_lista="sub1_crn_list b x2" and c_list="c_list" in msscu_ih)
       apply (auto)
      apply (rule_tac t="length (sub1_crn_list b x2)" and s="length b" in subst)
       apply (rule_tac sub1_same_length)
      apply (rule_tac select_less_length)
      apply (simp)
     apply (case_tac "case select_list concrete_crn (sub1_crn_list b x2) of None \<Rightarrow> Some empty_semi_env
              | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = NoPerm then None else min_semi_sol_calc_f c_t
              | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
                  (case min_semi_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some f_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then True else f_sub r'))
              | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x")
      apply (auto)
     apply (simp add: min_semi_sol_calc_def)
    (* if the constraints are solvable, then the solution assigns either 1 or 0 to r. we know an assignment of 0 will fail. an assignment of 1
        means sub1_crn_list should be solvable, a contradiction *)
    apply (case_tac "f_sub x2")
     apply (cut_tac c_list="b" and f_sub="f_sub" and x="x2" in sub1_semi_sol_sat)
       apply (rule_tac select_semi_sol)
        apply (auto)
    apply (cut_tac f_sub="f_sub" and c="LeqCrn2 x11 (SVar x2)" in select_semi_sol_crn)
      apply (auto)
    apply (cut_tac f="concrete_crn" and c="LeqCrn2 x11 (SVar x2)" in select_cond_sat)
     apply (auto)
    apply (cut_tac f_sub="f_sub" and p="x11" in nz_semi_sol_permx)
     apply (auto)
    (* disjointness cases, should never happen *)
   apply (cut_tac f="concrete_crn" and c="DisjCrn2 x21 x22" in select_cond_sat)
    apply (auto)
  apply (cut_tac f="concrete_crn" and c="MiniDisjCrn2 x31 x32" in select_cond_sat)
   apply (auto)
  done
    
lemma step2_solve_end: "\<lbrakk> select_list concrete_crn c_list = None \<rbrakk> \<Longrightarrow> semi_sol_sat2 empty_semi_env c_list"    
  apply (induct c_list)
   apply (auto)
    (* prove constraint is valid *)
   apply (case_tac "concrete_crn a")
    apply (auto)
   apply (case_tac a)
     apply (auto)
   apply (cut_tac p="x11" in zero_semi_sol_permx)
    apply (auto)
    (* induction *)
  apply (case_tac "concrete_crn a")
   apply (auto)
  apply (case_tac "select_list concrete_crn c_list")
   apply (auto)
  done

lemma select_semi_sol_split: "\<lbrakk> select_list f c_list = Some (c, c_t); semi_sol_crn2 f_sub c;
  semi_sol_sat2 f_sub c_t \<rbrakk> \<Longrightarrow> semi_sol_sat2 f_sub c_list"    
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

lemma step2_solve_iter_c1: "\<lbrakk> select_list concrete_crn c_list = Some (LeqCrn2 px (SPerm p), c_t); p \<noteq> NoPerm;
  min_semi_sol f_sub c_t \<rbrakk> \<Longrightarrow> min_semi_sol f_sub c_list"    
  apply (simp add: min_semi_sol_def)
  apply (auto)
   apply (rule_tac c="LeqCrn2 px (SPerm p)" in select_semi_sol_split)
     apply (auto)
    (* the main thing is to prove that f_sub is still minimal. say that there is some lesser f_sub'. then it must solve c_list' *)
  apply (cut_tac f_sub="f_sub'" and c_list="c_list" and c_t="c_t" in select_semi_sol)
    apply (auto)
  done

lemma add_semi_sol_perm: "\<lbrakk> semi_sol_perm f_sub (sub1_perm p r) \<rbrakk> \<Longrightarrow> semi_sol_perm (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') p"       
  apply (case_tac p)
   apply (auto)
  done
    
lemma add_semi_sol_permx_rev: "\<lbrakk> semi_sol_permx (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') px \<rbrakk> \<Longrightarrow> semi_sol_permx f_sub (sub1_permx px r)"       
  apply (induct px)
      apply (auto)
  apply (case_tac x)
   apply (auto)
  done
  
lemma add_semi_sol_crn: "\<lbrakk> semi_sol_crn2 f_sub (sub1_crn c r) \<rbrakk> \<Longrightarrow> semi_sol_crn2 (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') c"   
  apply (case_tac c)
    apply (auto)
   apply (cut_tac px="x11" and r="r" and f_sub="f_sub" in add_semi_sol_permx_rev)
    apply (auto)
  apply (rule_tac add_semi_sol_perm)
  apply (auto)
  done
  
lemma add_semi_sol: "\<lbrakk> semi_sol_sat2 f_sub (sub1_crn_list c_list r) \<rbrakk> \<Longrightarrow> semi_sol_sat2 (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') c_list"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac add_semi_sol_crn)
  apply (auto)
  done
  
lemma add_leq_semi_env: "\<lbrakk> leq_semi_env f_sub f_subx; f_subx r \<rbrakk> \<Longrightarrow> leq_semi_env (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') f_subx"    
  apply (simp add: leq_semi_env_def)
  apply (auto)
  done
  
lemma step2_solve_iter_c2: "\<lbrakk> select_list concrete_crn c_list = Some (LeqCrn2 px (SVar r), c_t);
  min_semi_sol f_sub (sub1_crn_list c_t r) \<rbrakk> \<Longrightarrow> min_semi_sol (\<lambda>r'. r' \<noteq> r \<longrightarrow> f_sub r') c_list"    
  apply (simp add: min_semi_sol_def)
  apply (auto)
    (* first we must prove that the new substitution solves *)
   apply (rule_tac c="LeqCrn2 px (SVar r)" in select_semi_sol_split)
     apply (auto)
   apply (rule_tac add_semi_sol)
   apply (auto)
    (* next we must prove that it is minimal. say that there is some lesser f_sub'. first we must have f_sub' r *)
  apply (case_tac "\<not> f_sub' r")
   apply (cut_tac f_sub="f_sub'" and c="LeqCrn2 px (SVar r)" in select_semi_sol_crn)
     apply (auto)
   apply (cut_tac c="LeqCrn2 px (SVar r)" and f="concrete_crn" in select_cond_sat)
    apply (auto)
   apply (cut_tac f_sub="f_sub'" and p="px" in nz_semi_sol_permx)
    apply (auto)
    (* we also know f_sub' must solve c_t. with these two facts combined, we have f_sub' solves c_t with r = 1  *)
  apply (cut_tac f_sub="f_sub'" and c_list="c_list" and c_t="c_t" in select_semi_sol)
    apply (auto)
  apply (cut_tac f_sub="f_sub'" and c_list="c_t" and x="r" in sub1_semi_sol_sat)
    apply (auto)
    (* this gives f_sub \<le> f_sub', which combined with f_sub' r gives us what we want *)
  apply (erule_tac x="f_sub'" in allE)
  apply (auto)
  apply (rule_tac add_leq_semi_env)
   apply (auto)
  done

lemma empty_leq_semi_env: "leq_semi_env empty_semi_env f_sub"    
  apply (simp add: leq_semi_env_def)
  apply (simp add: empty_semi_env_def)
  done
    
lemma min_semi_sol_calc_sat: "\<lbrakk> min_semi_sol_calc c_list = Some f_sub \<rbrakk> \<Longrightarrow> min_semi_sol f_sub c_list"    
  apply (induct "length c_list" arbitrary: c_list f_sub rule: less_induct)
    apply (case_tac "\<not> (case select_list concrete_crn c_list of None \<Rightarrow> Some empty_semi_env
         | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = NoPerm then None else min_semi_sol_calc_f c_t
         | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
             (case min_semi_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some f_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then True else f_sub r'))
         | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x) =
        Some f_sub")
   apply (simp add: min_semi_sol_calc_def)
  apply (auto)
  apply (case_tac "select_list concrete_crn c_list")
   apply (auto)
    (* base case *)
    apply (simp add: min_semi_sol_def)
   apply (auto)
    apply (rule_tac step2_solve_end)
    apply (auto)
   apply (rule_tac empty_leq_semi_env)
    (* case analysis over constraint *)
  apply (case_tac a)
    apply (auto)
  apply (case_tac x12)
   apply (auto)
    (* - inequality constraint. permission case *)
   apply (case_tac "x1 = NoPerm")
    apply (auto)
   apply (rule_tac px="x11" and p="x1" and c_t="b" in step2_solve_iter_c1)
     apply (auto)
   apply (cut_tac c_t="b" and c_l="c_list" in select_less_length)
    apply (auto)
   apply (case_tac "min_semi_sol_calc b = Some f_sub")
    apply (iprover)
   apply (simp add: min_semi_sol_calc_def)
    (* - inequality constraint. var case *)
  apply (case_tac "case select_list concrete_crn (sub1_crn_list b x2) of None \<Rightarrow> Some empty_semi_env
              | Some (LeqCrn2 px (SPerm p), c_t) \<Rightarrow> if p = NoPerm then None else min_semi_sol_calc_f c_t
              | Some (LeqCrn2 px (SVar r), c_t) \<Rightarrow>
                  (case min_semi_sol_calc_f (sub1_crn_list c_t r) of None \<Rightarrow> None | Some f_sub \<Rightarrow> Some (\<lambda>r'. if r' = r then True else f_sub r'))
              | Some (DisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x | Some (MiniDisjCrn2 x_perm1 x, c_t) \<Rightarrow> Map.empty x")
   apply (auto)
  apply (rule_tac px="x11" and c_t="b" in step2_solve_iter_c2)
  apply (auto)
  apply (case_tac "\<not> length (sub1_crn_list b x2) < length c_list")
   apply (cut_tac c_list="b" and r="x2" in sub1_same_length)
   apply (auto)
   apply (cut_tac c_t="b" and c_l="c_list" in select_less_length)
    apply (auto)
  apply (case_tac "min_semi_sol_calc (sub1_crn_list b x2) = Some a")
   apply (iprover)
  apply (simp add: min_semi_sol_calc_def)
  done 
  
end