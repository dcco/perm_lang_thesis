theory SolverP1
  imports InferRange
begin
  
  (* ## to move *)

definition sub_list where
  "sub_list l1 l2 = (\<forall> x. list_contain l1 x \<longrightarrow> list_contain l2 x)"  
  
lemma append_sub_list1: "\<lbrakk> sub_list (l1 @ l2) lx \<rbrakk> \<Longrightarrow> sub_list l1 lx"  
  apply (induct l1)
   apply (auto)
   apply (simp add: sub_list_def)
  apply (simp add: sub_list_def)
  done

lemma append_sub_list2: "\<lbrakk> sub_list (l1 @ l2) lx \<rbrakk> \<Longrightarrow> sub_list l2 lx"  
  apply (induct l1)
   apply (auto)
  apply (simp add: sub_list_def)
  done
    
lemma id_sub_list: "sub_list l l"    
  apply (simp add: sub_list_def)
  done    
  
    (* phase 1: type unification *)  
  
datatype perm_crn2 =
  LeqCrn2 x_perm s_perm
  | DisjCrn2 x_perm x_perm
  | MiniDisjCrn2 x_perm x_perm
  
fun unify_subset where
  "unify_subset [] = []"
| "unify_subset (c # c_t) = (case c of
    UnifyCrn tau1 tau2 \<Rightarrow> (tau1, tau2) # (unify_subset c_t)
    | cx \<Rightarrow> unify_subset c_t
  )"
  
fun eval_perm where
  "eval_perm p_sub (SPerm p) = p"
| "eval_perm p_sub (SVar r) = p_sub r"  
  
fun eval_permx where
  "eval_permx p_sub (XPerm p) = eval_perm p_sub p"  
| "eval_permx p_sub (XType a) = NoPerm"
| "eval_permx p_sub (XComp px qx) = union_perm (eval_permx p_sub px) (eval_permx p_sub qx)"  
| "eval_permx p_sub (XLift px q) = (if eval_perm p_sub q = OwnPerm \<and> eval_permx p_sub px \<noteq> NoPerm then OwnPerm else eval_permx p_sub px)"
| "eval_permx p_sub (XIfZero px qx) = (if eval_permx p_sub px = NoPerm then NoPerm else eval_permx p_sub qx)"  
  
fun sol_sat_crn2 where
  "sol_sat_crn2 p_sub (LeqCrn2 px q) = (leq_perm (eval_permx p_sub px) (eval_perm p_sub q))"  
| "sol_sat_crn2 p_sub (DisjCrn2 px qx) = (mini_disj_perm (eval_permx p_sub px) (eval_permx p_sub qx) \<and>
  mini_disj_perm (eval_permx p_sub qx) (eval_permx p_sub px))"  
| "sol_sat_crn2 p_sub (MiniDisjCrn2 px qx) = (mini_disj_perm (eval_permx p_sub px) (eval_permx p_sub qx))"  
  
fun sol_sat2 where
  "sol_sat2 p_sub [] = True"  
| "sol_sat2 p_sub (c # c_t) = (sol_sat_crn2 p_sub c \<and> sol_sat2 p_sub c_t)"     
    
  (* occurs *)
  
fun occurs where
  "occurs (VarScheme b) a = (a = b)"
| "occurs (ArrayScheme tau) a = (occurs tau a)"
| "occurs (PairScheme t1 t2 r) a = (occurs t1 a \<or> occurs t2 a)"  
| "occurs (FunScheme t1 t2 r af) a = (occurs t1 a \<or> occurs t2 a)"  
| "occurs (ChanScheme tau c_end) a = (occurs tau a)"
| "occurs tau a = False"
  
fun sol_subst_type :: "type_subst \<Rightarrow> s_type \<Rightarrow> s_type" where
  "sol_subst_type t_sub (VarScheme x) = (case t_sub x of
    None \<Rightarrow> VarScheme x
    | Some tau \<Rightarrow> tau
  )"
| "sol_subst_type t_sub (ArrayScheme tau) = ArrayScheme (sol_subst_type t_sub tau)"  
| "sol_subst_type t_sub (PairScheme t1 t2 p) = PairScheme (sol_subst_type t_sub t1) (sol_subst_type t_sub t2) p"
| "sol_subst_type t_sub (FunScheme t1 t2 p q) = FunScheme (sol_subst_type t_sub t1) (sol_subst_type t_sub t2) p q"  
| "sol_subst_type t_sub (ChanScheme tau c_end) = ChanScheme (sol_subst_type t_sub tau) c_end"
| "sol_subst_type t_sub tau_v = tau_v"
  
fun sol_subst_eq_list where
  "sol_subst_eq_list t_sub [] = []"  
| "sol_subst_eq_list t_sub ((t1, t2) # c_t) = ((sol_subst_type t_sub t1, sol_subst_type t_sub t2) # (sol_subst_eq_list t_sub c_t))"  
  
fun as_perm_s where
  "as_perm_s (AffConst a) = (SPerm (as_perm a))"
| "as_perm_s (AffVar r) = (SVar r)"  
 
definition add_list where
  "add_list l x = (if list_contain l x then l else x # l)"  

fun rem_list where
  "rem_list [] x = []"    
| "rem_list (y # l) x = (if x = y then l else y # (rem_list l x))"  
  
fun union_list where
  "union_list [] l2 = l2"
| "union_list (x # l1) l2 = add_list (union_list l1 l2) x"    
  
fun tvar_type_l where
  "tvar_type_l (VarScheme a) = [a]"
  | "tvar_type_l (ArrayScheme tau) = tvar_type_l tau"
  | "tvar_type_l (PairScheme t1 t2 p) = union_list (tvar_type_l t1) (tvar_type_l t2)"
  | "tvar_type_l (FunScheme t1 t2 p a) = union_list (tvar_type_l t1) (tvar_type_l t2)"
  | "tvar_type_l (ChanScheme tau c_end) = tvar_type_l tau"
  | "tvar_type_l tau = []"

fun tvar_eq_list where
  "tvar_eq_list [] = []"
| "tvar_eq_list ((t1, t2) # c_t) = union_list (union_list (tvar_type_l t1) (tvar_type_l t2)) (tvar_eq_list c_t)"
    
definition tvar_total where  
  "tvar_total c_list = length (tvar_eq_list c_list)"

fun type_cons :: "s_type \<Rightarrow> nat" where
  "type_cons (ArrayScheme tau) = type_cons tau + 1"
| "type_cons (PairScheme t1 t2 p) = (type_cons t1) + (type_cons t2) + 1"
| "type_cons (FunScheme t1 t2 p q) = (type_cons t1) + (type_cons t2) + 1"  
| "type_cons (ChanScheme tau c_end) = type_cons tau + 1"
| "type_cons (VarScheme a) = 0"
| "type_cons tau = 1"
  
fun lcons_list where
  "lcons_list [] = 0"
| "lcons_list ((t1, t2) # c_t) = (type_cons t1) + (lcons_list c_t)"
  
definition unify_rel where
  "unify_rel = measures [tvar_total, lcons_list, length]"  
  
lemma contain_rem_list_length: "\<lbrakk> list_contain l x \<rbrakk> \<Longrightarrow> length (rem_list l x) + 1 = length l"  
  apply (induct l)
   apply (auto)
  done
  
lemma rem_sub_list: "\<lbrakk> sub_list l1 l2; \<not> list_contain l1 x \<rbrakk> \<Longrightarrow> sub_list l1 (rem_list l2 x)"    
  apply (simp add: sub_list_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (induct l2)
   apply (auto)
  done
    
lemma add_sub_list: "\<lbrakk> sub_list l1 l2 \<rbrakk> \<Longrightarrow> sub_list l1 (add_list l2 x)"    
  apply (simp add: sub_list_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  apply (induct l2)
   apply (auto)
   apply (simp add: add_list_def)
  apply (simp add: add_list_def)
  done
  
lemma union_list_contain1: "\<lbrakk> list_contain l1 x \<rbrakk> \<Longrightarrow> list_contain (union_list l1 l2) x"    
  apply (induct l1 arbitrary: l2)
   apply (auto)
   apply (simp add: add_list_def)
  apply (simp add: add_list_def)
  done
    
lemma union_list_contain2: "\<lbrakk> list_contain l2 x \<rbrakk> \<Longrightarrow> list_contain (union_list l1 l2) x"    
  apply (induct l1 arbitrary: l2)
   apply (auto)
  apply (simp add: add_list_def)
  done    
  
lemma dist_union_list_contain: "\<lbrakk> list_contain (union_list l1 l2) x \<rbrakk> \<Longrightarrow> list_contain l1 x \<or> list_contain l2 x"    
  apply (induct l1 arbitrary: l2)
   apply (auto)
  apply (simp add: add_list_def)
  apply (case_tac "list_contain (union_list l1 l2) a")
   apply (auto)
  done        
    
lemma union_sub_list1: "\<lbrakk> sub_list la lb \<rbrakk> \<Longrightarrow> sub_list la (union_list lb lc)"
  apply (simp add: sub_list_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (rule_tac union_list_contain1)
  apply (simp)
  done
    
lemma union_sub_list2: "\<lbrakk> sub_list la lc \<rbrakk> \<Longrightarrow> sub_list la (union_list lb lc)"
  apply (simp add: sub_list_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (rule_tac union_list_contain2)
  apply (simp)
  done    
  
lemma dist_union_sub_list: "\<lbrakk> sub_list la lc; sub_list lb lc \<rbrakk> \<Longrightarrow> sub_list (union_list la lb) lc"    
  apply (simp add: sub_list_def)
  apply (auto)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (cut_tac ?l1.0="la" and ?l2.0="lb" and x="x" in dist_union_list_contain)
   apply (auto)
  done
    
lemma union_sub_list_rev: "\<lbrakk> sub_list (union_list la lb) lc \<rbrakk> \<Longrightarrow> sub_list la lc \<and> sub_list lb lc"      
  apply (simp add: sub_list_def)
  apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (cut_tac ?l1.0="la" in union_list_contain1)
    apply (auto)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (cut_tac ?l2.0="lb" in union_list_contain2)
   apply (auto)
  done
    
lemma sub_list_less_length: "\<lbrakk> fresh_in_list l1; sub_list l1 l2 \<rbrakk> \<Longrightarrow> length l1 \<le> length l2"  
  apply (induct l1 arbitrary: l2)
   apply (auto)
    (* because a # l1 is a sub_list of l2, l2 must contain a *)
  apply (case_tac "\<not> list_contain l2 a")
   apply (simp add: sub_list_def)
   apply (auto)
    (* we can replace length l2 with length (l2 - a) + 1 *)
  apply (rule_tac t="length l2" and s="length (rem_list l2 a) + 1" in subst)
   apply (rule_tac contain_rem_list_length)
   apply (auto)
    (* lastly, it remains to show that l1 is a sub-list of (l2 - a) *)
  apply (cut_tac ?l1.0="l1" and ?l2.0="l2" and x="a" in rem_sub_list)
    apply (simp add: sub_list_def)
   apply (auto)
  done
 
lemma union_fresh_list: "\<lbrakk> fresh_in_list l1; fresh_in_list l2 \<rbrakk> \<Longrightarrow> fresh_in_list (union_list l1 l2)"    
  apply (induct l1)
   apply (auto)
  apply (simp add: add_list_def)
  done

lemma tvar_type_fresh_list: "fresh_in_list (tvar_type_l tau)"    
  apply (induct tau)
         apply (auto)
   apply (rule_tac union_fresh_list)
    apply (auto)
  apply (rule_tac union_fresh_list)
   apply (auto)
  done

lemma tvar_eq_fresh_list: "fresh_in_list (tvar_eq_list c_list)"    
  apply (induct c_list)
   apply (auto)
  apply (rule_tac union_fresh_list)
  apply (rule_tac union_fresh_list)
    apply (rule_tac tvar_type_fresh_list)
   apply (rule_tac tvar_type_fresh_list)
  apply (simp)
  done
    
lemma cons_less_tvar_total: "tvar_total c_list \<le> tvar_total (c # c_list)"  
  apply (simp add: tvar_total_def)
  apply (case_tac c)
  apply (auto)
  apply (rule_tac sub_list_less_length)
   apply (rule_tac tvar_eq_fresh_list)
  apply (rule_tac union_sub_list2)
  apply (rule_tac id_sub_list)
  done

lemma orient_less_tvar_total: "tvar_total ((c2, c1) # c_list) \<le> tvar_total ((c1, c2) # c_list)"      
  apply (simp add: tvar_total_def)
  apply (rule_tac sub_list_less_length)
   apply (rule_tac union_fresh_list)
    apply (rule_tac union_fresh_list)
     apply (rule_tac tvar_type_fresh_list)
    apply (rule_tac tvar_type_fresh_list)
   apply (rule_tac tvar_eq_fresh_list)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac union_sub_list2)
    apply (rule_tac id_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac id_sub_list)
  apply (rule_tac union_sub_list2)
  apply (rule_tac id_sub_list)
  done
    
lemma simp_unify_rel: "(c_list, (x, y) # c_list) \<in> unify_rel"
  apply (simp add: unify_rel_def)
  apply (auto)
  apply (cut_tac c_list="c_list" and c="(x, y)" in cons_less_tvar_total)
  apply (auto)
  done
    
lemma orient_unify_rel: "\<lbrakk> \<forall> b. x \<noteq> VarScheme b \<rbrakk> \<Longrightarrow> ((VarScheme a, x) # c_list, (x, VarScheme a) # c_list) \<in> unify_rel"    
  apply (simp add: unify_rel_def)
  apply (auto)
   apply (cut_tac ?c2.0="VarScheme a" and ?c1.0="x" and c_list="c_list" in orient_less_tvar_total)
   apply (auto)
  apply (case_tac x)
         apply (auto)
  done

lemma sol_subst_type_sub_list: "\<lbrakk> sub_list (tvar_type_l tau) l; sub_list (tvar_type_l tau_x) l \<rbrakk> \<Longrightarrow>
  sub_list (tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau)) l"    
  apply (induct tau)
         apply (auto)
    apply (case_tac "x = xa")
     apply (simp add: add_env_def)
    apply (simp add: add_env_def)
    apply (simp add: empty_env_def)
   apply (cut_tac la="tvar_type_l tau1" and lb="tvar_type_l tau2" and lc="l" in union_sub_list_rev)
    apply (auto)
   apply (rule_tac dist_union_sub_list)
    apply (simp_all)
  apply (cut_tac la="tvar_type_l tau1" and lb="tvar_type_l tau2" and lc="l" in union_sub_list_rev)
   apply (auto)
  apply (rule_tac dist_union_sub_list)
   apply (simp_all)
  done

lemma sol_subst_sub_list: "\<lbrakk> sub_list (tvar_type_l tau) l; sub_list (tvar_eq_list c_list) l \<rbrakk> \<Longrightarrow>
  sub_list (tvar_eq_list (sol_subst_eq_list (add_env empty_env x tau) c_list)) l"   
  apply (induct c_list arbitrary: l)
   apply (auto)
  apply (cut_tac la="union_list (tvar_type_l a) (tvar_type_l b)" and lb="tvar_eq_list c_list" and lc="l" in union_sub_list_rev)
   apply (auto)
  apply (cut_tac la="tvar_type_l a" and lb="tvar_type_l b" and lc="l" in union_sub_list_rev)
   apply (auto)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac sol_subst_type_sub_list)
     apply (auto)
  apply (rule_tac sol_subst_type_sub_list)
   apply (auto)
  done
    
lemma occurs_list_contain: "\<lbrakk> \<not> occurs tau x \<rbrakk> \<Longrightarrow> \<not> list_contain (tvar_type_l tau) x"    
  apply (induct tau)
         apply (auto)
   apply (cut_tac ?l1.0="tvar_type_l tau1" and ?l2.0="tvar_type_l tau2" in dist_union_list_contain)
    apply (auto)
  apply (cut_tac ?l1.0="tvar_type_l tau1" and ?l2.0="tvar_type_l tau2" in dist_union_list_contain)
   apply (auto)
  done
    
lemma sol_subst_type_list_contain: "\<lbrakk> \<not> occurs tau_x x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau)) x"
  apply (induct tau)
         apply (auto)
    apply (simp add: add_env_def)
    apply (case_tac "x = xa")
     apply (auto)
     apply (simp add: occurs_list_contain)
    apply (simp add: empty_env_def)
   apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau1)" and
      ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau2)" in dist_union_list_contain)
    apply (auto)
  apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau1)" and
      ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env x tau_x) tau2)" in dist_union_list_contain)
   apply (auto)
  done
    
lemma sol_subst_list_contain: "\<lbrakk> \<not> occurs tau x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (tvar_eq_list (sol_subst_eq_list (add_env empty_env x tau) c_list)) x"    
  apply (induct c_list)
   apply (auto)
  apply (cut_tac ?l1.0="union_list (tvar_type_l (sol_subst_type (add_env empty_env x tau) a)) (tvar_type_l (sol_subst_type (add_env empty_env x tau) b))"
      and ?l2.0="tvar_eq_list (sol_subst_eq_list (add_env empty_env x tau) c_list)" and x="x" in dist_union_list_contain)
   apply (auto)
  apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env x tau) a)"
      and ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env x tau) b)" and x="x" in dist_union_list_contain)
   apply (auto)
   apply (cut_tac tau_x="tau" and tau="a" and x="x" in sol_subst_type_list_contain)
    apply (auto)
  apply (cut_tac tau_x="tau" and tau="b" and x="x" in sol_subst_type_list_contain)
   apply (auto)
  done
    
lemma eur_less_tvar_total: "\<lbrakk> \<not> occurs tau x \<rbrakk> \<Longrightarrow>
  length (tvar_eq_list (sol_subst_eq_list (add_env empty_env x tau) c_list)) \<le>
  length (rem_list (union_list (add_list (tvar_type_l tau) x) (tvar_eq_list c_list)) x)"    
  apply (rule_tac sub_list_less_length)
   apply (rule_tac tvar_eq_fresh_list)
  apply (rule_tac rem_sub_list)
   apply (rule_tac sol_subst_sub_list)
    apply (rule_tac union_sub_list1)
    apply (rule_tac add_sub_list)
    apply (rule_tac id_sub_list)    
   apply (rule_tac union_sub_list2)
   apply (rule_tac id_sub_list)
  apply (rule_tac sol_subst_list_contain)
  apply (simp)
  done
    
lemma elim_unify_rel: "\<lbrakk> \<not> occurs tau x \<rbrakk> \<Longrightarrow>
  (sol_subst_eq_list (add_env empty_env x tau) c_list, (VarScheme x, tau) # c_list) \<in> unify_rel"
  apply (case_tac "\<not> length (tvar_eq_list (sol_subst_eq_list (add_env empty_env x tau) c_list))
     < length (union_list (add_list (tvar_type_l tau) x) (tvar_eq_list c_list))")
   apply (cut_tac tau="tau" and x="x" and c_list="c_list" in eur_less_tvar_total)
    apply (simp)
   apply (cut_tac l="union_list (add_list (tvar_type_l tau) x) (tvar_eq_list c_list)" and x="x" in contain_rem_list_length)
    apply (rule_tac union_list_contain1)
    apply (simp add: add_list_def)
   apply (auto)
  apply (simp add: unify_rel_def)
  apply (auto)
    apply (simp_all add: tvar_total_def)
  done
    
lemma dist_ut_term_less_length: "
  length (union_list (union_list (tvar_type_l t1) (tvar_type_l t2)) (union_list (union_list (tvar_type_l s1) (tvar_type_l s2)) (tvar_eq_list c_t))) \<le>
  length (union_list (union_list (union_list (tvar_type_l t1) (tvar_type_l s1)) (union_list (tvar_type_l t2) (tvar_type_l s2))) (tvar_eq_list c_t))"    
  apply (rule_tac sub_list_less_length)
   apply (rule_tac union_fresh_list)
    apply (rule_tac union_fresh_list)
     apply (rule_tac tvar_type_fresh_list)
    apply (rule_tac tvar_type_fresh_list)
   apply (rule_tac union_fresh_list)
    apply (rule_tac union_fresh_list)
     apply (rule_tac tvar_type_fresh_list)
    apply (rule_tac tvar_type_fresh_list)
   apply (rule_tac tvar_eq_fresh_list)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac union_sub_list1)
    apply (rule_tac union_sub_list1)
    apply (rule_tac id_sub_list)
   apply (rule_tac union_sub_list2)
   apply (rule_tac union_sub_list1)
   apply (rule_tac id_sub_list)
  apply (rule_tac dist_union_sub_list)
   apply (rule_tac union_sub_list1)
   apply (rule_tac dist_union_sub_list)
    apply (rule_tac union_sub_list1)
    apply (rule_tac union_sub_list2)
    apply (rule_tac id_sub_list)
   apply (rule_tac union_sub_list2)
   apply (rule_tac union_sub_list2)
   apply (rule_tac id_sub_list)
  apply (rule_tac union_sub_list2)
  apply (rule_tac id_sub_list)
  done
    
function unify_type where
  "unify_type [] = Some (empty_env, [])"
| "unify_type ((tau1, tau2) # c_t) = (case (tau1, tau2) of
    (VarScheme a, tau_x) \<Rightarrow>
      if tau_x = VarScheme a then unify_type c_t
      else if occurs tau_x a then None
      else (case unify_type (sol_subst_eq_list (add_env empty_env a tau_x) c_t) of
        None \<Rightarrow> None
        | Some (sigma, p_list) \<Rightarrow> Some (add_env sigma a (sol_subst_type sigma tau_x), p_list)
      )
    | (tau_x, VarScheme a) \<Rightarrow> unify_type ((VarScheme a, tau_x) # c_t)
    | (ArrayScheme t, ArrayScheme s) \<Rightarrow> unify_type ((t, s) # c_t)
    | (PairScheme t1 t2 p, PairScheme s1 s2 q) \<Rightarrow> (case unify_type ((t1, s1) # (t2, s2) # c_t) of
      None \<Rightarrow> None
      | Some (sigma, p_list) \<Rightarrow> Some (sigma, (p, q) # p_list)
    )
    | (FunScheme t1 t2 p a, FunScheme s1 s2 q b) \<Rightarrow> (case unify_type ((t1, s1) # (t2, s2) # c_t) of
      None \<Rightarrow> None
      | Some (sigma, p_list) \<Rightarrow> Some (sigma, (p, q) # (as_perm_s a, as_perm_s b) # p_list)
    )
    | (ChanScheme t c_end, ChanScheme s c_end') \<Rightarrow> if c_end = c_end' then unify_type ((t, s) # c_t) else None
    | (t1, t2) \<Rightarrow> if t1 = t2 then unify_type c_t else None
  )"
  by pat_completeness auto
termination
  apply (relation "unify_rel")
                      apply (auto)
    (* simple cases *)
                  apply (simp add: unify_rel_def)
                 apply (simp_all add: simp_unify_rel)
             apply (simp_all add: orient_unify_rel)
    (* elim case *)
      apply (simp add: elim_unify_rel)
    (* decomp cases *)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="c_t" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
    apply (auto)
   apply (simp add: unify_rel_def)
   apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="c_t" in dist_ut_term_less_length)
   apply (simp add: tvar_total_def)
   apply (auto)
  apply (simp add: unify_rel_def)
  apply (simp add: tvar_total_def)
  done

fun perm_subst_type where
  "perm_subst_type p_sub (ArrayScheme tau) = ArrayScheme (perm_subst_type p_sub tau)"
| "perm_subst_type p_sub (PairScheme t1 t2 r) = PairScheme (perm_subst_type p_sub t1) (perm_subst_type p_sub t2) (SPerm (sol_subst_perm p_sub r))"
| "perm_subst_type p_sub (FunScheme t1 t2 r a) =
  FunScheme (perm_subst_type p_sub t1) (perm_subst_type p_sub t2) (SPerm (sol_subst_perm p_sub r)) (AffConst (sol_subst_aff p_sub a))"    
| "perm_subst_type p_sub (ChanScheme tau c_end) = ChanScheme (perm_subst_type p_sub tau) c_end"
| "perm_subst_type p_sub tau_v = tau_v"  
  
fun type_eq_sat_f where
  "type_eq_sat_f t_sub p_sub [] = True"
| "type_eq_sat_f t_sub p_sub ((a, b) # c_t) = (perm_subst_type p_sub (sol_subst_type t_sub a) =
  perm_subst_type p_sub (sol_subst_type t_sub b) \<and> type_eq_sat_f t_sub p_sub c_t)"
  
definition type_eq_sat where
  "type_eq_sat t_sub p_sub c_list = type_eq_sat_f t_sub p_sub c_list" 
  
fun type_contains_f where
  "type_contains_f tau tau' = (if tau = tau' then True else case tau' of
    ArrayScheme tau_x \<Rightarrow> type_contains_f tau tau_x
    | PairScheme t1 t2 r \<Rightarrow> type_contains_f tau t1 \<or> type_contains_f tau t2
    | FunScheme t1 t2 p q \<Rightarrow> type_contains_f tau t1 \<or> type_contains_f tau t2
    | ChanScheme tau_x c_end \<Rightarrow> type_contains_f tau tau_x
    | tau_x \<Rightarrow> False
  )"
  
definition type_contains where
  "type_contains tau tau' = type_contains_f tau tau'"  
  
    (* if a is in tau, then t_sub(tau) will contain t_sub(a) *)(*
lemma occurs_type_contains: "\<lbrakk> occurs tau a; t_sub a = Some tau_x \<rbrakk> \<Longrightarrow> type_contains tau_x (part_subst_type t_sub tau)"  
  apply (induct tau)
         apply (auto)
        apply (simp add: type_contains_def)
  done*)
    
lemma array_no_self: "ArrayScheme tau \<noteq> tau"  
  apply (induct tau)
         apply (auto)
  done

lemma pair_no_self1: "PairScheme t1 t2 r \<noteq> t1"  
  apply (induct t1)
         apply (auto)
  done

lemma pair_no_self2: "PairScheme t1 t2 r \<noteq> t2"  
  apply (induct t2)
         apply (auto)
  done    
    
lemma fun_no_self1: "FunScheme t1 t2 p q \<noteq> t1"  
  apply (induct t1)
         apply (auto)
  done

lemma fun_no_self2: "FunScheme t1 t2 p q \<noteq> t2"  
  apply (induct t2)
         apply (auto)
  done
    
lemma chan_no_self: "ChanScheme tau c_end \<noteq> tau"  
  apply (induct tau)
         apply (auto)
  done
    
lemma type_contains_less_cons: "\<lbrakk> type_contains tau tau'; tau \<noteq> tau' \<rbrakk> \<Longrightarrow> type_cons tau < type_cons tau'"
  apply (induct tau')
         apply (auto)
         apply (simp add: type_contains_def)
        apply (simp add: type_contains_def)
       apply (simp add: type_contains_def)
      apply (simp add: type_contains_def)
     apply (case_tac "tau = tau'")
      apply (auto)
     apply (simp add: type_contains_def)
    apply (case_tac "tau = tau'1")
     apply (auto)
    apply (case_tac "tau = tau'2")
     apply (auto)
    apply (simp add: type_contains_def)
    apply (auto)
   apply (case_tac "tau = tau'1")
    apply (auto)
   apply (case_tac "tau = tau'2")
    apply (auto)
   apply (simp add: type_contains_def)
   apply (auto)
  apply (case_tac "tau = tau'")
   apply (auto)
  apply (simp add: type_contains_def)
  done
    
lemma trans_type_contains: "\<lbrakk> type_contains tau_a tau_b; type_contains tau_b tau_c \<rbrakk> \<Longrightarrow> type_contains tau_a tau_c"    
  apply (induct tau_c)
         apply (auto)
    (* int case *)
         apply (simp add: type_contains_def)
         apply (case_tac tau_b)
                apply (auto)
         apply (case_tac tau_a)
                apply (auto)
    (* unit case *)
        apply (simp add: type_contains_def)
        apply (case_tac tau_b)
               apply (auto)
        apply (case_tac tau_a)
               apply (auto)
    (* bool case *)
       apply (simp add: type_contains_def)
       apply (case_tac tau_b)
              apply (auto)
       apply (case_tac tau_a)
              apply (auto)
    (* var case *)
      apply (simp add: type_contains_def)
      apply (case_tac tau_b)
             apply (auto)
      apply (case_tac tau_a)
             apply (auto)
      apply (case_tac "x4 = x")
       apply (auto)
      apply (case_tac "x4a = x")
       apply (auto)
    (* array case *)
     apply (case_tac "\<not> type_contains tau_b tau_c")
      apply (case_tac "tau_b \<noteq> tau_c")
       apply (simp add: type_contains_def)
       apply (case_tac tau_b)
              apply (auto)
       apply (case_tac "x5 = tau_c")
        apply (auto)
      apply (simp add: type_contains_def)
     apply (simp add: type_contains_def)
    (* pair case *)
    apply (case_tac "type_contains tau_b tau_c1")
     apply (auto)
     apply (simp add: type_contains_def)
    apply (case_tac "type_contains tau_b tau_c2")
     apply (auto)
     apply (simp add: type_contains_def)
    apply (case_tac "tau_b \<noteq> PairScheme tau_c1 tau_c2 x3")
     apply (simp add: type_contains_def)
    apply (auto)
    (* fun case *)
   apply (case_tac "type_contains tau_b tau_c1")
    apply (auto)
    apply (simp add: type_contains_def)
   apply (case_tac "type_contains tau_b tau_c2")
    apply (auto)
    apply (simp add: type_contains_def)
   apply (case_tac "tau_b \<noteq> FunScheme tau_c1 tau_c2 x3 x4a")
    apply (simp add: type_contains_def)
   apply (auto)
    (* chan case *)
  apply (case_tac "type_contains tau_b tau_c")
   apply (auto)
   apply (simp add: type_contains_def)
  apply (case_tac "tau_b \<noteq> ChanScheme tau_c x2")
   apply (simp add: type_contains_def)
  apply (auto)
  done

lemma occurs_less_cons_ih: "\<lbrakk> occurs tau a; tau \<noteq> VarScheme a; t_sub a = Some tau_x \<rbrakk> \<Longrightarrow> type_cons tau_x < type_cons (sol_subst_type t_sub tau)"    
  apply (induct tau)
         apply (auto)
       apply (case_tac "tau = VarScheme a")
        apply (auto)
      apply (case_tac "tau1 = VarScheme a")
       apply (auto)
     apply (case_tac "tau2 = VarScheme a")
      apply (auto)
    apply (case_tac "tau1 = VarScheme a")
     apply (auto)
   apply (case_tac "tau2 = VarScheme a")
    apply (auto)
  apply (case_tac "tau = VarScheme a")
   apply (auto)
  done
    
lemma occurs_less_cons: "\<lbrakk> occurs tau a; tau \<noteq> VarScheme a \<rbrakk> \<Longrightarrow> type_cons (sol_subst_type t_sub (VarScheme a)) < type_cons (sol_subst_type t_sub tau)"      
  apply (auto)
  apply (case_tac "t_sub a")
   apply (auto)
   apply (case_tac tau)
          apply (auto)
  apply (rule_tac occurs_less_cons_ih)
    apply (auto)
  done
  
    (*
      base case - in the base case, say that we have array(a). obviously array(t_sub(a)) \<noteq> t_sub(a).
      inductive case - say that we have array(tau), where t_sub(tau) \<noteq> t_sub(a).
        we want to show that array(t_sub(tau)) \<noteq> t_sub(a) either. this would only be possible if t_sub(tau) was
        smaller than t_sub(a). so we want to know that t_sub(tau) is not contained in t_sub(a)
    *)
lemma occurs_not_sub_contains: "\<lbrakk> occurs tau a; tau \<noteq> VarScheme a; t_sub a = Some tau_x \<rbrakk> \<Longrightarrow> \<not> type_contains (sol_subst_type t_sub tau) tau_x"
  apply (induct tau)
         apply (auto)
    (* array case. say that tau = a. then we must show that array(t_sub(a)) \<notin> t_sub(a). *)
       apply (case_tac "tau = VarScheme a")
        apply (simp)
        apply (cut_tac tau="ArrayScheme tau_x" and tau'="tau_x" in type_contains_less_cons)
          apply (auto)
        apply (simp add: array_no_self)
    (* - otherwise, we use containment transitivity *)
       apply (cut_tac tau_a="sol_subst_type t_sub tau" and tau_b="ArrayScheme (sol_subst_type t_sub tau)" and tau_c="tau_x" in trans_type_contains)
         apply (simp add: type_contains_def)
        apply (auto)
    (* pair case 1. *)
      apply (case_tac "tau1 = VarScheme a")
       apply (simp)
       apply (cut_tac tau="PairScheme tau_x (sol_subst_type t_sub tau2) x3" and tau'="tau_x" in type_contains_less_cons)
         apply (auto)
       apply (simp add: pair_no_self1)
      apply (cut_tac tau_a="sol_subst_type t_sub tau1" and tau_b="PairScheme (sol_subst_type t_sub tau1) (sol_subst_type t_sub tau2) x3"
        and tau_c="tau_x" in trans_type_contains)
        apply (simp add: type_contains_def)
       apply (auto)
    (* pair case 2. *)
      apply (case_tac "tau2 = VarScheme a")
      apply (simp)
      apply (cut_tac tau="PairScheme (sol_subst_type t_sub tau1) tau_x x3" and tau'="tau_x" in type_contains_less_cons)
        apply (auto)
      apply (simp add: pair_no_self2)
     apply (cut_tac tau_a="sol_subst_type t_sub tau2" and tau_b="PairScheme (sol_subst_type t_sub tau1) (sol_subst_type t_sub tau2) x3"
        and tau_c="tau_x" in trans_type_contains)
       apply (simp add: type_contains_def)
      apply (auto)
    (* fun case 1. *)
    apply (case_tac "tau1 = VarScheme a")
     apply (simp)
     apply (cut_tac tau="FunScheme (sol_subst_type t_sub tau1) (sol_subst_type t_sub tau2) x3 x4a" and tau'="tau_x" in type_contains_less_cons)
       apply (auto)
     apply (simp add: fun_no_self1)
    apply (cut_tac tau_a="sol_subst_type t_sub tau1" and tau_b="FunScheme (sol_subst_type t_sub tau1) (sol_subst_type t_sub tau2) x3 x4a"
        and tau_c="tau_x" in trans_type_contains)
      apply (simp add: type_contains_def)
     apply (auto)
    (* fun case 2. *)
   apply (case_tac "tau2 = VarScheme a")
    apply (simp)
    apply (cut_tac tau="FunScheme (sol_subst_type t_sub tau1) tau_x x3 x4a" and tau'="tau_x" in type_contains_less_cons)
      apply (auto)
    apply (simp add: fun_no_self2)
   apply (cut_tac tau_a="sol_subst_type t_sub tau2" and tau_b="FunScheme (sol_subst_type t_sub tau1) (sol_subst_type t_sub tau2) x3 x4a"
        and tau_c="tau_x" in trans_type_contains)
     apply (simp add: type_contains_def)
    apply (auto)
    (* chan case. *)
  apply (case_tac "tau = VarScheme a")
   apply (simp)
   apply (cut_tac tau="ChanScheme tau_x x2" and tau'="tau_x" in type_contains_less_cons)
     apply (auto)
   apply (simp add: chan_no_self)
  apply (cut_tac tau_a="sol_subst_type t_sub tau" and tau_b="ChanScheme (sol_subst_type t_sub tau) x2" and tau_c="tau_x" in trans_type_contains)
    apply (simp add: type_contains_def)
   apply (auto)
  done
    
    (* if a is in tau, and a \<noteq> tau, then t_sub(a) \<noteq> t_sub(tau) *)
lemma occurs_not_sub_eq: "\<lbrakk> occurs tau a; tau \<noteq> VarScheme a \<rbrakk> \<Longrightarrow> (sol_subst_type t_sub (VarScheme a)) \<noteq> sol_subst_type t_sub tau"  
  apply (auto)
  apply (case_tac "t_sub a")
   apply (auto)
   apply (case_tac tau)
          apply (auto)
  apply (cut_tac t_sub="t_sub" and tau="tau" and a="a" and tau_x="sol_subst_type t_sub tau" in occurs_not_sub_contains)
     apply (auto)
  apply (simp add: type_contains_def)
  done
    
lemma sol_subst_type_eq: "\<lbrakk> perm_subst_type p_sub (sol_subst_type t_sub (VarScheme a)) = perm_subst_type p_sub (sol_subst_type t_sub t) \<rbrakk> \<Longrightarrow>
  perm_subst_type p_sub (sol_subst_type t_sub (sol_subst_type (add_env empty_env a t) tau)) = perm_subst_type p_sub (sol_subst_type t_sub tau)"    
  apply (induct tau)
         apply (auto)
  apply (simp add: add_env_def)
  apply (simp add: empty_env_def)
  apply (auto)
  done
    
lemma intern_sol_subst_type_eq_sat: "\<lbrakk> type_eq_sat_f t_sub p_sub c_list;
  perm_subst_type p_sub (sol_subst_type t_sub (VarScheme a)) = perm_subst_type p_sub (sol_subst_type t_sub tau) \<rbrakk> \<Longrightarrow>
  type_eq_sat_f t_sub p_sub (sol_subst_eq_list (add_env empty_env a tau) c_list)"
  apply (induct c_list)
   apply (auto)
  apply (simp add: sol_subst_type_eq)
  done
    
lemma perm_subst_same_cons: "type_cons tau = type_cons (perm_subst_type p_sub tau)"    
  apply (induct tau)
         apply (auto)
  done
    
    (*
lemma unify_type_unsat: "\<lbrakk> unify_type c_list = None \<rbrakk> \<Longrightarrow> \<not> type_eq_sat t_sub p_sub c_list"
  apply (simp add: type_eq_sat_def)
  apply (induct rule: unify_type.pelims)
    apply (auto)
    *)

lemma unify_type_unsat: "\<lbrakk> unify_type c_list = None \<rbrakk> \<Longrightarrow> \<not> type_eq_sat t_sub p_sub c_list"
  apply (simp add: type_eq_sat_def)
  apply (induct rule: wf_induct [where r=unify_rel])
   apply (auto)
   apply (simp add: unify_rel_def)
  apply (case_tac x)
   apply (auto)
    (* elim case *)
  apply (case_tac "\<exists> a'. a = VarScheme a'")
   apply (auto)
   apply (case_tac "b = VarScheme a'")
    apply (auto)
    apply (simp add: simp_unify_rel)
   apply (case_tac "occurs b a'")
    apply (auto)
    apply (cut_tac t_sub="t_sub" and tau="b" and a="a'" in occurs_less_cons)
      apply (auto)
    apply (cut_tac tau="sol_subst_type t_sub (VarScheme a')" and p_sub="p_sub" in perm_subst_same_cons)
    apply (cut_tac tau="sol_subst_type t_sub b" and p_sub="p_sub" in perm_subst_same_cons)
    apply (auto)
   apply (case_tac "unify_type (sol_subst_eq_list (add_env empty_env a' b) list)")
    apply (auto)
    (* - here we have to prove that if list[b / a'] is unsolvable, then list itself is unsatisfiable.
        we know that 'a \<rightarrow> t_sub('b) in t_sub by the current equality, which we can use to relate the two.
     *)
   apply (erule_tac x="sol_subst_eq_list (add_env empty_env a' b) list" in allE)
   apply (simp add: elim_unify_rel)
   apply (simp add: intern_sol_subst_type_eq_sat)
    (* orient case *)
  apply (case_tac "\<exists> b'. b = VarScheme b'")
   apply (auto)
   apply (erule_tac x=" (VarScheme b', a) # list" in allE)
   apply (simp add: orient_unify_rel)
   apply (case_tac a)
          apply (auto)
    (* decomp case. int *)
  apply (case_tac a)
         apply (auto)
        apply (case_tac b)
               apply (auto)
        apply (simp add: simp_unify_rel)
    (* - unit case *)
       apply (case_tac b)
              apply (auto)
       apply (simp add: simp_unify_rel)
    (* - bool case *)
      apply (case_tac b)
             apply (auto)
      apply (simp add: simp_unify_rel)
    (* - array case *)
     apply (case_tac b)
            apply (auto)
     apply (erule_tac x="(x5, x5a) # list" in allE)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
    (* - pair case *)
    apply (case_tac b)
           apply (auto)
    apply (erule_tac x="(x61, x61a) # (x62, x62a) # list" in allE)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="list" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
    apply (auto)
    (* - fun case *)
   apply (case_tac b)
          apply (auto)
   apply (erule_tac x="(x71, x71a) # (x72, x72a) # list" in allE)
   apply (simp add: unify_rel_def)
   apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="list" in dist_ut_term_less_length)
   apply (simp add: tvar_total_def)
   apply (auto)
    (* - chan case *)
  apply (case_tac b)
         apply (auto)
  apply (erule_tac x="(x81, x81a) # list" in allE)
  apply (simp add: unify_rel_def)
  apply (simp add: tvar_total_def)
  done

lemma add_env_eq: "\<lbrakk> env x = Some tau \<rbrakk> \<Longrightarrow> env = add_env env x tau"  
  apply (case_tac "\<forall> x'. env x' = add_env env x tau x'")
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "x = x'")
   apply (auto)
  done
  
fun perm_eq_sat_f where
  "perm_eq_sat_f p_sub [] = True"
| "perm_eq_sat_f p_sub ((p, q) # p_t) = (sol_subst_perm p_sub p = sol_subst_perm p_sub q \<and> perm_eq_sat_f p_sub p_t)"    
  
definition perm_eq_sat where
  "perm_eq_sat p_sub c_list = perm_eq_sat_f p_sub c_list"  
  
fun apply_type_subst where
  "apply_type_subst t_sub a = (case t_sub a of
    None \<Rightarrow> VarScheme a
    | Some tau \<Rightarrow> tau
  )"
  
type_synonym perm_var_subst = "s_perm subst_env" 
  
fun equiv_scheme where
  "equiv_scheme (ArrayScheme tau) tau' = (\<exists> tau_x. tau' = ArrayScheme tau_x \<and> equiv_scheme tau tau_x)"
| "equiv_scheme (PairScheme t1 t2 r) tau' = (\<exists> t1x t2x q. tau' = PairScheme t1x t2x q \<and> equiv_scheme t1 t1x \<and> equiv_scheme t2 t2x)"
| "equiv_scheme (FunScheme t1 t2 r a) tau' = (\<exists> t1x t2x q a'. tau' = FunScheme t1x t2x q a' \<and> equiv_scheme t1 t1x \<and> equiv_scheme t2 t2x)"
| "equiv_scheme (ChanScheme tau c_end) tau' = (\<exists> tau_x. tau' = ChanScheme tau_x c_end \<and> equiv_scheme tau tau_x)"
| "equiv_scheme tau tau' = (tau = tau')"  
    
lemma id_equiv_scheme: "equiv_scheme tau tau"  
  apply (induct tau)
         apply (auto)
  done
    
definition equiv_sub where
  "equiv_sub t_sub t_sub' = (\<forall> x. apply_type_subst t_sub x = apply_type_subst t_sub' x)"

definition subst_compose where
  "subst_compose t_sub t_sub' = (\<lambda> x. case t_sub x of
    None \<Rightarrow> t_sub' x
    | Some tau \<Rightarrow> Some (sol_subst_type t_sub' tau)
  )"    
    (*
fun perm_var_subst_perm where
  "perm_var_subst_perm p_sub (SPerm p) = SPerm p"
| "perm_var_subst_perm p_sub (SVar r) = (case p_sub r of
    None \<Rightarrow> SVar r
    | Some p \<Rightarrow> p
  )"  
 
fun as_aff_s where
  "as_aff_s (SPerm p) = AffConst (as_aff p)"  
| "as_aff_s (SVar r) = AffVar r"  
  
fun perm_var_subst_aff where
  "perm_var_subst_aff p_sub (AffConst a) = AffConst a"
| "perm_var_subst_aff p_sub (AffVar r) = (case p_sub r of
    None \<Rightarrow> AffVar r
    | Some p \<Rightarrow> as_aff_s p
  )"
  
fun perm_var_subst_type where
  "perm_var_subst_type p_sub (ArrayScheme tau) = ArrayScheme (perm_var_subst_type p_sub tau)"  
| "perm_var_subst_type p_sub (PairScheme t1 t2 r) =
  PairScheme (perm_var_subst_type p_sub t1) (perm_var_subst_type p_sub t2) (perm_var_subst_perm p_sub r)"  
| "perm_var_subst_type p_sub (FunScheme t1 t2 r a) =
  FunScheme (perm_var_subst_type p_sub t1) (perm_var_subst_type p_sub t2) (perm_var_subst_perm p_sub r) (perm_var_subst_aff p_sub a)"  
| "perm_var_subst_type p_sub (ChanScheme tau c_end) = ChanScheme (perm_var_subst_type p_sub tau) c_end"  
| "perm_var_subst_type p_sub tau = tau"  *)
  
definition perm_compose where
  "perm_compose p_sub t_sub = (\<lambda> x. case t_sub x of
    None \<Rightarrow> None
    | Some tau \<Rightarrow> Some (perm_subst_type p_sub tau)
  )"  
  
lemma empty_compose_equiv_sub: "equiv_sub (subst_compose empty_env t_sub) t_sub"  
  apply (simp add: equiv_sub_def)
  apply (simp add: subst_compose_def)
  apply (simp add: empty_env_def)(*
  apply (auto)
  apply (rule_tac id_equiv_scheme)*)
  done
    
definition wf_sub where
  "wf_sub t_sub = (\<forall> x. case t_sub x of
    None \<Rightarrow> True
    | Some tau_x \<Rightarrow> (\<forall> y. case t_sub y of
      None \<Rightarrow> True
      | Some tau \<Rightarrow> x \<notin> tvar_type tau
    )
  )"
  
definition type_sub_range where
  "type_sub_range t_sub = { x | x. \<exists> y. case t_sub y of None \<Rightarrow> False | Some tau \<Rightarrow> x \<in> tvar_type tau }"  
  
lemma tvar_type_occurs: "\<lbrakk> a \<in> tvar_type tau \<rbrakk> \<Longrightarrow> occurs tau a" 
  apply (induct tau)
         apply (auto)
  done
    
lemma sol_subst_tvar_type: "\<lbrakk> a \<notin> tvar_type tau; a \<notin> type_sub_range t_sub \<rbrakk> \<Longrightarrow> a \<notin> tvar_type (sol_subst_type t_sub tau)"    
  apply (induct tau)
         apply (auto)
  apply (case_tac "t_sub x")
   apply (auto)
  apply (simp add: type_sub_range_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma wf_sol_subst_tvar_type: "\<lbrakk> wf_sub t_sub; t_sub x = Some tau' \<rbrakk> \<Longrightarrow> x \<notin> tvar_type (sol_subst_type t_sub tau)"    
  apply (induct tau)
         apply (auto)
  apply (case_tac "t_sub xa")
   apply (auto)
  apply (simp add: wf_sub_def)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (auto)
  done
    
lemma add_wf_sub: "\<lbrakk> \<not> occurs tau a; a \<notin> type_sub_range t_sub; wf_sub t_sub \<rbrakk> \<Longrightarrow> wf_sub (add_env t_sub a (sol_subst_type t_sub tau))"
    (* we must show that for all x in the new t_sub, x does not appear on the right-hand side of any assignment y *)
  apply (simp add: wf_sub_def)
  apply (auto)
  apply (simp add: add_env_def)
  apply (auto)
    (* x = a, x = y (showing a does not appear in tau) *)
    apply (case_tac "a \<in> tvar_type tau")
     apply (simp add: tvar_type_occurs)
    apply (cut_tac a="a" and tau="tau" in sol_subst_tvar_type)
    apply (auto)
    (* x = a, x \<noteq> y (showing a does not appear on the right-hand side of anything else) *)
   apply (case_tac "t_sub y")
    apply (auto)
   apply (simp add: type_sub_range_def)
   apply (erule_tac x="y" in allE)
   apply (auto)
    (* x \<noteq> a *)
  apply (case_tac "t_sub x")
   apply (auto)
  apply (simp add: add_env_def)
    (* a = y (showing that none of the xs appear in the right-hand side of tau) *)
  apply (auto)
   apply (simp add: type_sub_range_def)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (cut_tac x="x" and t_sub="t_sub" and tau="tau" and tau'="aa" in wf_sol_subst_tvar_type)
     apply (auto)
   apply (simp add: wf_sub_def)
    (* a \<noteq> y (showing that none of the xs appear on the right-hand side of another) *)
  apply (erule_tac x="x" in allE)
  apply (auto)
  done
    
lemma dist_sol_subst_type_list_contain: "\<lbrakk> \<not> occurs tau_x x; \<not> occurs tau x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (tvar_type_l (sol_subst_type (add_env empty_env a tau_x) tau)) x"    
  apply (induct tau)
         apply (auto)
    apply (simp add: add_env_def)
    apply (case_tac "a = xa")
     apply (auto)
     apply (cut_tac tau="tau_x" and x="x" in occurs_list_contain)
      apply (auto)
    apply (simp add: empty_env_def)
   apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env a tau_x) tau1)"
      and ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env a tau_x) tau2)" and x="x" in dist_union_list_contain)
    apply (auto)
  apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env a tau_x) tau1)"
      and ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env a tau_x) tau2)" and x="x" in dist_union_list_contain)
   apply (auto)
  done
    
lemma occurs_list_contain_rev: "\<lbrakk> \<not> list_contain (tvar_type_l tau) x\<rbrakk> \<Longrightarrow> \<not> occurs tau x"    
  apply (induct tau)
         apply (auto)
     apply (case_tac "list_contain (tvar_type_l tau1) x")
      apply (cut_tac ?l1.0="tvar_type_l tau1" and x="x" in union_list_contain1)
       apply (auto)
    apply (case_tac "list_contain (tvar_type_l tau2) x")
     apply (cut_tac ?l2.0="tvar_type_l tau2" and x="x" in union_list_contain2)
      apply (auto)
   apply (case_tac "list_contain (tvar_type_l tau1) x")
    apply (cut_tac ?l1.0="tvar_type_l tau1" and x="x" in union_list_contain1)
     apply (auto)
  apply (case_tac "list_contain (tvar_type_l tau2) x")
   apply (cut_tac ?l2.0="tvar_type_l tau2" and x="x" in union_list_contain2)
    apply (auto)
  done
    
lemma dist_sol_subst_list_contain: "\<lbrakk> \<not> list_contain (tvar_eq_list c_list) x; \<not> occurs tau x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (tvar_eq_list (sol_subst_eq_list (add_env empty_env a tau) c_list)) x"    
  apply (induct c_list)
   apply (auto)
  apply (cut_tac ?l1.0="union_list (tvar_type_l (sol_subst_type (add_env empty_env a tau) aa)) (tvar_type_l (sol_subst_type (add_env empty_env a tau) b))"
      and ?l2.0="tvar_eq_list (sol_subst_eq_list (add_env empty_env a tau) c_list)" and x="x" in dist_union_list_contain)
   apply (auto)
  apply (cut_tac ?l1.0="tvar_type_l (sol_subst_type (add_env empty_env a tau) aa) "
      and ?l2.0="tvar_type_l (sol_subst_type (add_env empty_env a tau) b)" and x="x" in dist_union_list_contain)
    apply (auto)
    (* list containment for t1 *)
    apply (cut_tac a="a" and tau_x="tau" and tau="aa" and x="x" in dist_sol_subst_type_list_contain)
      apply (auto)
    apply (cut_tac tau="aa" and x="x" in occurs_list_contain_rev)
     apply (auto)
    apply (cut_tac ?l1.0="tvar_type_l aa" and ?l2.0="tvar_type_l b" and x="x" in union_list_contain1)
     apply (auto)
    apply (cut_tac ?l1.0="union_list (tvar_type_l aa) (tvar_type_l b)" and ?l2.0="tvar_eq_list c_list" and x="x" in union_list_contain1)
     apply (auto)
    (* list containment for t2 *)
   apply (cut_tac a="a" and tau_x="tau" and tau="b" and x="x" in dist_sol_subst_type_list_contain)
     apply (auto)
   apply (cut_tac tau="b" and x="x" in occurs_list_contain_rev)
    apply (auto)
   apply (cut_tac ?l1.0="tvar_type_l aa" and ?l2.0="tvar_type_l b" and x="x" in union_list_contain2)
    apply (auto)
   apply (cut_tac ?l1.0="union_list (tvar_type_l aa) (tvar_type_l b)" and ?l2.0="tvar_eq_list c_list" and x="x" in union_list_contain1)
    apply (auto)
    (* list containment for remainder *)
  apply (case_tac "list_contain (tvar_eq_list c_list) x")
   apply (cut_tac ?l1.0="union_list (tvar_type_l aa) (tvar_type_l b)" and ?l2.0="tvar_eq_list c_list" and x="x" in union_list_contain2)
    apply (auto)
  done
    
lemma tvar_type_l_rel: "\<lbrakk> x \<in> tvar_type tau \<rbrakk> \<Longrightarrow> list_contain (tvar_type_l tau) x"    
  apply (cut_tac tau="tau" and a="x" in tvar_type_occurs)
   apply (auto)
  apply (case_tac "\<not> list_contain (tvar_type_l tau) x")
   apply (cut_tac tau="tau" and x="x" in occurs_list_contain_rev)
    apply (auto)
  done

(*
    \<not> list_contain (add_list (tvar_eq_list list) b') x; x \<in> type_sub_range t_sub; list_contain (union_list (add_list [] b') (tvar_eq_list list)) x

\<not> list_contain (union_list (union_list (tvar_type_l x5) [b']) (tvar_eq_list list)) x; x \<in> type_sub_range t_sub;
        list_contain (union_list (add_list (tvar_type_l x5) b') (tvar_eq_list list)) 

*)
    
lemma orient_list_contain1: "\<lbrakk> \<not> list_contain (add_list (tvar_eq_list list) y) x \<rbrakk> \<Longrightarrow> \<not> list_contain (union_list (add_list [] y) (tvar_eq_list list)) x"    
  apply (auto)
  apply (simp add: add_list_def)
  done
    
lemma add_union_list_contain: "\<lbrakk> list_contain (add_list l a) x \<rbrakk> \<Longrightarrow> list_contain (union_list l [a]) x"    
  apply (induct l)
   apply (auto)
   apply (simp add: add_list_def)
  apply (simp add: add_list_def)
  apply (auto)
   apply (case_tac "a = aa \<or> list_contain l a")
    apply (auto)
  apply (case_tac "a = aa \<or> list_contain l a")
   apply (auto)
  apply (case_tac "list_contain l a")
   apply (auto)
  done
    
lemma orient_list_contain2: "\<lbrakk> \<not> list_contain (union_list (union_list l [a]) (tvar_eq_list list)) x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (union_list (add_list l a) (tvar_eq_list list)) x"    
  apply (auto)
  apply (cut_tac ?l1.0="add_list l a" and ?l2.0="tvar_eq_list list" and x="x" in dist_union_list_contain)
   apply (auto)
   apply (cut_tac ?l1.0="union_list l [a]" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain1)
    apply (auto)
   apply (rule_tac add_union_list_contain)
   apply (auto)
  apply (cut_tac ?l1.0="union_list l [a]" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain2)
   apply (auto)
  done    

lemma dist_union_list_contain_split: "\<lbrakk> \<not> list_contain la x; \<not> list_contain lb x \<rbrakk> \<Longrightarrow> \<not> list_contain (union_list la lb) x"    
  apply (auto)
  apply (cut_tac ?l1.0="la" and ?l2.0="lb" in dist_union_list_contain)
   apply (auto)
  done

lemma dist_union_list_contain_split_ex: "\<lbrakk> list_contain (union_list la lb) x; list_contain la x \<longrightarrow> X; list_contain lb x \<longrightarrow> X \<rbrakk> \<Longrightarrow> X"    
  apply (auto)
  apply (cut_tac ?l1.0="la" and ?l2.0="lb" in dist_union_list_contain)
   apply (auto)
  done    
    
lemma dist_ut_list_contain: "\<lbrakk> list_contain (union_list (union_list (tvar_type_l x61) (tvar_type_l x61a))
  (union_list (union_list (tvar_type_l x62) (tvar_type_l x62a)) (tvar_eq_list list))) x \<rbrakk> \<Longrightarrow> list_contain (union_list (union_list
  (union_list (tvar_type_l x61) (tvar_type_l x62)) (union_list (tvar_type_l x61a) (tvar_type_l x62a))) (tvar_eq_list list)) x"    
  apply (rule_tac dist_union_list_contain_split_ex)
    apply (auto)
   apply (rule_tac union_list_contain1)
   apply (rule_tac la="tvar_type_l x61" in dist_union_list_contain_split_ex)
     apply (auto)
    apply (rule_tac union_list_contain1)
    apply (rule_tac union_list_contain1)
    apply (simp)
   apply (rule_tac union_list_contain2)
   apply (rule_tac union_list_contain1)
   apply (simp)
  apply (rule_tac la="union_list (tvar_type_l x62) (tvar_type_l x62a)" in dist_union_list_contain_split_ex)
    apply (auto)
   apply (rule_tac union_list_contain1)
   apply (rule_tac la="tvar_type_l x62" in dist_union_list_contain_split_ex)
     apply (auto)
    apply (rule_tac union_list_contain1)
    apply (rule_tac union_list_contain2)
    apply (simp)
   apply (rule_tac union_list_contain2)
   apply (rule_tac union_list_contain2)
   apply (simp)
  apply (rule_tac union_list_contain2)
  apply (simp)
  done
    
lemma dist_ut_list_contain_rev: "\<lbrakk> \<not> list_contain (union_list (union_list
  (union_list (tvar_type_l x61) (tvar_type_l x62)) (union_list (tvar_type_l x61a) (tvar_type_l x62a))) (tvar_eq_list list)) x \<rbrakk> \<Longrightarrow>
  \<not> list_contain (union_list (union_list (tvar_type_l x61) (tvar_type_l x61a))
  (union_list (union_list (tvar_type_l x62) (tvar_type_l x62a)) (tvar_eq_list list))) x"
  apply (auto)
  apply (simp add: dist_ut_list_contain)
  done
    
definition utsr_res where
  "utsr_res t_sub x = (x \<notin> type_sub_range t_sub \<and> t_sub x = None)"
    
lemma unify_type_sub_range_ih: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq); \<not> list_contain (tvar_eq_list c_list) x \<rbrakk> \<Longrightarrow> utsr_res t_sub x" 
  apply (induct arbitrary: t_sub p_eq rule: wf_induct [where r=unify_rel])
   apply (simp add: unify_rel_def) 
  apply (case_tac xa)
   apply (auto)
   apply (simp add: utsr_res_def)
   apply (simp add: type_sub_range_def)
   apply (simp add: empty_env_def)
    (* var case. delete *)
  apply (case_tac "\<exists> a'. a = VarScheme a'")
   apply (auto)
   apply (case_tac "b = VarScheme a'")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_unify_rel)
    apply (auto)
    apply (cut_tac ?l1.0="add_list [a'] a'" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain2)
     apply (auto)
    (* - occurs *)
   apply (case_tac "occurs b a'")
    apply (auto)
    (* - elim *)
   apply (case_tac "unify_type (sol_subst_eq_list (add_env empty_env a' b) list)")
    apply (auto)
   apply (erule_tac x="sol_subst_eq_list (add_env empty_env a' b) list" in allE)
   apply (auto)
     apply (simp add: elim_unify_rel)
    apply (cut_tac a="a'" and tau="b" and c_list="list" and x="x" in dist_sol_subst_list_contain)
      apply (auto)
     apply (cut_tac ?l1.0="add_list (tvar_type_l b) a'" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain2)
      apply (auto)
    apply (cut_tac tau="b" and x="x" in occurs_list_contain_rev)
     apply (auto)
     apply (cut_tac ?l1.0="add_list (tvar_type_l b) a'" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain1)
     apply (auto)
    apply (simp add: add_list_def)
   apply (simp add: utsr_res_def)
   apply (auto)
    apply (simp add: type_sub_range_def)
    apply (simp add: add_env_def)
    apply (auto)
    apply (case_tac "a' = y")
     apply (auto)
    apply (cut_tac a="x" and t_sub="a" and tau="b" in sol_subst_tvar_type)
      apply (auto)
     apply (cut_tac tau="b" and x="x" in tvar_type_l_rel)
      apply (auto)
     apply (cut_tac ?l1.0="add_list (tvar_type_l b) y" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain1)
      apply (auto)
     apply (simp add: add_list_def)
    apply (simp add: type_sub_range_def)
   apply (simp add: add_env_def)
   apply (auto)
   apply (case_tac "list_contain (add_list (tvar_type_l b) x) x")
    apply (cut_tac ?l1.0="add_list (tvar_type_l b) x" and ?l2.0="tvar_eq_list list" and x="x" in union_list_contain1)
     apply (auto)
   apply (simp add: add_list_def)
   apply (case_tac "list_contain (tvar_type_l b) x")
    apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> b'. b = VarScheme b'")
   apply (auto)
   apply (erule_tac x="(VarScheme b', a) # list" in allE)
   apply (auto)
    apply (simp add: orient_unify_rel)
   apply (case_tac a)
    apply (auto)
         apply (simp add: orient_list_contain1)
        apply (simp add: orient_list_contain1)
       apply (simp add: orient_list_contain1)
      apply (simp add: orient_list_contain2)
     apply (simp add: orient_list_contain2)
    apply (simp add: orient_list_contain2)
   apply (simp add: orient_list_contain2)
    (* decomp case *)
  apply (case_tac a)
         apply (auto)
        apply (case_tac b)
               apply (auto)
        apply (erule_tac x="list" in allE)
        apply (auto)
        apply (simp add: simp_unify_rel)
       apply (case_tac b)
              apply (auto)
       apply (erule_tac x="list" in allE)
       apply (auto)
       apply (simp add: simp_unify_rel)
      apply (case_tac b)
             apply (auto)
      apply (erule_tac x="list" in allE)
      apply (auto)
      apply (simp add: simp_unify_rel)
    (* - array case *)
     apply (case_tac b)
            apply (auto)
     apply (erule_tac x="(x5, x5a) # list" in allE)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
    (* - pair case *)
    apply (case_tac b)
           apply (auto)
    apply (erule_tac x="(x61, x61a) # (x62, x62a) # list" in allE)
    apply (auto)
     apply (simp add: unify_rel_def)
     apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="list" in dist_ut_term_less_length)
     apply (simp add: tvar_total_def)
    apply (simp add: dist_ut_list_contain_rev)
    apply (case_tac "unify_type ((x61, x61a) # (x62, x62a) # list)")
     apply (auto)
    (* - fun case *)
   apply (case_tac b)
          apply (auto)
   apply (erule_tac x="(x71, x71a) # (x72, x72a) # list" in allE)
    apply (auto)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="list" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
   apply (simp add: dist_ut_list_contain_rev)
   apply (case_tac "unify_type ((x71, x71a) # (x72, x72a) # list)")
    apply (auto)
    (* - chan case *)
  apply (case_tac b)
         apply (auto)
  apply (erule_tac x="(x81, x81a) # list" in allE)
  apply (auto)
   apply (simp add: unify_rel_def)
   apply (simp add: tvar_total_def)
  apply (case_tac "x82 = x82a")
   apply (auto)
  done
    
lemma unify_type_sub_range: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq); \<not> list_contain (tvar_eq_list c_list) x \<rbrakk> \<Longrightarrow> x \<notin> type_sub_range t_sub"     
  apply (cut_tac x="x" and t_sub="t_sub" in unify_type_sub_range_ih)
    apply (auto)
  apply (simp add: utsr_res_def)
  done

lemma unify_type_sub_dom: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq); \<not> list_contain (tvar_eq_list c_list) x \<rbrakk> \<Longrightarrow> t_sub x = None"     
  apply (cut_tac x="x" and t_sub="t_sub" in unify_type_sub_range_ih)
    apply (auto)
  apply (simp add: utsr_res_def)
  done
  
lemma unify_type_wf_sub: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq) \<rbrakk> \<Longrightarrow> wf_sub t_sub"  
  apply (induct arbitrary: t_sub p_eq rule: wf_induct [where r=unify_rel])
   apply (simp add: unify_rel_def) 
  apply (case_tac x)
   apply (auto)
   apply (simp add: wf_sub_def)
   apply (simp add: empty_env_def)
    (* var case. delete *)
  apply (case_tac "\<exists> a'. a = VarScheme a'")
   apply (auto)
   apply (case_tac "b = VarScheme a'")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_unify_rel)
    (* - occurs *)
   apply (case_tac "occurs b a'")
    apply (auto)
    (* - elim *)
   apply (case_tac "unify_type (sol_subst_eq_list (add_env empty_env a' b) list)")
    apply (auto)
   apply (erule_tac x="sol_subst_eq_list (add_env empty_env a' b) list" in allE)
   apply (simp add: elim_unify_rel)
   apply (rule_tac add_wf_sub)
     apply (auto)
   apply (cut_tac t_sub="a" and x="a'" in unify_type_sub_range)
     apply (auto)
   apply (cut_tac x="a'" and c_list="list" in sol_subst_list_contain)
    apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> b'. b = VarScheme b'")
   apply (auto)
   apply (erule_tac x="(VarScheme b', a) # list" in allE)
   apply (simp add: orient_unify_rel)
   apply (case_tac a)
          apply (auto)
    (* decomp case *)
  apply (case_tac a)
         apply (auto)
        apply (case_tac b)
               apply (auto)
        apply (erule_tac x="list" in allE)
        apply (auto)
        apply (simp add: simp_unify_rel)
       apply (case_tac b)
              apply (auto)
       apply (erule_tac x="list" in allE)
       apply (auto)
       apply (simp add: simp_unify_rel)
      apply (case_tac b)
             apply (auto)
      apply (erule_tac x="list" in allE)
      apply (auto)
      apply (simp add: simp_unify_rel)
    (* - array case *)
     apply (case_tac b)
            apply (auto)
     apply (erule_tac x="(x5, x5a) # list" in allE)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
    (* - pair case *)
    apply (case_tac b)
           apply (auto)
    apply (erule_tac x="(x61, x61a) # (x62, x62a) # list" in allE)
    apply (auto)
     apply (simp add: unify_rel_def)
     apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="list" in dist_ut_term_less_length)
     apply (simp add: tvar_total_def)
    apply (case_tac "unify_type ((x61, x61a) # (x62, x62a) # list)")
     apply (auto)
    (* - fun case *)
   apply (case_tac b)
          apply (auto)
   apply (erule_tac x="(x71, x71a) # (x72, x72a) # list" in allE)
    apply (auto)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="list" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
   apply (case_tac "unify_type ((x71, x71a) # (x72, x72a) # list)")
    apply (auto)
    (* - chan case *)
  apply (case_tac b)
         apply (auto)
  apply (erule_tac x="(x81, x81a) # list" in allE)
  apply (auto)
   apply (simp add: unify_rel_def)
   apply (simp add: tvar_total_def)
  apply (case_tac "x82 = x82a")
   apply (auto)
  done
    
lemma occurs_tvar_type: "occurs tau x \<Longrightarrow> x \<in> tvar_type tau"    
  apply (induct tau)
         apply (auto)
  done
    
    (* \<lbrakk>x4a \<noteq> x4; unify_type (sol_subst_eq_list (add_env empty_env x4a (VarScheme x4)) list) = Some (a, p_eq); perm_eq_sat p_sub p_eq;
        equiv_sub (subst_compose a t_sub') t_subx; t_subx x4a = None; type_eq_sat_f t_subx p_sub list; t_subx x4 = Some (VarScheme x4a)\<rbrakk>
       \<Longrightarrow> equiv_sub (subst_compose (add_env a x4a (case a x4 of None \<Rightarrow> VarScheme x4 | Some tau \<Rightarrow> tau)) (add_env t_sub' x4 (VarScheme x4a))) t_subx *)
  
lemma cancel_add_env: "\<lbrakk> env x = Some tau \<rbrakk> \<Longrightarrow> add_env env x tau = env"    
  apply (case_tac "\<forall> y. add_env env x tau y = env y")  
   apply (auto)
  apply (simp add: add_env_def)
  apply (case_tac "x = y")
   apply (auto)
  done
    
lemma add_sol_subst_type: "\<lbrakk> \<not> occurs tau a \<rbrakk> \<Longrightarrow>
  sol_subst_type (add_env t_sub a t) tau = sol_subst_type t_sub tau"    
  apply (induct tau)
         apply (auto)
  apply (simp add: add_env_def)
  done
    
lemma comm_equiv_scheme: "equiv_scheme tau tau' \<Longrightarrow> equiv_scheme tau' tau"    
  apply (induct tau arbitrary: tau')
         apply (auto)
  done

lemma trans_equiv_scheme: "\<lbrakk> equiv_scheme ta tb; equiv_scheme tb tc \<rbrakk> \<Longrightarrow> equiv_scheme ta tc"    
  apply (induct ta arbitrary: tb tc)
         apply (auto)
  done

lemma perm_subst_equiv_scheme: "\<lbrakk> perm_subst_type p_sub tau = perm_subst_type p_sub tau' \<rbrakk> \<Longrightarrow> equiv_scheme tau tau'"    
  apply (induct tau arbitrary: tau')  
         apply (auto)
         apply (case_tac tau')
                apply (auto)
        apply (case_tac tau')
               apply (auto)
       apply (case_tac tau')
              apply (auto)
      apply (case_tac tau')
             apply (auto)
     apply (case_tac tau')
            apply (auto)
    apply (case_tac tau')
           apply (auto)
   apply (case_tac tau')
          apply (auto)
  apply (case_tac tau')
         apply (auto)
  done
    
lemma expand_subst_compose: "sol_subst_type (subst_compose t_sub t_sub') tau = sol_subst_type t_sub' (sol_subst_type t_sub tau)"    
  apply (induct tau)
         apply (auto)
  apply (simp add: subst_compose_def)
  apply (case_tac "t_sub x")
   apply (auto)
  done
    
lemma double_perm_subst_type: "perm_subst_type p_sub tau = perm_subst_type p_sub (perm_subst_type p_sub tau)"    
  apply (induct tau)
         apply (auto)
  done
  
lemma compose_perm_subst_type: "perm_subst_type p_sub (sol_subst_type t_sub tau) = perm_subst_type p_sub (sol_subst_type (perm_compose p_sub t_sub) tau)"
  apply (induct tau)
         apply (auto)
  apply (simp add: perm_compose_def)
  apply (case_tac "t_sub x")
   apply (auto)
  apply (rule_tac double_perm_subst_type)
  done    
    
    (* say that we encounter constraint { a = b }. in our solution we want to select { a \<rightarrow> b }, but the given solution selects { b \<rightarrow> a }.
        we can translate one solution to the other by adding { b \<rightarrow> a } to the composition.  *)
lemma add_compose_equiv_sub: "\<lbrakk> equiv_sub (perm_compose p_sub (subst_compose t_sub t_sub')) (perm_compose p_sub t_subx);
  apply_type_subst t_subx a = VarScheme a; t_subx b = Some (VarScheme a); a \<noteq> b; wf_sub t_sub \<rbrakk> \<Longrightarrow>
  equiv_sub (perm_compose p_sub (subst_compose (add_env t_sub a (VarScheme b)) (add_env t_sub' b (VarScheme a)))) (perm_compose p_sub t_subx)"    
  apply (simp add: equiv_sub_def)
  apply (auto)
  apply (simp add: perm_compose_def)
  apply (simp add: subst_compose_def)
  apply (simp add: add_env_def)
  apply (auto)
    (* x = a *)
   apply (case_tac "t_subx a")
    apply (auto)
    (* x = b, there exists some c where t_sub: b \<rightarrow> c, t_sub': c \<rightarrow> x, where x is some var (meaning c is some var).
        whether b = c or not, the correct result follows
    *)
  apply (case_tac "x = b")
   apply (auto)
   apply (case_tac "t_sub b")
    apply (auto)
    apply (simp add: add_env_def)
   apply (erule_tac x="b" in allE)
   apply (auto)
   apply (case_tac aa)
          apply (auto)
   apply (simp add: add_env_def)
    (* otherwise, say t_sub: x \<rightarrow> x. this case is unchanged by NEW t_sub' *)
  apply (case_tac "t_sub x")
   apply (auto)
   apply (erule_tac x="x" in allE)
   apply (auto)
   apply (simp add: add_env_def)
    (* say that b occurs in t_sub(x). for this to work, we want t_sub': b \<rightarrow> a how can we show this? say that this was not the case.
        t_subx: b \<rightarrow> a, which means that either t_sub: b \<rightarrow> c and t_sub': c \<rightarrow> a, OR t_sub: b \<rightarrow> a.
          both are impossible since we can assume by construction of t_sub that it is "well-formed", namely that
          all variables with an assignment do not appear on the RHS of a substitution.
    *)
  apply (case_tac "occurs aa b")
   apply (case_tac "t_sub' b \<noteq> Some (VarScheme a)")
    apply (case_tac "t_sub b = None")
     apply (erule_tac x="b" in allE)
     apply (auto)
     apply (case_tac "t_sub' b")
      apply (auto)
     apply (case_tac aaa)
            apply (auto)
    apply (simp add: wf_sub_def)
    apply (erule_tac x="n" in allE)
    apply (erule_tac x="b" in allE)
    apply (auto)
    apply (erule_tac x="x" in allE)
    apply (auto)
    apply (cut_tac occurs_tvar_type)
     apply (auto)
    (* knowing that t_sub': b \<rightarrow> a, t_sub' is unchanged *)
   apply (simp add: cancel_add_env)
   apply (erule_tac x="x" in allE)
   apply (auto)
    (* lastly, we can analyze the case where t_sub: x \<rightarrow> anything else *)
  apply (erule_tac x="x" in allE)
  apply (auto)
  apply (case_tac "t_subx x")
   apply (auto)
   apply (case_tac aa)
          apply (auto)
   apply (simp add: add_env_def)
  apply (simp add: add_sol_subst_type)
  done
    
lemma equiv_sub_type: "\<lbrakk> equiv_sub t_sub t_sub' \<rbrakk> \<Longrightarrow> sol_subst_type t_sub tau = sol_subst_type t_sub' tau"    
  apply (induct tau)
         apply (auto)
  apply (simp add: equiv_sub_def)
  done    
    
lemma as_perm_sol_subst_aff: "sol_subst_perm p_sub (as_perm_s a) = as_perm (sol_subst_aff p_sub a)"    
  apply (case_tac a)
   apply (auto)
  apply (case_tac "p_sub x2")
    apply (auto)
  done    
    
lemma id_equiv_sub: "equiv_sub t_sub t_sub"    
  apply (simp add: equiv_sub_def)
  done
  
lemma comm_equiv_sub: "equiv_sub t_sub t_sub' \<Longrightarrow> equiv_sub t_sub' t_sub"    
  apply (simp add: equiv_sub_def)
  done    
    
lemma empty_subst_compose: "subst_compose empty_env t_sub = t_sub"    
  apply (case_tac "\<forall> x. subst_compose empty_env t_sub x = t_sub x")  
   apply (auto)
  apply (simp add: subst_compose_def)
  apply (simp add: empty_env_def)
  done
    
definition uts_res where
  "uts_res t_sub t_subx p_sub p_eq = ((\<exists> t_sub'. equiv_sub (perm_compose p_sub (subst_compose t_sub t_sub')) (perm_compose p_sub t_subx)) \<and> perm_eq_sat p_sub p_eq)"       

    (* if unification returns successfully, and the constraint list is satisfiable, then the satisfying type substitution of the solution
          will be a specialization of the one returned by type substitution, and the permission substitution will satisfy p_eq *)
lemma unify_type_sat: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq); type_eq_sat t_subx p_sub c_list \<rbrakk> \<Longrightarrow> uts_res t_sub t_subx p_sub p_eq"
  apply (induct arbitrary: t_sub p_eq rule: wf_induct [where r=unify_rel])
   apply (simp add: unify_rel_def)
  apply (case_tac x)
   apply (auto)
   apply (simp add: uts_res_def)
   apply (simp add: perm_eq_sat_def)
   apply (rule_tac x="t_subx" in exI)
   apply (simp add: empty_subst_compose)
   apply (rule_tac id_equiv_sub)
    (* elim case *)
  apply (case_tac "\<exists> a'. a = VarScheme a'")
   apply (auto)
    (* - delete case *)
   apply (case_tac "b = VarScheme a'")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_unify_rel)
    apply (simp add: type_eq_sat_def)
    (* - occurs case *)
   apply (case_tac "occurs b a'")
    apply (auto)
    (* - standard case *)
   apply (case_tac "unify_type (sol_subst_eq_list (add_env empty_env a' b) list)")
    apply (auto)
   apply (erule_tac x="sol_subst_eq_list (add_env empty_env a' b) list" in allE)
   apply (auto)
     apply (simp add: elim_unify_rel)
    apply (simp add: type_eq_sat_def)
    apply (auto)
    apply (simp add: intern_sol_subst_type_eq_sat)
   apply (simp add: uts_res_def)
   apply (auto)
    (* > say that t_subx a' = None (or to itself). since 'a = b, this would only be the case if b was another variable, and t_subx b = a' *)
   apply (case_tac "apply_type_subst t_subx a' = VarScheme a'")
    apply (simp add: type_eq_sat_def)
    apply (auto)
    apply (case_tac b)
           apply (auto)
    apply (case_tac "t_subx x4")
     apply (auto)
    apply (case_tac aa)
           apply (auto)
    (* > say that t_sub doesn't map b. then t_sub(b) = b
        we know that [[ a o t_sub' = t_subx ]]. so then [[ a + { 'a: b } o t_sub' + { b: 'a } =  t_subx ]] ('a = x4a, b = x4) *)
    apply (case_tac "a x4")
     apply (auto)
     apply (rule_tac x="add_env t_sub' x4 (VarScheme x4a)" in exI)
     apply (cut_tac t_sub="a" and t_sub'="t_sub'" and t_subx="t_subx" and a="x4a" and b="x4" and p_sub="p_sub" in add_compose_equiv_sub)
          apply (auto)
     apply (rule_tac unify_type_wf_sub)
     apply (auto)
    (* > otherwise, we have t_sub mapping b to some variable c. *)
    apply (case_tac "\<not> (\<exists> c. a x4 = Some (VarScheme c))")
     apply (simp add: equiv_sub_def)
     apply (simp add: perm_compose_def)
     apply (simp add: subst_compose_def)
     apply (erule_tac x="x4" in allE)
     apply (auto)
     apply (case_tac aa)
            apply (auto)
    (* > say that c = a. this is impossible since then a would be in t_sub's range *)
    apply (case_tac "c = x4a")
     apply (cut_tac x="x4a" and c_list="sol_subst_eq_list (add_env empty_env x4a (VarScheme x4)) list" in unify_type_sub_range)
       apply (auto)
      apply (cut_tac x="x4a" and c_list="list" in sol_subst_list_contain)
       apply (auto)
     apply (simp add: type_sub_range_def)
     apply (erule_tac x="x4" in allE)
     apply (auto)
    (* > we claim [[ a + { 'a: t_sub(b) = c } o t_sub' + { c: 'a } = t_subx ]] should work *)
    apply (rule_tac x="add_env t_sub' c (VarScheme x4a)" in exI)
    apply (cut_tac t_sub="a" and t_sub'="t_sub'" and t_subx="t_subx" and a="x4a" and b="c" in add_compose_equiv_sub)
         apply (auto)
    (* >> t_sub: c \<rightarrow> c by well-formedness *)
     apply (case_tac "a c \<noteq> None")
      apply (cut_tac c_list="sol_subst_eq_list (add_env empty_env x4a (VarScheme x4)) list" and t_sub="a" in unify_type_wf_sub)
       apply (auto)
      apply (simp add: wf_sub_def)
      apply (erule_tac x="c" in allE)
      apply (auto)
      apply (erule_tac x="x4" in allE)
      apply (auto)
    (* >> t_subx: c \<rightarrow> a, since t_sub: b \<rightarrow> c and t_subx: b \<rightarrow> a, meaning t_sub': c \<rightarrow> a *)
     apply (case_tac "t_sub' c \<noteq> Some (VarScheme x4a)")
      apply (simp add: equiv_sub_def)
      apply (simp add: perm_compose_def)
      apply (simp add: subst_compose_def)
      apply (erule_tac x="x4" in allE)
      apply (auto)
      apply (case_tac "t_sub' c")
       apply (auto)
      apply (case_tac aa)
             apply (auto)
    (* >> using equivalence to put these facts together *)
     apply (simp add: equiv_sub_def)
     apply (erule_tac x="c" in allE)
     apply (simp add: perm_compose_def)
     apply (simp add: subst_compose_def)
     apply (case_tac "t_subx c")
      apply (auto)
     apply (case_tac aa)
            apply (auto)
    apply (rule_tac unify_type_wf_sub)
    apply (auto)
      (* > otherwise, we know that t_subx(a') maps to something besides a'. we know that t_sub(a') = None,
          meaning that t_sub'(a') = t_subx(a'), meaning that we shouldn't have to change the mapping. *)
   apply (case_tac "t_subx a'")
    apply (auto)
   apply (rule_tac x="t_sub'" in exI)
   apply (case_tac "a a' \<noteq> None")
    apply (cut_tac t_sub="a" and x="a'" in unify_type_sub_dom)
      apply (auto)
    apply (cut_tac x="a'" and tau="b" and c_list="list" in sol_subst_list_contain)
     apply (auto)
   apply (case_tac "\<not> perm_subst_type p_sub (apply_type_subst t_sub' a') = perm_subst_type p_sub aa")
    apply (simp add: equiv_sub_def)
    apply (simp add: perm_compose_def)
    apply (simp add: subst_compose_def)
    apply (erule_tac x="a'" in allE)
    apply (auto)
    apply (case_tac "t_sub' a'")
     apply (auto)
   apply (simp add: equiv_sub_def)
   apply (simp add: perm_compose_def)
   apply (simp add: subst_compose_def)
   apply (case_tac "\<not> equiv_sub (perm_compose p_sub (subst_compose a t_sub')) (perm_compose p_sub t_subx)")
    apply (simp add: equiv_sub_def)
    apply (simp add: perm_compose_def)
    apply (simp add: subst_compose_def)
   apply (auto)
   apply (simp add: add_env_def)
   apply (auto)
    (* >> we utilize the equations to show equality *)
   apply (simp add: type_eq_sat_def)
   apply (auto)
   apply (rule_tac t="sol_subst_type t_sub' (sol_subst_type a b)" and s="sol_subst_type (subst_compose a t_sub') b" in subst)
    apply (rule_tac expand_subst_compose)
   apply (cut_tac p_sub="p_sub" and t_sub="subst_compose a t_sub'" and tau="b" in compose_perm_subst_type)
   apply (auto)
   apply (cut_tac p_sub="p_sub" and t_sub="t_subx" and tau="b" in compose_perm_subst_type)
   apply (auto)
     (* >> we manipulate to activate this lemma concerning application of equivalent substitutions *)
   apply (rule_tac t="sol_subst_type (perm_compose p_sub (subst_compose a t_sub')) b" and s="sol_subst_type (perm_compose p_sub t_subx) b" in subst)
    apply (rule_tac equiv_sub_type)
    apply (rule_tac comm_equiv_sub)
    apply (auto)
      (* orient case *)
  apply (case_tac "\<exists> b'. b = VarScheme b'")
   apply (auto)
   apply (erule_tac x="(VarScheme b', a) # list" in allE)
   apply (simp add: orient_unify_rel)
   apply (simp add: type_eq_sat_def)
   apply (case_tac a)
          apply (auto)
      (* decomp cases. primitives *)    
  apply (case_tac a)
         apply (auto)
        apply (case_tac b)
               apply (auto)
        apply (erule_tac x="list" in allE)
        apply (auto)
         apply (simp add: simp_unify_rel)
        apply (simp add: type_eq_sat_def)
       apply (case_tac b)
              apply (auto)
       apply (erule_tac x="list" in allE)
       apply (auto)
        apply (simp add: simp_unify_rel)
       apply (simp add: type_eq_sat_def)
      apply (case_tac b)
             apply (auto)
      apply (erule_tac x="list" in allE)
      apply (auto)
       apply (simp add: simp_unify_rel)
      apply (simp add: type_eq_sat_def)
    (* - array case *)
     apply (case_tac b)
            apply (auto)
     apply (erule_tac x="(x5, x5a) # list" in allE)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
     apply (simp add: type_eq_sat_def)
    (* - pair case *)
    apply (case_tac b)
           apply (auto)
    apply (erule_tac x="(x61, x61a) # (x62, x62a) # list" in allE)
    apply (auto)
     apply (simp add: unify_rel_def)
     apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="list" in dist_ut_term_less_length)
     apply (simp add: tvar_total_def)
    apply (simp add: type_eq_sat_def)
    apply (case_tac "unify_type ((x61, x61a) # (x62, x62a) # list)")
     apply (auto)
    apply (simp add: uts_res_def)
    apply (simp add: perm_eq_sat_def)
    (* - fun case *)
   apply (case_tac b)
          apply (auto)
   apply (erule_tac x="(x71, x71a) # (x72, x72a) # list" in allE)
    apply (auto)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="list" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
   apply (simp add: type_eq_sat_def)
   apply (case_tac "unify_type ((x71, x71a) # (x72, x72a) # list)")
    apply (auto)
   apply (simp add: uts_res_def)
   apply (simp add: perm_eq_sat_def)
   apply (simp add: as_perm_sol_subst_aff)
    (* - chan case *)
  apply (case_tac b)
         apply (auto)
  apply (erule_tac x="(x81, x81a) # list" in allE)
  apply (auto)
   apply (simp add: unify_rel_def)
   apply (simp add: tvar_total_def)
  apply (simp add: type_eq_sat_def)
  done
    

fun as_scheme where
  "as_scheme IntTy = IntScheme"  
| "as_scheme UnitTy = UnitScheme"  
| "as_scheme BoolTy = BoolScheme"  
| "as_scheme (ArrayTy tau) = ArrayScheme (as_scheme tau)"  
| "as_scheme (PairTy t1 t2 r) = PairScheme (as_scheme t1) (as_scheme t2) (SPerm r)"  
| "as_scheme (FunTy t1 t2 r a) = FunScheme (as_scheme t1) (as_scheme t2) (SPerm r) (AffConst a)"  
| "as_scheme (ChanTy tau c_end) = ChanScheme (as_scheme tau) c_end"  
  
definition indir_sub where
  "indir_sub t_sub = (\<lambda> x. case t_sub x of None \<Rightarrow> None | Some tau \<Rightarrow> Some (as_scheme tau))"  
  
lemma cancel_perm_as_scheme: "perm_subst_type p_sub (as_scheme tau) = as_scheme tau"  
  apply (induct tau)
        apply (auto)
  done
  
lemma dir_perm_subst_type: "\<lbrakk> dir_subst_type t_sub p_sub tau tau' \<rbrakk> \<Longrightarrow>
  perm_subst_type p_sub (sol_subst_type (indir_sub t_sub) tau) = as_scheme tau'"  
  apply (induct tau arbitrary: tau')
         apply (auto)
  apply (simp add: indir_sub_def)
  apply (rule_tac cancel_perm_as_scheme)
  done

lemma dir_sol_type_eq_sat: "\<lbrakk> dir_sol_sat t_sub p_sub c_list \<rbrakk> \<Longrightarrow> type_eq_sat (indir_sub t_sub) p_sub (unify_subset c_list)"  
  apply (induct c_list)
   apply (auto)
   apply (simp add: type_eq_sat_def)
  apply (simp add: type_eq_sat_def)
  apply (case_tac a)
       apply (auto)
  apply (simp add: dir_perm_subst_type)
  done    
    
lemma dist_add_sol_subst_type: "sol_subst_type t_sub (sol_subst_type (add_env empty_env a tau) tau') =
  sol_subst_type (add_env t_sub a (sol_subst_type t_sub tau)) tau'"
  apply (induct tau')
         apply (auto)
  apply (simp add: add_env_def)
  apply (auto)
  apply (simp add: empty_env_def)
  done
  
lemma extern_sol_subst_type_eq_sat: "\<lbrakk> \<not> occurs tau a; type_eq_sat t_sub p_sub (sol_subst_eq_list (add_env empty_env a tau) c_list) \<rbrakk>
       \<Longrightarrow> type_eq_sat (add_env t_sub a (sol_subst_type t_sub tau)) p_sub ((VarScheme a, tau) # c_list)" 
  apply (simp add: type_eq_sat_def)
  apply (auto)
   apply (simp add: add_sol_subst_type)
   apply (simp add: add_env_def)
  apply (induct c_list)
   apply (auto)
  apply (simp add: dist_add_sol_subst_type)
  done
    (*
      sat 1: if type unification succeeds, and the constraint list is satisfiable, then our type substitution will be most general
      sat 2: if type unification succeeds, our type substitution will satisfy
    *)
    
lemma unify_type_satx: "\<lbrakk> unify_type c_list = Some (t_sub, p_eq); perm_eq_sat p_sub p_eq \<rbrakk> \<Longrightarrow>
  type_eq_sat t_sub p_sub c_list"
  apply (induct arbitrary: t_sub p_eq rule: wf_induct [where r=unify_rel])
   apply (simp add: unify_rel_def)
  apply (case_tac x)
   apply (auto)
   apply (simp add: type_eq_sat_def)
    (* var case *)
  apply (case_tac "\<exists> a'. a = VarScheme a'")
   apply (auto)
    (* - delete case *)
   apply (case_tac "b = VarScheme a'")
    apply (auto)
    apply (erule_tac x="list" in allE)
    apply (simp add: simp_unify_rel)
    apply (simp add: type_eq_sat_def)
    (* - occurs case *)
   apply (case_tac "occurs b a'")
    apply (auto)
    (* - elim case *)
   apply (erule_tac x="sol_subst_eq_list (add_env empty_env a' b) list" in allE)
   apply (simp add: elim_unify_rel)
   apply (case_tac "unify_type (sol_subst_eq_list (add_env empty_env a' b) list)")
    apply (auto)
   apply (rule_tac extern_sol_subst_type_eq_sat)
    apply (auto)
    (* orient case *)
  apply (case_tac "\<exists> b'. b = VarScheme b'")
   apply (auto)
   apply (erule_tac x="(VarScheme b', a) # list" in allE)
   apply (simp add: orient_unify_rel)
   apply (simp add: type_eq_sat_def)
   apply (case_tac a)
          apply (auto)
    (* decomp case *)
  apply (case_tac a)
         apply (auto)
        apply (case_tac b)
               apply (auto)
        apply (erule_tac x="list" in allE)
        apply (auto)
         apply (simp add: simp_unify_rel)
        apply (simp add: type_eq_sat_def)
       apply (case_tac b)
              apply (auto)
       apply (erule_tac x="list" in allE)
       apply (auto)
        apply (simp add: simp_unify_rel)
       apply (simp add: type_eq_sat_def)
      apply (case_tac b)
             apply (auto)
      apply (erule_tac x="list" in allE)
      apply (auto)
       apply (simp add: simp_unify_rel)
      apply (simp add: type_eq_sat_def)
    (* - array case *)
     apply (case_tac b)
            apply (auto)
     apply (erule_tac x="(x5, x5a) # list" in allE)
     apply (simp add: unify_rel_def)
     apply (simp add: tvar_total_def)
     apply (simp add: type_eq_sat_def)
    (* - pair case *)
    apply (case_tac b)
           apply (auto)
    apply (erule_tac x="(x61, x61a) # (x62, x62a) # list" in allE)
    apply (auto)
     apply (simp add: unify_rel_def)
     apply (cut_tac ?t1.0="x61" and ?t2.0="x61a" and ?s1.0="x62" and ?s2.0="x62a" and c_t="list" in dist_ut_term_less_length)
     apply (simp add: tvar_total_def)
    apply (simp add: perm_eq_sat_def)
    apply (case_tac "unify_type ((x61, x61a) # (x62, x62a) # list)")
     apply (auto)
    apply (simp add: type_eq_sat_def)
    (* - fun case *)
   apply (case_tac b)
          apply (auto)
   apply (erule_tac x="(x71, x71a) # (x72, x72a) # list" in allE)
    apply (auto)
    apply (simp add: unify_rel_def)
    apply (cut_tac ?t1.0="x71" and ?t2.0="x71a" and ?s1.0="x72" and ?s2.0="x72a" and c_t="list" in dist_ut_term_less_length)
    apply (simp add: tvar_total_def)
   apply (simp add: perm_eq_sat_def)
   apply (case_tac "unify_type ((x71, x71a) # (x72, x72a) # list)")
    apply (auto)
   apply (simp add: type_eq_sat_def)
    apply (auto)
   apply (simp add: as_perm_sol_subst_aff)
   apply (case_tac "sol_subst_aff p_sub x74")
     apply (auto)
     apply (case_tac "sol_subst_aff p_sub x74a")
       apply (auto)
    apply (case_tac "sol_subst_aff p_sub x74a")
      apply (auto)
   apply (case_tac "sol_subst_aff p_sub x74a")
     apply (auto)
    (* - chan case *)
  apply (case_tac b)
         apply (auto)
  apply (erule_tac x="(x81, x81a) # list" in allE)
  apply (auto)
   apply (simp add: unify_rel_def)
   apply (simp add: tvar_total_def)
  apply (case_tac "x82 = x82a")
   apply (auto)
  apply (simp add: type_eq_sat_def)
  done


end