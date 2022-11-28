theory ProcCVars
  imports WTLemma ResMapValid ReduceProper
begin

    (* #### we use this to define the full dominator *)
(*
fun complete_vars :: "nres_map \<Rightarrow> res_id set \<Rightarrow> res_id set" where
  "complete_vars rs_map s = { Loc x | x. \<exists> l z. Loc z \<in> s \<and> path_lookup rs_map z l x} \<union> s"  *)
  
definition dom_use_env :: "res_id set \<Rightarrow> perm_use_env"  where
  "dom_use_env s = (\<lambda> x. if x \<in> s then OwnPerm else NoPerm)"  
  
definition np_dom_use_env where
  "np_dom_use_env env delta e = dom_use_env (non_prim_vars env delta e)"  
  (*
definition full_dom_use_env where
  "full_dom_use_env env delta e = dom_use_env (complete_vars rs_map (non_prim_vars env delta e))"    *)
  
lemma strong_dom_use_env: "strong_use_env (dom_use_env s)"
  apply (simp add: strong_use_env_def)
  apply (simp add: dom_use_env_def)
  done  
  
lemma dist_dom_leq_use_env: "\<lbrakk> s \<subseteq> s' \<rbrakk> \<Longrightarrow> leq_use_env (dom_use_env s) (dom_use_env s')"    
  apply (simp add: dom_use_env_def)
  apply (simp add: leq_use_env_def)
  apply (auto)
  done
    (*
lemma full_dom_leq_use_env: "leq_use_env (np_dom_use_env env e) (full_dom_use_env env rs_map e)"    
  apply (simp add: np_dom_use_env_def)
  apply (simp add: full_dom_use_env_def)
  apply (rule_tac dist_dom_leq_use_env)
  apply (auto)
  done*)
  
lemma wt_np_leq_use_env: "\<lbrakk> well_typed env delta r_s1 e tau r_s2 rx; is_own r \<rbrakk> \<Longrightarrow> leq_use_env (np_dom_use_env env delta e) (lift_use_env r_s1 r)"    
  apply (simp add: leq_use_env_def)
  apply (simp add: np_dom_use_env_def)
  apply (simp add: dom_use_env_def)
  apply (auto)
  apply (simp add: is_own_def)
  apply (case_tac "r_s1 x = NoPerm")
   apply (cut_tac env="env" and ?r_s1.0="r_s1" and e="e" and x="x" in well_typed_no_npv_use)
     apply (auto)
  done
 
end