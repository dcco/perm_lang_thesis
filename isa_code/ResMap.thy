theory ResMap
  imports WellTypedExp GenSubEnv
begin

    (* ## NEW RES MAP DEFINITION ## *)

type_synonym nres_map = "string \<Rightarrow> perm_use_env option"   
    
definition full_nres_map :: "'a state_env \<Rightarrow> nres_map \<Rightarrow> bool" where
  "full_nres_map s s_map = (\<forall> x. (s x = None) = (s_map x = None))"  
  
definition nres_lookup where
  "nres_lookup rs_map x = (case rs_map x of
    None \<Rightarrow> empty_use_env
    | Some r_s \<Rightarrow> r_s
  )"  
  
lemma nres_add_same: "nres_lookup (add_env rs_map x r_s) x = r_s"       
  apply (simp add: nres_lookup_def)
  apply (simp add: add_env_def)
  done

lemma nres_add_diff: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> nres_lookup (add_env rs_map x r_s) y = nres_lookup rs_map y"       
  apply (simp add: nres_lookup_def)
  apply (simp add: add_env_def)
  done    
    
lemma nres_rem_same: "nres_lookup (rem_env rs_map x) x = empty_use_env"    
  apply (simp add: nres_lookup_def)
  apply (simp add: rem_env_def)
  done    
    
lemma nres_rem_diff: "\<lbrakk> x \<noteq> y \<rbrakk> \<Longrightarrow> nres_lookup (rem_env rs_map x) y = nres_lookup rs_map y"
  apply (simp add: nres_lookup_def)
  apply (simp add: rem_env_def)
  done       
    
lemma add_full_nres_map: "\<lbrakk> full_nres_map s rs_map \<rbrakk> \<Longrightarrow> full_nres_map (add_env s x v) (add_env rs_map x r_s)"
  apply (simp add: add_env_def)
  apply (simp add: full_nres_map_def)
  done
  
definition sub_nres_map :: "'a state_env \<Rightarrow> nres_map \<Rightarrow> bool" where
  "sub_nres_map s s_map = (\<forall> x. sub_use_env s (nres_lookup s_map x))"       
  
lemma add_sub_nres_map2: "\<lbrakk> sub_nres_map s rs_map; s x = None \<rbrakk> \<Longrightarrow> sub_nres_map (add_env s x v) rs_map "    
  apply (simp add: sub_nres_map_def)
  apply (auto)
  apply (erule_tac x="xa" in allE)
  apply (rule_tac s="s" in contain_sub_use_env)
   apply (simp)
  apply (rule_tac add_contain_env)
  apply (simp)
  done
  
lemma add_sub_nres_map1: "\<lbrakk> sub_nres_map s rs_map; sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_nres_map s (add_env rs_map x r_s) "    
  apply (simp add: sub_nres_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_diff)
   apply (auto)
  done
 
lemma dist_add_sub_nres_map: "\<lbrakk> sub_nres_map s rs_map; sub_use_env s r_s \<rbrakk> \<Longrightarrow> sub_nres_map (add_env s x v) (add_env rs_map x r_s) "       
  apply (simp add: sub_nres_map_def)
  apply (auto)
  apply (case_tac "x = xa")
   apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_same)
   apply (auto)
   apply (rule_tac add_sub_use_env)
   apply (simp)
  apply (cut_tac rs_map="rs_map" and x="x" and r_s="r_s" in nres_add_diff)
   apply (auto)
  apply (rule_tac add_sub_use_env)
  apply (simp)
  done
    
end