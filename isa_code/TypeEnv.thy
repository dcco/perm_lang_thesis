theory TypeEnv
  imports PermEnv GenEnv
begin

    (* 
      ####################################
        P2. type definitions
      ####################################
    *)

datatype p_aff = Aff | Ref | Prim
  
datatype c_end = SEnd | REnd  
  
datatype p_type =
   IntTy | UnitTy | BoolTy
  | ArrayTy p_type  
  | PairTy p_type p_type p_perm
  | FunTy p_type p_type p_perm p_aff
  | ChanTy p_type c_end

fun as_perm where
  "as_perm Aff = OwnPerm"
| "as_perm Ref = UsePerm"
| "as_perm Prim = NoPerm"
  
type_synonym pt_env = "p_type res_env" 
  
end