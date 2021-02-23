(**************************************************************************)
(*                                                                        *)
(*  Copyright (c) 2021 OCamlPro & Origin Labs                             *)
(*                                                                        *)
(*  All rights reserved.                                                  *)
(*  This file is distributed under the terms of the GNU Lesser General    *)
(*  Public License version 2.1, with the special exception on linking     *)
(*  described in the LICENSE.md file in the root directory.               *)
(*                                                                        *)
(*                                                                        *)
(**************************************************************************)

open Solidity_common
open Solidity_ast

let error loc fmt =
  Format.kasprintf (fun s -> raise (TypecheckError (s, loc))) fmt

type env = {
  mutable ident_map : ((ident_desc * bool) list) IdentMap.t;
  upper_env : env option; (* i.e module/contract/fonction *)
}

and ident_desc =
  (* | Module of module_desc *)
  | Contract of contract_desc
  | Type of type_desc
  | Variable of variable_desc
  | Modifier of modifier_desc
  | Function of function_desc
  (* | Event (\* TODO *\) *)
(* see how to deal with using for *)

(* This is just a container for things imported using the import directive *)
(* Can be imported : types, contract, libraries AND MODULES (top-level stuff) *)
(* and module_desc = {
 *   module_type_name : user_defined_type_name;
 *   module_env : env;
 * } *)

and type_desc =
  | TDEnum of enum_desc
  | TDStruct of struct_desc

and enum_desc = {
  enum_abs_name : absolute LongIdent.t;
  enum_values : (Ident.t * int) list;
}

and struct_desc = {
  struct_abs_name : absolute LongIdent.t;
  mutable struct_fields : (Ident.t * type_) list; (* Note: order is important *)
  mutable has_mapping : bool;
  struct_env : env; (* Note: needed to qualify types *)
  struct_def : Ident.t * field_definition list;
}

and contract_desc = {
  contract_abs_name : absolute LongIdent.t;
  contract_env : env;
  contract_def : contract_definition;
  mutable contract_hierarchy : (absolute LongIdent.t * contract_desc) list;
    (* Note: the most derived first, including itself *)
}

and variable_desc = {
  variable_abs_name : absolute LongIdent.t;
  variable_type : type_;
  variable_visibility : visibility;
  variable_mutability : var_mutability;
  variable_local : bool;
  variable_init : expression option;
  variable_override : absolute LongIdent.t list option;
  variable_getter : function_desc option; (* when the variable has a getter *)
}

and function_desc = {
  function_abs_name : absolute LongIdent.t;
  function_params : (type_ * Ident.t option) list;
  function_returns : (type_ * Ident.t option) list;
  function_returns_lvalue : bool;
  function_visibility : visibility;
  function_mutability : fun_mutability;
  function_def : function_definition option; (* REMOVE ? change to body ? *)
  function_override : absolute LongIdent.t list option;
  function_selector : string option;
}

and modifier_desc = {
  modifier_abs_name : absolute LongIdent.t;
  modifier_params : (type_ * Ident.t option) list;
  modifier_def : modifier_definition; (* REMOVE ? change to body ?  *)
  (* Note: Modifiers have no visibility nor mutability *)
}

and fun_kind =
  | KOther
  | KNewContract
  | KExtContractFun

and function_options = {
  kind : fun_kind;
  value : bool;
  gas : bool;
  salt : bool;
}

and location =
  | LMemory
  | LStorage of bool (* false = ref, true = pointer *)
  | LCalldata (* is always a reference *)

and magic_type =
  | TMsg (* type of the 'msg' object *)
  | TBlock (* type of the 'block' object *)
  | TTx (* type of the 'tx' object *)
  | TAbi (* type of the 'abi' object *)
  | TMetaType of type_ (* result of type(X) *)
  (* TON-specific *)
  | TTvm
  | TMath
  | TRnd

and type_ =
  | TBool
  | TInt of int option (* None = int, Some (N) = intN *)
  | TUint of int option (* None = uint, Some (N) = uintN *)
  | TFixed of int option * int (* None, N = fixed*xN, Some (M), N = fixedMxN *)
  | TUfixed of int option * int (* None, N = ufixed*xN, Some (M),N = ufixedMxN *)
  | TAddress of bool (* false = address, true = address payable *)
  | TFixBytes of int
  | TBytes of location
  | TString of location
  | TEnum of absolute LongIdent.t * enum_desc
  | TStruct of absolute LongIdent.t * struct_desc * location
  | TContract of absolute LongIdent.t * contract_desc * bool (* super *)
  | TArray of type_ * Z.t option * location
  | TMapping of type_ * type_ * location (* storage ref or storage pointer *)
  | TFunction of function_desc * function_options
  (* TON-specific *)
  | TTvmCell
  | TTvmSlice
  | TTvmBuilder
  | TExtraCurrencyCollection
  | TOptional of type_

  (* Internal use only *)
  | TModifier of modifier_desc
  | TTuple of type_ option list
  | TArraySlice of type_ * location (* is never an lvalue *)
  | TType of type_ (* a type is an expression of type 'type' *)
  | TMagic of magic_type
  | TRationalConst of Q.t * int option (* Some _ = size in bytes (if hex) *)
  | TLiteralString of string

(* source_unit (Import) *)
type annot += AImport of Ident.t

(* expression, statement, ident/field (incl. contract) *)
type annot += AType of type_

(* source_unit (ContractDefinition), inheritance_specifier *)
type annot += AContract of contract_desc

(* contract_part (FunctionDefinition), constructor invocation, ident/field (functions AND getters) *)
type annot += AFunction of function_desc

(* contract_part (ModifierDefinition), ident/field *)
type annot += AModifier of modifier_desc

(* contract_part (StateVariableDeclaration), ident/field *)
type annot += AVariable of variable_desc

(* ident/field *)
type annot += APrimitive (* id ? *)

let new_env ?upper_env () =
  { ident_map = IdentMap.empty; upper_env }

let new_fun_options = {
  kind = KOther;
  value = false;
  gas = false;
  salt = false
}

let primitive_type ?(kind=KOther) ?(returns_lvalue=false)
    arg_types ret_types function_mutability =
  let fd = {
    function_abs_name = LongIdent.empty;
    function_params = List.map (fun t -> (t, None)) arg_types;
    function_returns = List.map (fun t -> (t, None)) ret_types;
    function_returns_lvalue = returns_lvalue;
    function_visibility = VPublic; (* TODO: private if builtin... *)
    function_mutability;
    function_def = None;
    function_override = None;
    function_selector = None; }
  in
  TFunction (fd, { new_fun_options with kind })

let is_loc_storage = function
  | LMemory -> false
  | LStorage _b -> true
  | LCalldata -> false

let is_loc_storage_ptr = function
  | LMemory -> false
  | LStorage b -> b
  | LCalldata -> false

let is_tuple = function
  | TTuple _ -> true
  | _ -> false

let same_fun_options fo1 fo2 =
  fo1.value = fo2.value &&
  fo1.gas = fo2.gas &&
  fo1.salt = fo2.salt

let same_location l1 l2 =
  match l1, l2 with
  | LMemory, LMemory -> true
  | LStorage (ptr1), LStorage (ptr2) -> ptr1 = ptr2
  | LCalldata, LCalldata -> true
  | _ -> false

let rec same_type ?(ignore_loc=false) t1 t2 =
  match t1, t2 with
  | TBool, TBool ->
      true
  | TInt (None), TInt (None) ->
      true
  | TInt (Some sz1), TInt (Some sz2) ->
      (sz1 = sz2)
  | TUint (None), TUint (None) ->
      true
  | TUint (Some sz1), TUint (Some sz2) ->
      (sz1 = sz2)
  | TFixed (None, dec1), TFixed (None, dec2) ->
      (dec1 = dec2)
  | TFixed (Some sz1, dec1), TFixed (Some sz2, dec2) ->
      (sz1 = sz2) &&
      (dec1 = dec2)
  | TUfixed (None, dec1), TUfixed (None, dec2) ->
      (dec1 = dec2)
  | TUfixed (Some sz1, dec1), TUfixed (Some sz2, dec2) ->
      (sz1 = sz2) &&
      (dec1 = dec2)
  | TAddress (payable1), TAddress (payable2) ->
      payable1 = payable2
  | TFixBytes (sz1), TFixBytes (sz2) ->
      (sz1 = sz2)
  | TBytes (loc1), TBytes (loc2) ->
      ignore_loc || same_location loc1 loc2
  | TString (loc1), TString (loc2) ->
      ignore_loc || same_location loc1 loc2
  | TEnum (lid1, _ed1), TEnum (lid2, _ed2) ->
      LongIdent.equal lid1 lid2
  | TStruct (lid1, _ed1, loc1), TStruct (lid2, _ed2, loc2) ->
      LongIdent.equal lid1 lid2 &&
      (ignore_loc || same_location loc1 loc2)
  | TContract (lid1, _ed1, super1), TContract (lid2, _ed2, super2) ->
      LongIdent.equal lid1 lid2 && super1 = super2
  | TArray (t1, None, loc1), TArray (t2, None, loc2) ->
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TArray (t1, Some sz1, loc1), TArray (t2, Some sz2, loc2) ->
      Z.equal sz1 sz2 &&
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TMapping (src1, dst1, loc1), TMapping (src2, dst2, loc2) ->
      same_type ~ignore_loc src1 src2 &&
      same_type ~ignore_loc dst1 dst2 &&
      (ignore_loc || same_location loc1 loc2)
(* TODO: be more accurate *)
(* TODO: options ? *)
  | TFunction (fd1, fo1),
    TFunction (fd2, fo2) ->
      same_type_pl ~ignore_loc fd1.function_params fd2.function_params &&
      same_type_pl ~ignore_loc fd1.function_returns fd2.function_returns &&
      same_mutability fd1.function_mutability fd2.function_mutability &&
(* TODO: only external counts (use kind instead) *)
      same_visibility fd1.function_visibility fd2.function_visibility &&
      same_fun_options fo1 fo2
  | TModifier md1, TModifier md2 ->
      same_type_pl ~ignore_loc md1.modifier_params md2.modifier_params
  | TArraySlice (t1, loc1), TArraySlice (t2, loc2) ->
      same_type ~ignore_loc t1 t2 &&
      (ignore_loc || same_location loc1 loc2)
  | TType t1, TType t2 ->
      same_type ~ignore_loc t1 t2
  | TMagic mt1, TMagic mt2 ->
      same_magic_type ~ignore_loc mt1 mt2
  | TRationalConst (q1, sz_opt1), TRationalConst (q2, sz_opt2) ->
      Q.equal q1 q2 &&
      (match sz_opt1, sz_opt2 with
       | Some sz1, Some sz2 -> (sz1 = sz2)
       | _ -> false)
  | TLiteralString s1, TLiteralString s2 ->
      String.equal s1 s2
  | TTuple tl1, TTuple tl2 ->
      same_type_ol ~ignore_loc tl1 tl2
  (* TON-specific *)
  | TTvmCell, TTvmCell ->
      true
  | TTvmSlice, TTvmSlice ->
      true
  | TTvmBuilder, TTvmBuilder ->
      true
  | TExtraCurrencyCollection, TExtraCurrencyCollection ->
      true
  | TOptional (t1), TOptional (t2) ->
      same_type ~ignore_loc t1 t2
  | _ ->
      false

and same_magic_type ?(ignore_loc=false) t1 t2 =
  match t1, t2 with
  | TMsg, TMsg ->
      true
  | TBlock, TBlock ->
      true
  | TTx, TTx ->
      true
  | TAbi, TAbi ->
      true
  | TMetaType (t1), TMetaType (t2) ->
      same_type ~ignore_loc t1 t2
  (* TON-specific *)
  | TTvm, TTvm ->
      true
  | TMath, TMath ->
      true
  | TRnd, TRnd ->
      true
  | _ ->
      false

and same_type_ol ?(ignore_loc=false) tl1 tl2 =
  (List.length tl1 = List.length tl2) &&
  List.for_all2 (fun t1_opt t2_opt ->
      match t1_opt, t2_opt with
      | Some t1, Some t2 -> same_type ~ignore_loc t1 t2
      | Some _, None | None, Some _ -> false
      | None, None -> true) tl1 tl2

and same_type_pl ?(ignore_loc=false) tl1 tl2 =
  (List.length tl1 = List.length tl2) &&
  List.for_all2 (fun (t1, _) (t2, _) -> same_type ~ignore_loc t1 t2) tl1 tl2

and same_type_l ?(ignore_loc=false) tl1 tl2 =
  (List.length tl1 = List.length tl2) &&
  List.for_all2 (same_type ~ignore_loc) tl1 tl2

let same_signature fd1 fd2 =
  if not (ExtList.same_lengths fd1.function_params fd2.function_params) then
    false
  else
    List.for_all2 (fun (t1, _) (t2, _) -> same_type t1 t2)
      fd1.function_params fd2.function_params

let rec has_mapping = function
  | TBool | TInt _ | TUint _ | TFixed _ | TUfixed _
  | TAddress _ | TFixBytes _ | TBytes _ | TString _ | TEnum _
  | TContract _ | TFunction _ | TModifier _ | TMagic _ | TType _
  | TRationalConst _ | TLiteralString _ ->
      false
  | TMapping _ ->
      true
  | TArray (t, _, _)
  | TArraySlice (t, _) ->
      has_mapping t
  | TStruct (_, s, _) ->
      s.has_mapping
  | TTuple (tl) ->
      List.exists (function
          | None -> false
          | Some (t) -> has_mapping t
        ) tl
  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      false
  | TOptional (t) ->
      has_mapping t

let rec is_storage_type = function
  | TBytes (LStorage _) | TString (LStorage _)
  | TStruct (_, _, LStorage _)
  | TArray (_, _, LStorage _)
  | TArraySlice (_, LStorage _)
  | TMapping (_, _, LStorage _) ->
      true
  | TBool | TInt _ | TUint _ | TFixed _ | TUfixed _
  | TAddress _ | TFixBytes _ | TEnum _ | TContract _
  | TFunction _ | TModifier _ | TMagic _ | TType _
  | TRationalConst _ | TLiteralString _
  | TBytes _ | TString _ | TStruct _
  | TArray _ | TArraySlice _ ->
      false
  | TTuple (tl) ->
      List.exists (function
          | None -> false
          | Some (t) -> is_storage_type t
        ) tl
  | TMapping (_, _, (LMemory | LCalldata)) ->
      failwith "Mapping can not have memory/calldata location"
  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      false
  | TOptional (t) ->
      is_storage_type t




type lookup_kind =
  | LAny
  | LInternal
  | LExternal
  | LStatic of contract_kind * bool (* true = contract is a parent *)
  | LSuper

let is_externally_visible = function
  | VExternal | VPublic -> true
  | VInternal | VPrivate -> false

let is_internally_visible = function
  | VPublic | VInternal | VPrivate -> true
  | VExternal -> false

let is_statically_visible ~library = function
  | VPublic | VInternal -> true
  | VExternal -> library
  | VPrivate -> false

(* variables and functions only *)
let is_visible lookup visibility ~inherited ~variable =
  match lookup with
  | LAny ->
      true
  | LExternal ->
      is_externally_visible visibility
  | LInternal -> (* Note: privates are only those defined by the contract *)
      is_internally_visible visibility
  | LStatic (Interface, _) ->
      false
  | LStatic (Contract, false) ->
      false
  | LStatic (Contract, true) ->
      is_statically_visible visibility ~library:false && not inherited
  | LStatic (Library, false) ->
      is_statically_visible visibility ~library:true
  | LStatic (Library, true) -> (* i.e. call from the library itself *)
      is_internal visibility ||
      variable && is_public visibility
  | LSuper ->
      is_statically_visible visibility ~library:false && not variable

let filter_by_visibility lookup idl =
  List.filter (fun id ->
      match id, lookup with
      | _, LAny ->
          true
      | (Contract _, _), LInternal ->
          true
      | (Contract _, _), (LExternal | LStatic (_) | LSuper) ->
          false
      | (Type _, _), (LInternal | LStatic ((Library | Interface), _)) ->
          true
      | (Type _, _), (LExternal | LSuper) ->
          false
      | (Type _, inherited), LStatic (Contract, _) ->
          not inherited
      | (Modifier _, _), LInternal ->
          true
      | (Modifier _, _), (LExternal | LStatic (_) | LSuper) ->
          false
      | (Variable { variable_visibility; _ }, inherited), _ ->
          (* TODO: return as function when external ? *)
          is_visible lookup variable_visibility ~inherited ~variable:true
      | (Function ({ function_visibility; _ }), inherited), _ ->
          is_visible lookup function_visibility ~inherited ~variable:false
    ) idl

let rec lookup_ident
    (env : env) ~(upper : bool) ~(lookup : lookup_kind)
    (ident : Ident.t) : ident_desc list =
  let idl =
    filter_by_visibility lookup (
        Option.value ~default:[] (IdentMap.find_opt ident env.ident_map))
  in
  match idl with
  | [] ->
      begin
        match upper, env.upper_env with
        | true, Some env -> lookup_ident env ~upper ~lookup ident
        | _ -> []
      end
  | _ -> List.map fst idl

let rec lookup_lident
    (loc : loc) (env : env) ~(upper : bool) ~(lookup : lookup_kind)
    (lident : relative LongIdent.t) : ident_desc list =
  match LongIdent.to_ident_list lident with
  | [] -> assert false
  | [ident] -> lookup_ident env ~upper ~lookup ident
  | ident :: lident ->
      match lookup_ident env ~upper ~lookup:LAny ident with
      | [] -> []
      | [Contract c] ->
          lookup_lident loc c.contract_env ~upper:false ~lookup
            (LongIdent.of_ident_list_rel lident)
      | _ ->
(* TODO: just None ? *)
          error loc "Member %s not found or not visible after \
                     argument-dependent lookup in %s"
            (Ident.to_string (List.hd lident)) (Ident.to_string ident)
(* TODO: find_lident no longer needed in typecheck // error irrelevant *)

let find_ident env ~lookup ident =
  lookup_ident env ~upper:true ~lookup ident

let find_lident loc env ~lookup lident =
  lookup_lident loc env ~upper:true ~lookup lident

let find_type loc env lident =
  match lookup_lident loc env ~upper:true ~lookup:LAny lident with
  | [Type (TDEnum (ed))] ->
      Some (TEnum (ed.enum_abs_name, ed))
  | [Type (TDStruct (sd))] ->
      Some (TStruct (sd.struct_abs_name, sd, LStorage (true)))
  | [Contract (cd)] ->
      Some (TContract (cd.contract_abs_name, cd, false (* super *)))
  | _ -> None

let find_contract loc env lident =
  match lookup_lident loc env ~upper:true ~lookup:LAny lident with
  | [Contract (cd)] -> Some (cd)
  | _ -> None




let ensure_undefined loc env ident =
  if IdentMap.mem ident env.ident_map then
    error loc "Identifier %s already declared" (Ident.to_string ident);
  if String.equal (Ident.to_string ident) "default" then
    error loc "Identifier \"default\" is reserved"


let replace_idents loc env ident descl =
  if String.equal (Ident.to_string ident) "default" then
    error loc "Identifier \"default\" is reserved";
  env.ident_map <- IdentMap.add ident descl env.ident_map

let add_unique_ident loc env ident desc =
  ensure_undefined loc env ident;
  env.ident_map <- IdentMap.add ident [desc] env.ident_map

let add_type loc env ~inherited type_name type_desc =
  add_unique_ident loc env type_name (Type (type_desc), inherited)

let add_contract loc env contract_name contract_desc =
  add_unique_ident loc env contract_name (Contract (contract_desc), false)

let add_enum loc env ~inherited enum_abs_name enum_name values =
  let values, _ =
    List.fold_left (fun (enum_values, i) enum_value ->
        IdentAList.add_uniq enum_value i enum_values, (i+1)
      ) ([], 0) values
  in
  let enum_desc = { enum_abs_name; enum_values = List.rev values } in
  add_type loc env ~inherited enum_name (TDEnum enum_desc)

let add_struct loc env ~inherited struct_abs_name struct_name struct_def =
  let struct_desc = {
    struct_abs_name; struct_fields = []; has_mapping = false;
    struct_def; struct_env = env }
  in
  add_type loc env ~inherited struct_name (TDStruct struct_desc)

let add_struct_fields struct_desc fields =
  let fields =
    List.fold_left (fun fields (field_name, field_type) ->
        struct_desc.has_mapping <-
          struct_desc.has_mapping || has_mapping field_type;
        IdentAList.add_uniq field_name field_type fields
      ) [] fields
  in
  struct_desc.struct_fields <- IdentAList.rev fields

let add_nonpublic_variable loc env ~inherited variable_name variable_desc =
(*  add_unique_ident loc env variable_name (Variable (variable_desc), inherited)
*)
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt variable_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error loc "Can not add an inherited variable \
                     over an non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error loc "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd)
          when not inh || not (is_external fd.function_visibility) ->
            (* Note: multiple definition in the same contract *)
            error loc "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd) ->
            (Function (fd), inh) :: iddl
      ) [] iddl
  in
  replace_idents loc env variable_name
    (List.rev ((Variable (variable_desc), inherited) :: iddl_rev))

let add_public_variable loc env ~inherited variable_name variable_desc =
  let function_desc =
    match variable_desc.variable_getter with
    | None -> error loc "Public state variable without getter !"
    | Some (fd) -> fd
  in
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt variable_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error loc "Can not add an inherited variable \
                     over an non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error loc "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error loc "Identifier %s already declared"
              (Ident.to_string variable_name)
        | Function (fd) when not (same_signature fd function_desc) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Function (fd), inh) :: iddl
        | Function (fd) (* when inh *) ->
            (* Note: override because previous function is inherited *)
            begin
              match fd.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if not fd.fun_virtual then
                    error loc "Trying to override non-virtual function"
            end;
            if is_none variable_desc.variable_override then
              error loc "Overriding public state variable \
                         is missing \"override\" specifier";
            if not (is_external fd.function_visibility) then
              error loc "Public state variables can only override \
                         functions with external visibility";
            if not (convertible_mutability
                      ~from:fd.function_mutability
                      ~to_:function_desc.function_mutability) then
              error loc "Overriding public state variable changes \
                         state mutability from \"%s\" to \"%s\""
                (Solidity_printer.string_of_fun_mutability
                   fd.function_mutability)
                (Solidity_printer.string_of_fun_mutability
                   function_desc.function_mutability);
            iddl
      ) [] iddl
  in
  replace_idents loc env variable_name
    (List.rev ((Variable (variable_desc), inherited) :: iddl_rev))

let add_variable loc env ~inherited variable_name variable_desc =
  match variable_desc.variable_visibility with
  | VPublic ->
      add_public_variable loc env ~inherited variable_name variable_desc
  | _ ->
      add_nonpublic_variable loc env ~inherited variable_name variable_desc

let add_function loc env ~inherited function_name function_desc =
  let iddl =
    Option.value ~default:[] (IdentMap.find_opt function_name env.ident_map) in
  let iddl_rev =
    List.fold_left (fun iddl (id, inh) ->
        if inherited && not inh then
          error loc "Can not add an inherited function \
                     over an non-inherited symbol !";
        match id with
        | Modifier _ | Variable _ | Type _ | Contract _ ->
            error loc "Identifier %s already declared"
              (Ident.to_string function_name)
        | Function (fd) when not (same_signature fd function_desc) ->
            (* Note: overload (hierachy-wise), because signature is different *)
            (Function (fd), inh) :: iddl
        | Function (_fd) when not inh ->
            (* Note: multiple definition in the same contract *)
            error loc "Function with same name and arguments defined twice"
        | Function (fd) (* when inh *) ->
            (* Note: override because previous function is inherited *)
            begin
              match fd.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if not fd.fun_virtual then
                    error loc "Trying to override non-virtual function"
            end;
            begin
              match function_desc.function_def with
              | None -> () (* error ? *)
              | Some (fd) ->
                  if is_none fd.fun_override && not inh then
                    error loc "Overriding function is missing \
                               \"override\" specifier"
            end;
            if not (convertible_visibility
                      ~from:fd.function_visibility
                      ~to_:function_desc.function_visibility) then
              error loc "Overriding function visibility differs";
            if not (convertible_mutability
                      ~from:fd.function_mutability
                      ~to_:function_desc.function_mutability) then
              error loc "Overriding function changes state \
                         mutability from \"%s\" to \"%s\""
                (Solidity_printer.string_of_fun_mutability
                   fd.function_mutability)
                (Solidity_printer.string_of_fun_mutability
                   function_desc.function_mutability);
            iddl
      ) [] iddl
  in
  replace_idents loc env function_name
    (List.rev ((Function (function_desc), inherited) :: iddl_rev))

let add_modifier loc env ~inherited modifier_name modifier_desc =
  begin
    match IdentMap.find_opt modifier_name env.ident_map with
    | None ->
        ()
    | Some (idl) ->
        if List.exists (fun (id, inh) ->
            match id with
            | Modifier (_md) -> not inh
            | Function _ | Variable _ | Type _ | Contract _ -> true) idl
        then
          error loc "Identifier %s already declared"
            (Ident.to_string modifier_name)
  end;
  (* add_unique_ident loc env modifier_name
   *   (Modifier (modifier_desc), inherited) *)
  replace_idents loc env modifier_name
    [(Modifier (modifier_desc), inherited)]

let add_parent_definitions loc ~preprocess c =
  List.iter (fun (_lid, cd) ->
      IdentMap.iter (fun id idl ->
          List.iter (fun (id_desc, inh) ->
              if not inh then
                match id_desc, preprocess with
                | Type (td), true ->
                    add_type loc c.contract_env ~inherited:true id td
                | Variable (vd), false ->
                    if is_inheritable vd.variable_visibility then
                      add_variable loc c.contract_env ~inherited:true id vd
                    else
                      ensure_undefined loc c.contract_env id
                | Modifier (md), false ->
                    add_modifier loc c.contract_env ~inherited:true id md
                | Function (_fd), false when Ident.equal id Ident.constructor ->
                    ()
                | Function (fd), false ->
                    (* TODO: overriding function should have same visibility *)
                    if is_inheritable fd.function_visibility then
                      add_function loc c.contract_env
                        ~inherited:true id fd
                | _ ->
                    ()
            ) idl
        ) cd.contract_env.ident_map
    ) (List.rev (List.tl (c.contract_hierarchy)))



let has_abstract_function c =
  let exception Found of Ident.t in
  try
    IdentMap.iter (fun id idl ->
        List.iter (fun (id_desc, _inh) ->
            match id_desc with
            | Function { function_def = Some { fun_body = None; _ }; _ } ->
                raise (Found (id))
            | _ ->
                ()
          ) idl
      ) c.contract_env.ident_map;
    None
  with Found (id) ->
    Some (id)




let string_of_location = function
  | LMemory -> "memory"
  | LStorage (false) -> "storage ref"
  | LStorage (true) -> "storage pointer"
  | LCalldata -> "calldata"

let rec string_of_type = function
  | TBool ->
      "bool"
  | TInt (None) ->
      "int"
  | TInt (Some sz)->
      Format.sprintf "int%d" sz
  | TUint (None) ->
      "uint"
  | TUint (Some sz)->
      Format.sprintf "uint%d" sz
  | TFixed (None, dec) ->
      Format.sprintf "fixed%d" dec
  | TFixed (Some sz, dec) ->
      Format.sprintf "fixed%dx%d" sz dec
  | TUfixed (None, dec) ->
      Format.sprintf "ufixed%d" dec
  | TUfixed (Some sz, dec) ->
      Format.sprintf "ufixed%dx%d" sz dec
  | TAddress (false) ->
      "address"
  | TAddress (true) ->
      "address payable"
  | TFixBytes (sz) ->
      Format.sprintf "bytes%d" sz
  | TBytes (loc) ->
      Format.sprintf "bytes %s" (string_of_location loc)
  | TString (loc) ->
      Format.sprintf "string %s" (string_of_location loc)
  | TStruct (lid, _, loc) ->
      Format.sprintf "struct %s %s"
        (LongIdent.to_string lid) (string_of_location loc)
  | TEnum (lid, _) ->
      Format.sprintf "enum %s" (LongIdent.to_string lid)
  | TContract (lid, _, super) ->
      if super then
        Format.sprintf "contract super %s" (LongIdent.to_string lid)
      else
        Format.sprintf "contract %s" (LongIdent.to_string lid)
  | TArray (t, sz_opt, loc) ->
      Format.sprintf "%s[%s] %s"
        (string_of_type t)
        (match sz_opt with
         | None -> ""
         | Some i -> Z.to_string i)
        (string_of_location loc)
  | TMapping (tk, tv, _loc) -> (* Note: loc is only LStorage*)
      Format.sprintf "mapping (%s => %s)"
        (string_of_type tk) (string_of_type tv)
  | TFunction (fd, _fo) ->
      string_of_function_desc fd
  | TModifier (md) ->
      string_of_modifier_desc md
  | TArraySlice (t, loc) ->
      Format.sprintf "%s[] %s" (string_of_type t) (string_of_location loc)
  | TType (t) ->
      Format.sprintf "type %S" (string_of_type t)
  | TMagic mt ->
      string_of_magic_type mt
  | TRationalConst (q, _) when ExtQ.is_int q ->
      Format.sprintf "int_const %s" (Q.to_string q)
  | TRationalConst (q, _) ->
      Format.sprintf "rational_const %s" (Q.to_string q)
  | TLiteralString (s) ->
      Format.sprintf "literal_string (%s)" s
  | TTuple (tl) ->
      Format.sprintf "(%s)"
        (String.concat ", " (List.map (function
             | Some t -> string_of_type t
             | None -> "") tl))
  (* TON-specific *)
  | TTvmCell ->
      "TvmCell"
  | TTvmSlice ->
      "TvmSlice"
  | TTvmBuilder ->
      "TvmBuilder"
  | TExtraCurrencyCollection ->
      "ExtraCurrencyCollection"
  | TOptional (t) ->
      Format.sprintf "option(%s)" (string_of_type t)

and string_of_magic_type = function
  | TMsg ->
      "msg"
  | TBlock ->
      "block"
  | TTx ->
      "tx"
  | TAbi ->
      "msg"
  | TMetaType (t) ->
      Format.sprintf "type %S" (string_of_type t)
  (* TON-specific *)
  | TTvm ->
      "tvm"
  | TMath ->
      "math"
  | TRnd ->
      "rnd"

and string_of_function_desc fd =
  Format.sprintf "function(%s) %s%s %s"
    (string_of_param_list fd.function_params)
    (match fd.function_returns with
     | [] -> ""
     | rtl -> string_of_param_list rtl ^ " ")
    (Solidity_printer.string_of_fun_mutability fd.function_mutability)
    (match fd.function_visibility with
     | VExternal -> "external"
     | _ -> "")

and string_of_modifier_desc md =
  Format.sprintf "modifier(%s)"
    (string_of_param_list md.modifier_params)

and string_of_param_list pl =
  String.concat "," (List.map (fun (t, _) -> string_of_type t) pl)

and string_of_type_list t =
  String.concat "," (List.map string_of_type t)







(* String literals are valid strings if they only contain
   printable or whitespace 7-bit ASCII characters *)
(* Note: in Solidity, strings are UTF-8, not ASCII *)
let valid_string s =
  let valid = ref true in
  String.iter (fun c ->
      let c = Char.code c in
      valid := !valid &&
               (0x20 <= c && c <= 0x7E || (* printable characters *)
                0x09 <= c && c <= 0x0D) (* whitespace characters *)
    ) s;
  !valid

(* TODO: improve rules according to solc (Types.cpp:1600) *)
let convertible_location ~from ~to_ =
  match from, to_ with
  | LCalldata, LCalldata -> true
  | _, (LMemory | LStorage (false)) -> true
  | LStorage _, _ -> true
  | _ -> false (* TODO : calldata ? *)

(* Returns the number of bits took by the decimals of a fixed *)
let decimals_space (decimals : int) =
  let max : Z.t = Z.pow (Z.of_int 10) decimals in
  let rec loop (cpt : int) (two_to_cpt : Z.t) =
    if (>=) ((Z.compare (Z.min two_to_cpt Z.one)) max) 0 then
      cpt
    else
      loop (cpt + 1) (Z.shift_left two_to_cpt 1)
  in loop 0 Z.one

(* Returns the size (in bits) of the integer part of a fixed
   encoded in 'size' bits with 'dec' decimals (type float'size'x'dec') *)
let integer_part_size (size : int) (dec : int) =
  size - (decimals_space dec)

(* Check whether implicit conversion can occur between two types *)

(* TODO: contract casts with base/derived contract *)
(* TODO: location is a bit more subtle *)
(* TODO: missing contract cast ? *)
let rec implicitly_convertible ?(ignore_loc=false) ~from ~to_ () =
  match from, to_ with

  (* Integers <= Unbounded signed integers *)
  | (TUint _ | TInt _), TInt None -> true

  (* Unsigned integers <= unbounded signed integers *)
  | TUint (Some _), TUint None -> true

  (* Sized integers <= Bigger signed integers *)
  | TUint (Some size), (TInt (Some size') | TUint (Some size'))
  | TInt (Some size), TInt (Some size') ->
      (size <= size')

  (* integers <= Unbounded Fixed *)
  | (TInt _ | TUint _), TFixed (None, _)
  | TUint _, TUfixed (None, _) -> true

  | (TInt (Some size) | TUint (Some size)), TFixed (Some size', dec)
  | TUint (Some size), TUfixed (Some size', dec) ->
      (size <= integer_part_size size' dec)

  (* (Un)bounded fixed <= Unbounded fixed with more decimals *)
  | TFixed (_, udec), TFixed (None, udec')
  | TUfixed (_, udec), (TUfixed (None, udec') | TFixed (None, udec')) ->
      (udec <= udec')

  (* Bounded fixed <= Bigger bound fixed.*)
  | TUfixed (Some size, udec), (  TUfixed (Some size', udec')
                                | TFixed  (Some size', udec'))
  | TFixed (Some size, udec), TFixed (Some size', udec')  ->
      (udec <= udec') &&
      (integer_part_size size udec <= integer_part_size size' udec')

  | TRationalConst (q, sz_opt), TFixBytes bsz ->
      ExtQ.is_int q &&
      not (ExtQ.is_neg q) &&
      (match sz_opt with
       | Some sz -> (sz = bsz)
       | _ -> false)
  | TRationalConst (q, _), TUint None ->
      ExtQ.is_int q &&
      not (ExtQ.is_neg q)
  | TRationalConst (q, _), TUint (Some sz) ->
      ExtQ.is_int q &&
      not (ExtQ.is_neg q) &&
      (Z.numbits (Q.num q) < sz) (* TODO: <= ? *)
  | TRationalConst (q, _), TInt None ->
      ExtQ.is_int q
  | TRationalConst (q, _), TInt (Some sz) ->
      (* Note: when negative, add one to correctly count bits *)
      let n = if ExtQ.is_neg q then Z.succ (Q.num q) else Q.num q in
      ExtQ.is_int q &&
      (Z.numbits n < sz) (* TODO: <= ? *)
  | TLiteralString (s), TString (loc) ->
      valid_string s &&
      (ignore_loc || convertible_location ~from:LMemory ~to_:loc)
  | TLiteralString (_s), TBytes (loc) ->
      (ignore_loc || convertible_location ~from:LMemory ~to_:loc)
  | TLiteralString (s), TFixBytes (sz) ->
      (String.length s <= sz)
  | TAddress (true), TAddress _ ->
      true
  | TContract (_, derived, _), TContract (base, _, _) ->
      List.exists (fun (derived, _) ->
          LongIdent.equal derived base) derived.contract_hierarchy
  | TString (loc1), TString (loc2)
  | TBytes (loc1), TBytes (loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2)
  | TStruct (lid1, _, loc1), TStruct (lid2, _, loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2) &&
      LongIdent.equal lid1 lid2
  | TArray (from, _, loc1), TArray (to_, _, loc2) ->
      (ignore_loc || convertible_location ~from:loc1 ~to_:loc2) &&
       implicitly_convertible ~ignore_loc ~from ~to_ ()
  | TMapping (tk1, tv1, loc1), TMapping (tk2, tv2, loc2) ->
      (ignore_loc || is_loc_storage loc1 && is_loc_storage_ptr loc2) &&
       implicitly_convertible ~ignore_loc ~from:tk1 ~to_:tk2 () &&
       implicitly_convertible ~ignore_loc ~from:tv1 ~to_:tv2 ()
  | TTuple (tl1), TTuple (tl2) ->
      implicitly_convertible_ol ~ignore_loc ~from:tl1 ~to_:tl2 ()
  (* TON-specific *)
  | TOptional (t1), TOptional (t2) ->
      implicitly_convertible ~ignore_loc ~from:t1 ~to_:t2 ()
  | _ ->
      same_type from to_

and implicitly_convertible_ol ?(ignore_loc=false) ~from ~to_ () =
  (List.length from = List.length to_) &&
  List.for_all2 (fun from_opt to_opt ->
      match from_opt, to_opt with
      | Some from, Some to_ -> implicitly_convertible ~ignore_loc ~from ~to_ ()
      | None, None -> true
      | Some _, None -> true
      | None, Some _ -> false) from to_

and implicitly_convertible_l ?(ignore_loc=false) ~from ~to_ () =
  (List.length from = List.length to_) &&
  List.for_all2 (fun from to_ ->
      implicitly_convertible ~ignore_loc ~from ~to_ ()) from to_




(* Check whether explicit conversion can occur between two type and returns
   the casted type. *)

let rec explicitly_convertible ~from ~to_ : type_ option =
  let if_true cond = if cond then Some to_ else None in

  match from, to_ with
  | (TInt isz | TUint isz), TFixBytes bsz -> begin
      let isz = match isz with
        | None -> 256
        | Some s -> s in
       if_true (bsz = (isz/8))
      end

  | TAddress _, TFixBytes bsz ->
      if_true (bsz = 20 || bsz = 21)

  | TFixBytes bsz, TAddress _ ->
      if (bsz = 20 || bsz = 21) then
        Some (TAddress (true))
      else
        None

  | TAddress _, TContract _ -> Some (to_)
  | TContract (_, cd, _), TAddress (payable) ->
      if not payable then Some (to_)
      else begin
        let idl = lookup_ident cd.contract_env
            ~upper:false ~lookup:LAny Ident.receive in
        let payable =
          List.exists (function
              | Function { function_mutability = MPayable; _ } -> true
              | _ -> false
            ) idl
        in
        Some (TAddress (payable))
      end

  | TContract (_, derived, _), TContract (base, _, _) ->
      if_true (
        List.exists (fun (derived, _) ->
            LongIdent.equal derived base
          ) derived.contract_hierarchy)

  | (TInt _ | TUint _), TAddress (false) ->
      Some (TAddress (true))

  | TRationalConst (q, _), TAddress _ ->
      if ExtQ.is_int q then Some (TAddress true)
      else None

  | TRationalConst (q, sz_opt), TFixBytes bsz ->
      if_true (
        ExtQ.is_int q &&
        not (ExtQ.is_neg q) &&
        (match sz_opt with
           | Some sz -> (sz = bsz)
           | _ -> false))

  | TRationalConst (q, _),
    (TInt _ | TUint _ | TContract _ | TEnum _) ->
      if_true (ExtQ.is_int q)

  | TLiteralString s, TString (LMemory | LStorage (false)) ->
      if_true (valid_string s)

  | TLiteralString s, TFixBytes sz ->
      if_true ((String.length s <= sz))

  | (TString (loc1) | TBytes (loc1)),
    (TString (loc2) | TBytes (loc2)) ->
      if_true (convertible_location ~from:loc1 ~to_:loc2)

  | TArray (from, sz_from, loc1), TArray (to_, sz_to, loc2) -> begin
      let test_size () =
        match sz_from, sz_to with
          | None, None -> true
          | Some s1, Some s2 -> Z.equal s1 s2
          | _ -> false in
      let test_loc () = convertible_location ~from:loc1 ~to_:loc2 in
      if test_size () && test_loc () then
        match explicitly_convertible ~from ~to_ with
          | Some t -> Some (TArray (t, sz_to, loc2))
          | None -> None
      else None

    end

  | TTuple tl1, TTuple tl2 -> begin
      match explicitly_convertible_ol ~from:tl1 ~to_:tl2 with
        | None -> None
        | Some (l) -> Some (TTuple l)
    end

  (* Automatic conversions *)
  | TLiteralString _, TBytes (LMemory | LStorage (false))
  | (TInt _ | TUint _),
    (TInt _ | TUint _ | TAddress _ | TContract _ | TEnum _)
  | TFixBytes _, TFixBytes _
  | TAddress _,
    (TInt _ | TUint _ | TAddress _)
  | TEnum _, (TInt _ | TUint _) ->
      Some to_

  (* Automatic fails *)
  | _, TStruct _ -> None

  (* TON-specific *)
  | TOptional (from), TOptional (to_) ->
      explicitly_convertible ~from ~to_

  | _ ->
      if_true (same_type from to_)

and explicitly_convertible_ol ~from ~to_ : type_ option list option =
  if (List.length from = List.length to_) then
    let exception Stop in
    let rec loop acc froml tol =
      match froml, tol with
        | [], [] -> List.rev acc
        | from :: tl_from, to_ :: tl_to -> begin
            let acc =
              match from, to_ with
                | None, None -> None :: acc (* Ok, but there is no type *)
                | Some t, None
                | None, Some t -> Some t :: acc
                | Some from, Some to_ ->
                    let res = explicitly_convertible ~from ~to_ in
                    match res with
                      | None -> raise Stop
                      | (Some _) -> res :: acc in
            loop acc tl_from tl_to
          end
        | _ :: _, [] | [], _ :: _ -> assert false (* List have the same size *)
     in
     try
       Some (loop [] from to_)
     with Stop -> None
  else None

and explicitly_convertible_l ~from ~to_ : type_ list option =
  if (List.length from = List.length to_) then
    let exception Stop in
    let rec loop acc froml tol =
      match froml, tol with
        | [], [] -> List.rev acc
        | from :: tl_from, to_ :: tl_to -> begin
            let acc =
              match explicitly_convertible ~from ~to_ with
                | None -> raise Stop
                | Some res -> res :: acc in
            loop acc tl_from tl_to
          end
        | _ :: _, [] | [], _ :: _ -> assert false (* List have the same size *)
     in
     try
       Some (loop [] from to_)
     with Stop -> None
  else None

let explicitly_convertible_bool ~from ~to_ =
  match explicitly_convertible ~from ~to_ with
    | None -> false
    | Some _ -> true





(* In fact, only value types, with bool and fun restricted to ==/!= *)
let valid_compare_type op = function
  | TBool | TFunction _ ->
  (* TODO: only internal functions can be compared *)
      begin
        match op with
        | CEq | CNeq -> true
        | _ -> false
      end
  | TInt _ | TUint _ | TRationalConst _
  | TFixed _ | TUfixed _ | TFixBytes _
  | TAddress _ | TEnum _ | TContract _ ->
      true
  | TTuple _ (* may become comparable in the future *)
  | TBytes _ | TString _ | TLiteralString _
  | TArray _ | TArraySlice _ | TMapping _ | TStruct _
  | TType _ | TMagic _ | TModifier _  ->
      false
  (* TON-specific *)
  | TTvmCell | TTvmSlice | TTvmBuilder | TExtraCurrencyCollection ->
      true
  | TOptional (_t) ->
      false




let common_type t1 t2 =
  if implicitly_convertible ~from:t1 ~to_:t2 () then
    Some t2
  else if implicitly_convertible ~from:t2 ~to_:t1 () then
    Some t1
  else
    None



let rec mobile_type t =
  match t with
  | TRationalConst (q, _sz_opt) ->
      if ExtQ.is_int q then
        let sz = ExtZ.numbits_mod8 (Q.num q) in
        let sz =
          if (sz > 256) then None
          else Some (sz)
        in
        if ExtQ.is_neg q then TInt (sz)
        else TUint (sz)
      else
        let z, nb_dec = ExtQ.to_fixed q in
        let sz = ExtZ.numbits_mod8 z in
        let sz =
          if (sz > 256) then None
          else Some (sz)
        in
        if ExtQ.is_neg q then TFixed (sz, nb_dec)
        else TUfixed (sz, nb_dec)
  | TLiteralString _s ->
      (* Note: even if not a valid string *)
      TString LMemory
  | TArraySlice (bt, (LCalldata as loc)) ->
      (* Array slices of dynamic calldata arrays are of type array *)
      TArray (bt, None, loc)
  | TTuple tl ->
      TTuple (List.map (function
          | Some t -> Some (mobile_type t)
          | None -> None) tl)
  | _ -> t





(*
Library functions may define overloads with same types but different location
(only memory vs storage or calldata vs storage, calldata vs memory is not valid)
*)

let storage_suffix library = function
  | LStorage (_) when library -> " storage"
  | _ -> ""

let rec canonical_type loc ~library = function
  | TBool ->
      "bool"
  | TInt (None) ->
      "int"
  | TInt (Some sz) ->
      Format.sprintf "int%d" sz
  | TUint (None) ->
      "uint"
  | TUint (Some sz) ->
      Format.sprintf "uint%d" sz
  | TFixed (None, dec) ->
      Format.sprintf "fixed%d" dec
  | TFixed (Some sz, dec) ->
      Format.sprintf "fixed%dx%d" sz dec
  | TUfixed (None, dec) ->
      Format.sprintf "ufixed%d" dec
  | TUfixed (Some sz, dec) ->
      Format.sprintf "ufixed%dx%d" sz dec
  | TAddress (_) ->
      "address"
  | TFixBytes (sz)->
      Format.sprintf "bytes%d" sz

  | TBytes (l) ->
      Format.sprintf "bytes%s" (storage_suffix library l)
  | TString (l) ->
      Format.sprintf "string%s" (storage_suffix library l)
  | TArray (t, None, l) ->
      Format.sprintf "%s[]%s"
        (canonical_type loc ~library t) (storage_suffix library l)
  | TArray (t, Some sz, l) ->
      Format.sprintf "%s[%s]%s"
        (canonical_type loc ~library t) (Z.to_string sz)
        (storage_suffix library l)

  | TContract (lid, _cd, false) ->
      if library then
        (LongIdent.to_string lid)
      else
        "address"

  | TEnum (lid, ed) ->
      if library then
        (LongIdent.to_string lid)
      else
        let n = List.length ed.enum_values in
        let sz = ExtZ.numbits_mod8 (Z.of_int n) in
        Format.sprintf "uint%d" sz

  | TStruct (lid, sd, l) ->
      if library then
        Format.sprintf "%s%s"
          (LongIdent.to_string lid) (storage_suffix library l)
      else
        let tl = List.map (fun (_id, t) ->
            canonical_type loc ~library t) sd.struct_fields in
        Format.sprintf "(%s)" (String.concat "," tl)

  | TFunction (fd, _fd_opt) ->
      let tl = List.map (fun (t, _id) ->
          canonical_type loc ~library t) fd.function_params in
      Format.sprintf "function(%s)" (String.concat "," tl)

  | TMapping (t1, t2, _loc) -> (* Note: loc is only LStorage*)
      Format.sprintf "mapping(%s => %s) storage"
        (canonical_type loc ~library t1) (canonical_type loc ~library t2)

  | TContract (_, _, true)
  | TModifier (_)
  | TTuple (_)
  | TArraySlice (_)
  | TType (_)
  | TMagic (_)
  | TRationalConst (_)
  | TLiteralString (_) ->
      error loc "Internal type can not be canonized"
  (* TON-specific *)
  | TTvmCell ->
      "TvmCell"
  | TTvmSlice ->
      "TvmSlice"
  | TTvmBuilder ->
      "TvmBuilder"
  | TExtraCurrencyCollection ->
      "ExtraCurrencyCollection"
  | TOptional (t) ->
      Format.sprintf "optional(%s)" (canonical_type loc ~library t)

let node_list_loc body =
  match body with
    | [] -> dummy_loc
    | {loc; _} :: _ -> loc
