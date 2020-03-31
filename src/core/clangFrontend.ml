open Vocab
module H = Hashtbl
module C = Clang
module F = Format
module L = Logging

exception UnknownSyntax

module EnvData = struct
  type t = EnvVar of Cil.varinfo | EnvEnum of Cil.exp | EnvTyp of Cil.typ

  let to_string = function
    | EnvVar vi -> vi.vname
    | EnvEnum e -> CilHelper.s_exp e
    | EnvTyp t -> CilHelper.s_type t
end

module Env = struct
  type t = {
    var : (string, EnvData.t) H.t;
    typ : (string, Cil.typ) H.t;
    label : (string, string) H.t;
  }

  let create () = { var = H.create 64; typ = H.create 64; label = H.create 64 }

  let add_var name vi env =
    H.add env.var name vi;
    env

  let add_typ name typ env =
    H.add env.typ name typ;
    env

  let add_label name env =
    H.add env.label name name;
    env

  let mem_var name env = H.mem env.var name

  let mem_typ name env = H.mem env.typ name

  let mem_label name env = H.mem env.label name

  let find_var name env = H.find env.var name

  let find_typ name env = H.find env.typ name

  let find_label name env = H.find env.label name
end

module Scope = struct
  type t = Env.t list

  let empty = []

  let create () = [ Env.create () ]

  let enter scope = Env.create () :: scope

  let exit = List.tl

  let add name varinfo = function
    | h :: t as l ->
        ignore (Env.add_var name varinfo h);
        l
    | [] -> failwith "empty scope"

  let add_type name typ = function
    | h :: t as l ->
        ignore (Env.add_typ name typ h);
        l
    | [] -> failwith "empty scope"

  let add_label name = function
    | h :: t as l ->
        ignore (Env.add_label name h);
        l
    | [] -> failwith "empty scope"

  let rec mem_var name = function
    | h :: t -> if Env.mem_var name h then true else mem_var name t
    | [] -> false

  let rec mem_typ name = function
    | h :: t -> if Env.mem_typ name h then true else mem_typ name t
    | [] -> false

  let rec mem_label name = function
    | h :: t -> if Env.mem_label name h then true else mem_label name t
    | [] -> false

  let rec find ?(allow_undef = false) ?(compinfo = None) name = function
    | h :: t ->
        if H.mem h name then H.find h name
        else find ~allow_undef ~compinfo name t
    | [] when allow_undef ->
        let ftype = Cil.TFun (Cil.intType, None, false, []) in
        EnvData.EnvVar (Cil.makeGlobalVar name ftype)
    | [] when compinfo <> None ->
        EnvData.EnvTyp (Cil.TComp (Option.get compinfo, []))
    | [] -> failwith (name ^ " not found")

  let rec find_var_enum ?(allow_undef = false) name = function
    | h :: t ->
        if Env.mem_var name h then Env.find_var name h
        else find_var_enum ~allow_undef name t
    | [] when allow_undef ->
        let ftype = Cil.TFun (Cil.intType, None, false, []) in
        EnvData.EnvVar (Cil.makeGlobalVar name ftype)
    | _ -> failwith ("variable " ^ name ^ " not found")

  let rec find_type ?(compinfo = None) name = function
    | h :: t ->
        if Env.mem_typ name h then Env.find_typ name h
        else find_type ~compinfo name t
    | [] when name = "__builtin_va_list" || name = "__va_list_tag" ->
        Cil.TBuiltin_va_list []
    | [] when compinfo <> None ->
        let compinfo = Option.get compinfo in
        if compinfo.Cil.cname = name then Cil.TComp (compinfo, [])
        else failwith ("type of " ^ name ^ " not found")
    | _ -> failwith ("type of " ^ name ^ " not found")

  let pp fmt scope =
    let fmt = F.std_formatter in
    List.iter
      (fun env ->
        F.fprintf fmt "=====\n";
        H.iter
          (fun name v -> F.fprintf fmt "%s -> %s\n" name (EnvData.to_string v))
          env;
        F.fprintf fmt "=====\n")
      scope
end

let empty_block = { Cil.battrs = []; bstmts = [] }

let struct_id_count = ref 0

let new_record_id is_struct =
  let kind = if is_struct then "struct" else "union" in
  let new_id = "__anon" ^ kind ^ "_" ^ string_of_int !struct_id_count in
  struct_id_count := !struct_id_count + 1;
  new_id

type exp_action = ADrop | AExp

let alpha_count = ref 0

let create_new_global_variable scope name typ =
  let new_name =
    if Scope.mem_var name scope then (
      let new_name = name ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name )
    else name
  in
  let varinfo = Cil.makeGlobalVar new_name typ in
  let scope = Scope.add name (EnvData.EnvVar varinfo) scope in
  (varinfo, scope)

let find_global_variable scope name typ =
  if Scope.mem_var name scope then
    let envdata = Scope.find_var_enum name scope in
    match envdata with
    | EnvData.EnvVar vi -> (vi, scope)
    | _ -> create_new_global_variable scope name typ
  else create_new_global_variable scope name typ

let create_local_variable scope fundec name typ =
  let new_name =
    if Scope.mem_var name scope then (
      let new_name = name ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name )
    else name
  in
  let varinfo = Cil.makeLocalVar fundec new_name typ in
  let scope = Scope.add name (EnvData.EnvVar varinfo) scope in
  (varinfo, scope)

let create_label scope label =
  let new_name =
    if Scope.mem_var label scope then (
      let new_name = label ^ "___" ^ string_of_int !alpha_count in
      alpha_count := !alpha_count + 1;
      new_name )
    else label
  in
  let scope = Scope.add_label new_name scope in
  (new_name, scope)

let trans_location node =
  let location =
    C.Ast.location_of_node node |> C.Ast.concrete_of_source_location C.Presumed
  in
  {
    Cil.file = location.C.Ast.filename;
    line = location.C.Ast.line;
    byte = location.C.Ast.column;
  }

let get_compinfo typ =
  match Cil.unrollType typ with
  | Cil.TComp (ci, _) -> ci
  | _ -> failwith ("invalid type: " ^ CilHelper.s_type typ)

let trans_int_kind : C.Ast.builtin_type -> Cil.ikind = function
  | C.Int | C.Bool -> Cil.IInt
  | C.Char_U | C.UChar -> Cil.IUChar
  | C.UShort -> Cil.IUShort
  | C.UInt -> Cil.IUInt
  | C.ULong -> Cil.IULong
  | C.ULongLong -> Cil.IULongLong
  | C.Char_S -> Cil.IChar
  | C.SChar -> Cil.ISChar
  | C.Short -> Cil.IShort
  | C.Long -> Cil.ILong
  | C.LongLong -> Cil.ILongLong
  | _ -> invalid_arg "int kind"

let trans_float_kind : C.Ast.builtin_type -> Cil.fkind = function
  | C.Float -> Cil.FFloat
  | C.Double -> Cil.FDouble
  | C.LongDouble -> Cil.FLongDouble
  | _ -> invalid_arg "float kind"

let trans_binop lhs rhs = function
  | C.Mul -> Cil.Mult
  | C.Div -> Cil.Div
  | C.Rem -> Cil.Mod
  | C.Add when Cil.typeOf lhs |> Cil.isPointerType -> Cil.PlusPI
  | C.Add -> Cil.PlusA
  | C.Sub
    when Cil.typeOf lhs |> Cil.isPointerType
         && Cil.typeOf rhs |> Cil.isPointerType ->
      Cil.MinusPP
  | C.Sub when Cil.typeOf lhs |> Cil.isPointerType -> Cil.MinusPI
  | C.Sub -> Cil.MinusA
  | C.Shl -> Cil.Shiftlt
  | C.Shr -> Cil.Shiftrt
  | C.LT -> Cil.Lt
  | C.GT -> Cil.Gt
  | C.LE -> Cil.Le
  | C.GE -> Cil.Ge
  | C.EQ -> Cil.Eq
  | C.NE -> Cil.Ne
  | C.And -> Cil.BAnd
  | C.Xor -> Cil.BXor
  | C.Or -> Cil.BOr
  | C.LAnd -> Cil.LAnd
  | C.LOr -> Cil.LOr
  | _ -> failwith "invalid binop"

let string_of_declaration_name name =
  match name with
  | C.Ast.IdentifierName s -> s
  | _ -> failwith "name_of_ident_ref"

let name_of_ident_ref idref = string_of_declaration_name idref.C.Ast.name

let trans_attribute typ =
  if typ.C.Ast.const then [ Cil.Attr ("const", []) ] else []

let rec trans_type ?(compinfo = None) scope typ =
  match typ.C.Ast.desc with
  | C.Ast.Pointer pt ->
      Cil.TPtr (trans_type ~compinfo scope pt, trans_attribute typ)
  | C.Ast.FunctionType ft -> trans_function_type scope ft
  | C.Ast.Typedef td -> Scope.find_type ~compinfo (name_of_ident_ref td) scope
  | C.Ast.Elaborated et -> trans_type ~compinfo scope et.named_type
  | C.Ast.Record rt -> Scope.find_type ~compinfo (name_of_ident_ref rt) scope
  | C.Ast.Enum et -> Scope.find_type ~compinfo (name_of_ident_ref et) scope
  | C.Ast.InvalidType -> failwith "invalid type"
  | C.Ast.Vector _ -> failwith "vector type"
  | C.Ast.BuiltinType _ -> trans_builtin_type ~compinfo scope typ
  | x -> trans_builtin_type ~compinfo scope typ

and trans_builtin_type ?(compinfo = None) scope t =
  let k = C.get_type_kind t.C.Ast.cxtype in
  let attr = trans_attribute t in
  match k with
  | C.Void -> Cil.TVoid attr
  (* integer types *)
  | C.Int | C.Bool | C.Char_U | C.UChar | C.UShort | C.UInt | C.ULong
  | C.ULongLong | C.Char_S | C.SChar | C.Short | C.Long | C.LongLong ->
      Cil.TInt (trans_int_kind (k : C.Ast.builtin_type), attr)
  | C.Float | C.Double | C.LongDouble -> Cil.TFloat (trans_float_kind k, attr)
  | C.Pointer -> failwith "pointer"
  | C.Enum -> failwith "enum"
  | C.Typedef -> failwith "typedef"
  | C.FunctionNoProto -> failwith "typedef"
  | C.FunctionProto -> failwith "typedef"
  | C.ConstantArray ->
      let size = C.get_array_size t.cxtype |> Cil.integer in
      let elem_type =
        C.get_array_element_type t.cxtype
        |> C.Type.of_cxtype |> trans_type ~compinfo scope
      in
      Cil.TArray (elem_type, Some size, attr)
  | C.VariableArray | C.IncompleteArray ->
      let elem_type =
        C.get_array_element_type t.cxtype
        |> C.Type.of_cxtype |> trans_type ~compinfo scope
      in
      Cil.TArray (elem_type, None, attr)
  | Invalid | Unexposed | Char16 | Char32 -> failwith "type 1"
  | UInt128 | WChar | Int128 | NullPtr | Overload | Dependent | ObjCId ->
      failwith "9"
  | ObjCClass -> failwith "objc class"
  | ObjCSel -> failwith "objc sel"
  | Float128 -> failwith "float 128"
  | Half -> failwith "half"
  | Float16 -> failwith "float 16"
  | ShortAccum -> failwith "short accum"
  | Accum -> failwith "accum"
  | LongAccum | UShortAccum | UAccum | ULongAccum | Complex | BlockPointer
  | LValueReference | RValueReference | Record ->
      failwith "7"
  | ObjCInterface | ObjCObjectPointer | Vector -> failwith ""
  | DependentSizedArray -> failwith "dependent"
  | MemberPointer -> failwith "6"
  | Auto | Elaborated | Pipe -> failwith "5"
  | x ->
      F.fprintf F.err_formatter "%s" (C.get_type_spelling t.cxtype);
      F.fprintf F.err_formatter "\n";
      F.pp_print_flush F.err_formatter ();
      failwith "trans_builtin_type"

and trans_function_type scope typ =
  let return_typ = trans_type scope typ.C.Ast.result in
  let param_types, var_arg = trans_parameter_types scope typ.C.Ast.parameters in
  Cil.TFun (return_typ, param_types, var_arg, [])

and trans_parameter_types scope = function
  | Some params ->
      let formals =
        List.map
          (fun (param : C.Ast.parameter) ->
            (param.desc.name, trans_type scope param.desc.qual_type, []))
          params.C.Ast.non_variadic
      in
      (Some formals, params.C.Ast.variadic)
  | None -> (None, false)

let trans_params scope args fundec =
  match args with
  | Some l ->
      List.fold_left
        (fun scope (param : C.Ast.parameter) ->
          let vi =
            Cil.makeFormalVar fundec param.desc.name
              (trans_type scope param.desc.qual_type)
          in
          Scope.add param.desc.name (EnvData.EnvVar vi) scope)
        scope l.C.Ast.non_variadic
  | None -> scope

let trans_integer_literal decoration il =
  let ikind =
    match decoration with
    | C.Ast.Cursor c -> C.get_cursor_type c |> C.get_type_kind |> trans_int_kind
    | _ -> failwith "qqq"
  in
  match il with
  | C.Ast.Int i -> Cil.kinteger ikind i
  | _ -> failwith "unknown integer literal"

let trans_floating_literal decoration il =
  let fkind =
    match decoration with
    | C.Ast.Cursor c ->
        C.get_cursor_type c |> C.get_type_kind |> trans_float_kind
    | _ -> failwith "qqq"
  in
  match il with
  | C.Ast.Float f -> Cil.Const (Cil.CReal (f, fkind, None))
  | _ -> failwith "no"

let trans_string_literal sl = Cil.Const (Cil.CStr sl.C.Ast.bytes)

let type_of_decoration decoration =
  match decoration with
  | C.Ast.Cursor c -> C.get_cursor_type c
  | _ -> failwith "qqq"

let type_of_expr expr = C.Type.of_node expr

let trans_decl_ref scope allow_undef idref =
  let name = name_of_ident_ref idref in
  match Scope.find_var_enum ~allow_undef name scope with
  | EnvVar varinfo ->
      let exp = Cil.Lval (Cil.Var varinfo, NoOffset) in
      ([], Some exp)
  | EnvEnum enum -> ([], Some enum)
  | _ -> failwith "no found"

let should_ignore_implicit_cast1 expr qual_type =
  let expr_kind = C.Ast.cursor_of_node expr |> C.ext_get_cursor_kind in
  let type_kind =
    C.get_pointee_type qual_type.C.Ast.cxtype |> C.ext_type_get_kind
  in
  (* ignore FunctionToPointerDecay and BuiltinFnToFnPtr *)
  expr_kind = C.ImplicitCastExpr
  && (type_kind = C.FunctionNoProto || type_kind = C.FunctionProto)

let rec append_instr sl instr =
  match sl with
  | [ ({ Cil.skind = Cil.Instr l } as h) ] ->
      [ { h with skind = Cil.Instr (l @ [ instr ]) } ]
  | [] -> [ Cil.mkStmt (Cil.Instr [ instr ]) ]
  | h :: t -> h :: append_instr t instr

let rec append_stmt_list sl1 sl2 =
  match (sl1, sl2) with
  | ( [ ({ Cil.skind = Cil.Instr l1 } as h1) ],
      ({ Cil.skind = Cil.Instr l2 } as h2) :: t2 )
  (* merging statements with labels may break goto targets *)
    when h1.labels = [] && h2.labels = [] ->
      { h1 with skind = Cil.Instr (l1 @ l2) } :: t2
  | [], _ -> sl2
  | h1 :: t1, _ -> h1 :: append_stmt_list t1 sl2

let rec should_ignore_implicit_cast2 e typ =
  (* ignore LValueToRValue *)
  match (typ, Cil.typeOf e) with
  | Cil.TVoid _, Cil.TVoid _
  | Cil.TInt (_, _), Cil.TInt (_, _)
  | Cil.TFloat (_, _), Cil.TFloat (_, _)
  | Cil.TPtr (_, _), Cil.TPtr (_, _)
  | Cil.TArray (_, _, _), Cil.TArray (_, _, _)
  | Cil.TFun (_, _, _, _), Cil.TFun (_, _, _, _)
  | Cil.TNamed (_, _), Cil.TNamed (_, _)
  | Cil.TComp (_, _), Cil.TComp (_, _)
  | Cil.TEnum (_, _), Cil.TEnum (_, _)
  | Cil.TBuiltin_va_list _, Cil.TBuiltin_va_list _ ->
      (* enumerate all to preserve typedef because typeSig unrolls TNamed *)
      Cil.typeSig typ = (Cil.typeOf e |> Cil.typeSig)
  | _, _ -> false

let rec trans_expr ?(allow_undef = false) ?(skip_lhs = false) scope fundec_opt
    loc action (expr : C.Ast.expr) =
  try
    match expr.C.Ast.desc with
    | C.Ast.IntegerLiteral il ->
        ([], Some (trans_integer_literal expr.decoration il))
    | C.Ast.FloatingLiteral fl ->
        ([], Some (trans_floating_literal expr.decoration fl))
    | C.Ast.StringLiteral sl -> ([], Some (trans_string_literal sl))
    | C.Ast.CharacterLiteral cl ->
        ([], Some (Cil.Const (Cil.CChr (char_of_int cl.value))))
    | C.Ast.UnaryOperator uo ->
        let typ = type_of_expr expr |> trans_type scope in
        let il, exp =
          trans_unary_operator scope fundec_opt loc action typ uo.kind
            uo.operand
        in
        (il, Some exp)
    | C.Ast.BinaryOperator bo ->
        let typ = type_of_expr expr |> trans_type scope in
        let il, exp =
          trans_binary_operator scope fundec_opt loc action typ bo.kind bo.lhs
            bo.rhs
        in
        (il, Some exp)
    | C.Ast.DeclRef idref -> trans_decl_ref scope allow_undef idref
    | C.Ast.Call call ->
        trans_call scope skip_lhs fundec_opt loc action call.callee call.args
    | C.Ast.Cast cast ->
        let sl, expr_opt =
          trans_expr ~allow_undef scope fundec_opt loc action cast.operand
        in
        let e = Option.get expr_opt in
        let typ = trans_type scope cast.qual_type in
        if should_ignore_implicit_cast1 expr cast.qual_type then (sl, Some e)
        else if should_ignore_implicit_cast2 e typ then (sl, Some e)
        else (sl, Some (Cil.CastE (typ, e)))
    | C.Ast.Member mem ->
        ( [],
          Some (trans_member scope fundec_opt loc mem.base mem.arrow mem.field)
        )
    | C.Ast.ArraySubscript arr ->
        let sl1, base = trans_expr scope fundec_opt loc action arr.base in
        let sl2, idx = trans_expr scope fundec_opt loc action arr.index in
        let base =
          match Option.get base |> CilHelper.remove_cast with
          | Cil.Lval lv -> lv
          | e -> failwith (CilHelper.s_exp e)
        in
        let new_lval =
          match idx with
          | Some x when Cil.isPointerType (Cil.typeOfLval base) ->
              ( Cil.Mem
                  (Cil.BinOp (Cil.PlusPI, Cil.Lval base, x, Cil.typeOfLval base)),
                Cil.NoOffset )
          | Some x -> Cil.addOffsetLval (Cil.Index (x, Cil.NoOffset)) base
          | _ -> failwith "lval"
        in
        (sl1 @ sl2, Some (Cil.Lval new_lval))
    | C.Ast.ConditionalOperator co ->
        trans_cond_op scope fundec_opt loc co.cond co.then_branch co.else_branch
    | C.Ast.UnaryExpr ue ->
        trans_unary_expr scope fundec_opt loc ue.kind ue.argument
    | C.Ast.UnexposedExpr e -> (
        match e with
        | DesignatedInitExpr -> failwith "not implemented"
        | _ -> failwith "not expected" )
    | C.Ast.InitList el -> failwith "init list"
    | C.Ast.ImaginaryLiteral _ ->
        failwith "Unsupported syntax (ImaginaryLiteral)"
    | C.Ast.BoolLiteral _ -> failwith "Unsupported syntax (BoolLiteral)"
    | C.Ast.NullPtrLiteral -> failwith "Unsupported syntax (NullPtrLiteral)"
    | C.Ast.UnknownExpr (C.StmtExpr, C.StmtExpr) ->
        (* StmtExpr is not supported yet *)
        raise UnknownSyntax
    | C.Ast.UnknownExpr (_, _) ->
        prerr_endline ("warning unknown expr " ^ CilHelper.s_location loc);
        Clangml_show.pp_expr F.err_formatter expr;
        raise UnknownSyntax
    | _ ->
        Clangml_show.pp_expr F.err_formatter expr;
        failwith "unknown trans_expr"
  with UnknownSyntax -> ([], Some Cil.zero)

and trans_unary_operator scope fundec_opt loc action typ kind expr =
  let sl, var_opt = trans_expr scope fundec_opt loc action expr in
  let var =
    match var_opt with
    | Some x -> x
    | None ->
        prerr_endline (CilHelper.s_location loc);
        Clangml_show.pp_expr F.err_formatter expr;
        failwith "var_opt"
  in
  let lval_of_expr var =
    match var with Cil.Lval x -> x | x -> failwith (CilHelper.s_exp x)
  in
  match kind with
  | C.PostInc ->
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.PlusPI else Cil.PlusA
      in
      let fundec = Option.get fundec_opt in
      (* i++ ==> temp = i; i = i + 1; temp *)
      let temp = (Cil.Var (Cil.makeTempVar fundec typ), Cil.NoOffset) in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr2 = Cil.Set (lval_of_expr var, exp, loc) in
      if action = ADrop then (sl @ [ Cil.mkStmt (Cil.Instr [ instr2 ]) ], var)
      else
        let instr1 = Cil.Set (temp, var, loc) in
        (sl @ [ Cil.mkStmt (Cil.Instr [ instr1; instr2 ]) ], Cil.Lval temp)
  | C.PostDec ->
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.MinusPI else Cil.MinusA
      in
      let fundec = Option.get fundec_opt in
      let temp = (Cil.Var (Cil.makeTempVar fundec typ), Cil.NoOffset) in
      let instr1 = Cil.Set (temp, var, loc) in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr2 = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr1; instr2 ]) ], Cil.Lval temp)
  | C.PreInc ->
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.PlusPI else Cil.PlusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], var)
  | C.PreDec ->
      let op =
        if Cil.typeOf var |> Cil.isPointerType then Cil.MinusPI else Cil.MinusA
      in
      let exp = Cil.BinOp (op, var, Cil.one, Cil.intType) in
      let instr = Cil.Set (lval_of_expr var, exp, loc) in
      (sl @ [ Cil.mkStmt (Cil.Instr [ instr ]) ], var)
  | C.AddrOf -> (sl, Cil.AddrOf (lval_of_expr var))
  | C.Deref -> (sl, Cil.Lval (Cil.Mem var, Cil.NoOffset))
  | C.Plus -> (sl, Cil.Lval (lval_of_expr var))
  | C.Minus -> (sl, Cil.UnOp (Cil.Neg, var, typ))
  | C.Not -> (sl, Cil.UnOp (Cil.BNot, var, typ))
  | C.LNot -> (sl, Cil.UnOp (Cil.LNot, var, typ))
  | C.Extension -> (sl, var)
  | _ ->
      Clangml_show.pp_expr F.err_formatter expr;
      failwith ("unary_operator at " ^ CilHelper.s_location loc)

and trans_binary_operator scope fundec_opt loc action typ kind lhs rhs =
  let lhs_sl, lhs_opt = trans_expr scope fundec_opt loc AExp lhs in
  let rhs_sl, rhs_opt = trans_expr scope fundec_opt loc AExp rhs in
  let lhs_expr = match lhs_opt with Some x -> x | None -> failwith "lhs" in
  let rhs_expr = match rhs_opt with Some x -> x | None -> failwith "rhs" in
  match kind with
  | C.Mul | C.Div | C.Rem | C.Add | C.Sub | C.Shl | C.Shr | C.LT | C.GT | C.LE
  | C.GE | C.EQ | C.NE | C.And | C.Xor | C.Or | C.LAnd | C.LOr ->
      ( rhs_sl @ lhs_sl,
        Cil.constFoldBinOp false
          (trans_binop lhs_expr rhs_expr kind)
          lhs_expr rhs_expr typ )
  | C.Assign -> (
      let lval =
        match lhs_expr with Cil.Lval l -> l | _ -> failwith "invalid lhs"
      in
      match (rhs_expr, rhs_sl) with
      | ( Cil.Lval _,
          [ ({ Cil.skind = Cil.Instr [ Cil.Call (Some y, f, el, loc) ] } as s) ]
        ) ->
          let stmt =
            { s with skind = Cil.Instr [ Cil.Call (Some lval, f, el, loc) ] }
          in
          (append_stmt_list lhs_sl [ stmt ], lhs_expr)
      | _ ->
          let instr = Cil.Set (lval, rhs_expr, loc) in
          (append_instr (rhs_sl @ lhs_sl) instr, lhs_expr) )
  | C.MulAssign | C.DivAssign | C.RemAssign | C.AddAssign | C.SubAssign
  | C.ShlAssign | C.ShrAssign | C.AndAssign | C.XorAssign | C.OrAssign ->
      let drop_assign = function
        | C.MulAssign -> C.Mul
        | C.DivAssign -> C.Div
        | C.RemAssign -> C.Rem
        | C.AddAssign -> C.Add
        | C.SubAssign -> C.Sub
        | C.ShlAssign -> C.Shl
        | C.ShrAssign -> C.Shr
        | C.AndAssign -> C.And
        | C.XorAssign -> C.Xor
        | C.OrAssign -> C.Or
        | _ -> failwith "Invalid syntaxk"
      in
      let lval =
        match lhs_expr with Cil.Lval l -> l | _ -> failwith "invalid lhs"
      in
      let bop = drop_assign kind in
      let rhs =
        Cil.BinOp (trans_binop lhs_expr rhs_expr bop, lhs_expr, rhs_expr, typ)
      in
      let stmt = Cil.mkStmt (Cil.Instr [ Cil.Set (lval, rhs, loc) ]) in
      (rhs_sl @ lhs_sl @ [ stmt ], lhs_expr)
  | C.Comma -> failwith "Unsupported syntax (Comma)"
  | C.Cmp | C.PtrMemD | C.PtrMemI | C.InvalidBinaryOperator ->
      failwith "unsupported expr"

and trans_call scope skip_lhs fundec_opt loc action callee args =
  let fundec = Option.get fundec_opt in
  let callee_insts, callee_opt =
    trans_expr ~allow_undef:true scope fundec_opt loc AExp callee
  in
  let callee = match callee_opt with Some x -> x | None -> failwith "call" in
  let args_insts, args_exprs =
    List.fold_left
      (fun (args_insts, args_exprs) arg ->
        let insts, expr_opt = trans_expr scope fundec_opt loc AExp arg in
        let expr = match expr_opt with Some x -> x | None -> failwith "arg" in
        (args_insts @ insts, args_exprs @ [ expr ]))
      ([], []) args
  in
  let retvar =
    match Cil.typeOf callee with
    | (Cil.TFun (rt, _, _, _) | TPtr (TFun (rt, _, _, _), _))
      when (not (Cil.isVoidType rt)) && not skip_lhs ->
        let temp = (Cil.Var (Cil.makeTempVar fundec rt), Cil.NoOffset) in
        Some temp
    | _ -> None
  in
  let retvar_exp =
    match retvar with Some x -> Some (Cil.Lval x) | _ -> None
  in
  let instr = Cil.Call (retvar, callee, args_exprs, loc) in
  (append_instr (callee_insts @ args_insts) instr, retvar_exp)

and trans_member scope fundec_opt loc base arrow field =
  match base with
  | Some b -> (
      let _, bexp = trans_expr scope fundec_opt loc ADrop b in
      match bexp with
      | Some e when arrow ->
          let typ = Cil.typeOf e in
          let fieldinfo =
            match Cil.unrollTypeDeep typ with
            | Cil.TPtr (TComp (comp, _), _) ->
                let name =
                  match field with
                  | C.Ast.FieldName f -> name_of_ident_ref f.desc
                  | _ -> "unknown"
                in
                List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
            | _ -> failwith "fail"
          in
          Cil.Lval
            (Cil.mkMem ~addr:e ~off:(Cil.Field (fieldinfo, Cil.NoOffset)))
      | Some (Cil.Lval lv) when not arrow ->
          let typ = Cil.typeOfLval lv in
          let fieldinfo =
            match Cil.unrollTypeDeep typ with
            | Cil.TComp (comp, _) ->
                let name =
                  match field with
                  | C.Ast.FieldName f -> name_of_ident_ref f.desc
                  | _ -> "unknown"
                in
                List.find (fun f -> f.Cil.fname = name) comp.Cil.cfields
            | _ -> failwith "fail"
          in
          Cil.Lval (Cil.addOffsetLval (Cil.Field (fieldinfo, Cil.NoOffset)) lv)
      | Some e ->
          CilHelper.s_location loc |> prerr_endline;
          CilHelper.s_exp e |> prerr_endline;
          failwith "error bexp = some e"
      | None ->
          CilHelper.s_location loc |> prerr_endline;
          failwith "error bexp = none" )
  | None ->
      CilHelper.s_location loc |> prerr_endline;
      failwith "error base = none"

and trans_cond_op scope fundec_opt loc cond then_branch else_branch =
  let cond_sl, cond_expr = trans_expr scope fundec_opt loc AExp cond in
  let then_sl, then_expr =
    match then_branch with
    | Some tb -> trans_expr scope fundec_opt loc ADrop tb
    | None -> ([], None)
  in
  let else_sl, else_expr = trans_expr scope fundec_opt loc ADrop else_branch in
  let cond_expr = Option.get cond_expr in
  let else_expr = Option.get else_expr in
  match fundec_opt with
  | None ->
      if Cil.constFold false cond_expr |> Cil.isZero then
        ([], Some (Cil.constFold false else_expr))
      else if then_expr = None then ([], None)
      else ([], Some (Option.get then_expr |> Cil.constFold false))
  | Some fundec ->
      let typ =
        match then_expr with
        | Some e -> Cil.typeOf e
        | None -> Cil.typeOf else_expr
      in
      let vi, scope = create_local_variable scope fundec "tmp" typ in
      let var = (Cil.Var vi, Cil.NoOffset) in
      let bstmts =
        match then_expr with
        | Some e when should_ignore_implicit_cast2 e typ ->
            append_instr then_sl (Cil.Set (var, e, loc))
        | Some e ->
            append_instr then_sl (Cil.Set (var, Cil.CastE (typ, e), loc))
        | None -> []
      in
      let tb = { Cil.battrs = []; bstmts } in
      let bstmts =
        if should_ignore_implicit_cast2 else_expr typ then
          append_instr else_sl (Cil.Set (var, else_expr, loc))
        else
          append_instr else_sl (Cil.Set (var, Cil.CastE (typ, else_expr), loc))
      in
      let fb = { Cil.battrs = []; bstmts } in
      let return_exp =
        if should_ignore_implicit_cast2 (Cil.Lval var) Cil.intType then
          Some (Cil.Lval var)
        else Some (Cil.CastE (Cil.intType, Cil.Lval var))
      in
      (cond_sl @ [ Cil.mkStmt (Cil.If (cond_expr, tb, fb, loc)) ], return_exp)

and trans_unary_expr scope fundec_opt loc kind argument =
  match (kind, argument) with
  | C.SizeOf, C.Ast.ArgumentExpr e -> (
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.SizeOfE e)) | None -> ([], None) )
  | C.SizeOf, C.Ast.ArgumentType t ->
      let typ = trans_type scope t in
      ([], Some (Cil.SizeOf typ))
  | C.AlignOf, C.Ast.ArgumentExpr e -> (
      let _, exp = trans_expr scope fundec_opt loc ADrop e in
      match exp with Some e -> ([], Some (Cil.AlignOfE e)) | None -> ([], None)
      )
  | C.AlignOf, C.Ast.ArgumentType t ->
      let typ = trans_type scope t in
      ([], Some (Cil.AlignOf typ))
  | _, _ -> ([], None)

let get_opt msg = function Some x -> x | None -> failwith msg

let goto_count = ref 0

module Chunk = struct
  module LabelMap = struct
    include Map.Make (String)

    let append xm ym = union (fun k x y -> failwith "duplicated labels") xm ym
  end

  module GotoMap = struct
    include Map.Make (struct
      type t = Cil.stmt ref

      let compare = compare
    end)

    let append xm ym =
      union (fun k x y -> failwith "duplicated goto targets") xm ym
  end

  type t = {
    stmts : Cil.stmt list;
    cases : Cil.stmt list;
    labels : Cil.stmt ref LabelMap.t;
    gotos : string GotoMap.t;
  }

  let empty =
    { stmts = []; cases = []; labels = LabelMap.empty; gotos = GotoMap.empty }

  let append x y =
    {
      stmts = append_stmt_list x.stmts y.stmts;
      cases = x.cases @ y.cases;
      labels = LabelMap.append x.labels y.labels;
      gotos = GotoMap.append x.gotos y.gotos;
    }
end

let append_label chunk label loc in_origin =
  let l = Cil.Label (label, loc, in_origin) in
  match chunk.Chunk.stmts with
  | h :: t ->
      h.labels <- h.labels @ [ l ];
      { chunk with labels = Chunk.LabelMap.add label (ref h) chunk.labels }
  | [] ->
      let h = Cil.mkStmt (Cil.Instr []) in
      h.labels <- [ l ];
      {
        chunk with
        stmts = [ h ];
        labels = Chunk.LabelMap.add label (ref h) chunk.labels;
      }

let trans_storage decl =
  match C.Ast.cursor_of_node decl |> C.cursor_get_storage_class with
  | C.Extern -> Cil.Extern
  | C.Register -> Cil.Register
  | C.Static -> Cil.Static
  | _ -> Cil.NoStorage

let rec trans_stmt scope fundec (stmt : C.Ast.stmt) : Chunk.t * Scope.t =
  let loc = trans_location stmt in
  if !Options.debug then prerr_endline (CilHelper.s_location loc);
  match stmt.C.Ast.desc with
  | C.Ast.Null ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr []) ] }, scope)
  | C.Ast.Compound sl ->
      (* CIL does not need to have local blocks because all variables have unique names *)
      let chunk = trans_compound scope fundec sl in
      (chunk, scope)
  | C.Ast.For fdesc ->
      ( trans_for scope fundec loc fdesc.init fdesc.condition_variable
          fdesc.cond fdesc.inc fdesc.body,
        scope )
  | C.Ast.ForRange _ ->
      failwith ("Unsupported syntax : " ^ CilHelper.s_location loc)
  | C.Ast.If desc ->
      ( trans_if scope fundec loc desc.init desc.condition_variable desc.cond
          desc.then_branch desc.else_branch,
        scope )
  | C.Ast.Switch desc ->
      ( trans_switch scope fundec loc desc.init desc.condition_variable
          desc.cond desc.body,
        scope )
  | C.Ast.Case desc ->
      (trans_case scope fundec loc desc.lhs desc.rhs desc.body, scope)
  | C.Ast.Default stmt -> (trans_default scope fundec loc stmt, scope)
  | C.Ast.While desc ->
      ( trans_while scope fundec loc desc.condition_variable desc.cond desc.body,
        scope )
  | C.Ast.Do desc -> (trans_do scope fundec loc desc.body desc.cond, scope)
  | C.Ast.Label desc -> trans_label scope fundec loc desc.label desc.body
  | C.Ast.Goto label -> (trans_goto scope fundec loc label, scope)
  | C.Ast.IndirectGoto _ ->
      failwith ("Unsupported syntax (IndirectGoto): " ^ CilHelper.s_location loc)
  | C.Ast.Continue ->
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Continue loc) ] },
        scope )
  | C.Ast.Break ->
      ({ Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Break loc) ] }, scope)
  | C.Ast.Asm desc ->
      let instr =
        Cil.Asm ([], [ desc.asm_string ], [], [], [], Cil.locUnknown)
      in
      ( { Chunk.empty with Chunk.stmts = [ Cil.mkStmt (Cil.Instr [ instr ]) ] },
        scope )
  | C.Ast.Return None ->
      let stmts = [ Cil.mkStmt (Cil.Return (None, loc)) ] in
      ({ Chunk.empty with stmts }, scope)
  | C.Ast.Return (Some e) ->
      let sl, expr_opt = trans_expr scope (Some fundec) loc AExp e in
      let expr = get_opt "return" expr_opt in
      let stmts =
        if List.length sl = 0 then [ Cil.mkStmt (Cil.Return (Some expr, loc)) ]
        else sl @ [ Cil.mkStmt (Cil.Return (Some expr, loc)) ]
      in
      ({ Chunk.empty with stmts }, scope)
  | C.Ast.Decl dl ->
      let stmts, scope = trans_var_decl_list scope fundec loc AExp dl in
      ({ Chunk.empty with stmts }, scope)
  | C.Ast.Expr e ->
      (* skip_lhs is true only here: a function is called at the top-most level
       * without a return variable *)
      let stmts, _ =
        trans_expr ~skip_lhs:true scope (Some fundec) loc ADrop e
      in
      ({ Chunk.empty with stmts }, scope)
  | C.Ast.Try _ ->
      failwith ("Unsupported syntax (Try): " ^ CilHelper.s_location loc)
  | C.Ast.AttributedStmt _ ->
      failwith
        ("Unsupported syntax (AttributedStmt)): " ^ CilHelper.s_location loc)
  | C.Ast.UnknownStmt (_, _) ->
      (*       C.Ast.pp_stmt F.err_formatter stmt ; *)
      let stmts = [ Cil.dummyStmt ] in
      ({ Chunk.empty with stmts }, scope)

and trans_compound scope fundec sl =
  let scope = Scope.enter scope in
  List.fold_left
    (fun (l, scope) s ->
      let chunk, scope = trans_stmt scope fundec s in
      (Chunk.append l chunk, scope))
    (Chunk.empty, scope) sl
  |> fst

and trans_var_decl_list scope fundec loc action (dl : C.Ast.decl list) =
  List.fold_left
    (fun (sl, scope) (d : C.Ast.decl) ->
      match d.C.Ast.desc with
      | C.Ast.Var desc ->
          let storage = trans_storage d in
          let decl_stmts, scope =
            trans_var_decl ~storage scope fundec loc action desc
          in
          (sl @ decl_stmts, scope)
      | _ -> (sl, scope))
    ([], scope) dl

and trans_var_decl ?(storage = Cil.NoStorage) (scope : Scope.t) fundec loc
    action (desc : C.Ast.var_decl_desc) =
  let typ = trans_type scope desc.C.Ast.var_type in
  let varinfo, scope = create_local_variable scope fundec desc.var_name typ in
  varinfo.vstorage <- storage;
  match desc.var_init with
  | Some e -> (
      match (e.C.Ast.desc, typ) with
      | C.Ast.InitList el, Cil.TArray (arr_typ, arr_exp, attr) ->
          let len_exp = Option.get arr_exp in
          let arr_len =
            match len_exp with
            | Const c -> (
                match c with
                | CInt64 (v, _, _) -> Int64.to_int v
                | _ -> failwith "not expected" )
            | _ -> failwith "not expected"
          in
          let el =
            if List.length el > arr_len then BatList.take arr_len el else el
          in
          let sl, _ =
            List.fold_left
              (fun (sl, o) i ->
                let _, expr_opt = trans_expr scope (Some fundec) loc action i in
                let expr = get_opt "var_decl" expr_opt in
                let var =
                  (Cil.Var varinfo, Cil.Index (Cil.integer o, Cil.NoOffset))
                in
                let stmt =
                  Cil.mkStmt (Cil.Instr [ Cil.Set (var, expr, loc) ])
                in
                (sl @ [ stmt ], o + 1))
              ([], 0) el
          in
          (sl, scope)

      (* origin source code *)
      (*
      | C.Ast.InitList el ->
          let sl, _ =
            List.fold_left
              (fun (sl, o) i ->
                let _, expr_opt = trans_expr scope (Some fundec) loc action i in
                let expr = get_opt "var_decl" expr_opt in
                let var =
                  (Cil.Var varinfo, Cil.Index (Cil.integer o, Cil.NoOffset))
                in
                let instr = Cil.Set (var, expr, loc) in
                (append_instr sl instr, o + 1))
              ([], 0) el
          in
          (sl, scope)
      *)
      | _ ->
          let sl_expr, expr_opt = trans_expr scope (Some fundec) loc action e in
          let expr = get_opt "var_decl" expr_opt in
          let var = (Cil.Var varinfo, Cil.NoOffset) in
          let instr = Cil.Set (var, expr, loc) in
          (append_instr sl_expr instr, scope) )
  | _ -> ([], scope)

and trans_var_decl_opt scope fundec loc action (vdecl : C.Ast.var_decl option) =
  match vdecl with
  | Some v ->
      let sl, scope = trans_var_decl scope fundec loc AExp v.C.Ast.desc in
      (sl, scope)
  | None -> ([], scope)

and trans_for scope fundec loc init cond_var cond inc body =
  let scope = Scope.enter scope in
  let init_stmt, scope = trans_stmt_opt scope fundec init in
  let decl_stmt, scope = trans_var_decl_opt scope fundec loc AExp cond_var in
  let cond_expr =
    match cond with
    | Some e ->
        trans_expr scope (Some fundec) loc AExp e |> snd |> get_opt "for_cond"
    | None -> Cil.one
  in
  let break_stmt = Cil.mkBlock [ Cil.mkStmt (Cil.Break loc) ] in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc))
    :: body_stmt.Chunk.stmts
  in
  let block = { Cil.battrs = []; bstmts } in
  let inc_stmt = trans_stmt_opt scope fundec inc |> fst in
  let stmts =
    decl_stmt @ init_stmt.Chunk.stmts
    @ [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ]
    @ inc_stmt.Chunk.stmts
  in
  let cases = init_stmt.cases @ body_stmt.cases @ inc_stmt.cases in
  { Chunk.stmts; cases; labels = body_stmt.labels; gotos = body_stmt.gotos }

and trans_while scope fundec loc condition_variable cond body =
  let scope = Scope.enter scope in
  let decl_stmt, scope =
    trans_var_decl_opt scope fundec loc AExp condition_variable
  in
  let cond_expr =
    trans_expr scope (Some fundec) loc AExp cond |> snd |> get_opt "while_cond"
  in
  let break_stmt = Cil.mkBlock [ Cil.mkStmt (Cil.Break loc) ] in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    match Cil.constFold false cond_expr |> Cil.isInteger with
    | Some i64 when Cil.i64_to_int i64 = 1 -> body_stmt.Chunk.stmts
    | _ ->
        Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc))
        :: body_stmt.Chunk.stmts
  in
  let block = { Cil.battrs = []; bstmts } in
  let stmts = decl_stmt @ [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ] in
  {
    Chunk.stmts;
    cases = body_stmt.cases;
    labels = body_stmt.labels;
    gotos = body_stmt.gotos;
  }

and trans_do scope fundec loc body cond =
  let scope = Scope.enter scope in
  let cond_expr =
    trans_expr scope (Some fundec) loc AExp cond |> snd |> get_opt "do_cond"
  in
  let break_stmt = Cil.mkStmt (Cil.Break loc) in
  let body_stmt = trans_block scope fundec body in
  let bstmts =
    match Cil.constFold false cond_expr |> Cil.isInteger with
    | Some i64 when Cil.i64_to_int i64 = 1 -> body_stmt.Chunk.stmts
    | Some i64 when Cil.i64_to_int i64 = 0 ->
        body_stmt.Chunk.stmts @ [ break_stmt ]
    | _ ->
        let break_stmt = Cil.mkBlock [ break_stmt ] in
        body_stmt.Chunk.stmts
        @ [ Cil.mkStmt (Cil.If (cond_expr, empty_block, break_stmt, loc)) ]
  in

  let block = { Cil.battrs = []; bstmts } in
  let stmts = [ Cil.mkStmt (Cil.Loop (block, loc, None, None)) ] in
  {
    Chunk.stmts;
    cases = body_stmt.cases;
    labels = body_stmt.labels;
    gotos = body_stmt.gotos;
  }

and trans_if scope fundec loc init cond_var cond then_branch else_branch =
  let init_stmt = trans_stmt_opt scope fundec init |> fst in
  let decl_stmt, scope = trans_var_decl_opt scope fundec loc AExp cond_var in
  let cond_sl, cond_expr = trans_expr scope (Some fundec) loc AExp cond in
  let then_stmt = trans_block scope fundec then_branch in
  let else_stmt =
    match else_branch with
    | Some s -> trans_block scope fundec s
    | None -> Chunk.empty
  in
  (* let then_block = { Cil.battrs = []; bstmts = then_stmt.stmts } in
     let else_block = { Cil.battrs = []; bstmts = else_stmt.stmts } in*)
  let cond_expr = Option.get cond_expr in
  let duplicate chunk =
    if
      chunk.Chunk.cases <> []
      || not (Chunk.LabelMap.is_empty chunk.Chunk.labels)
    then raise (Failure "cannot duplicate: has labels")
    else
      let count =
        List.fold_left
          (fun c stmt ->
            match stmt.Cil.skind with
            | Cil.If _ | Cil.Switch _ | Cil.Loop _ | Cil.Block _ ->
                raise (Failure "cannot duplicate: complex stmt")
            | Cil.Instr il -> c + List.length il
            | _ -> c)
          0 chunk.Chunk.stmts
      in
      if count > 5 then raise (Failure "cannot duplicate: too many instr")
      else { Chunk.empty with stmts = chunk.Chunk.stmts }
  in
  (* Reference: https://github.com/cil-project/cil/blob/936b04103eb573f320c6badf280e8bb17f6e7b26/src/frontc/cabs2cil.ml#L4837 *)
  let rec compile_cond scope ce st sf =
    match ce with
    | Cil.BinOp (Cil.LAnd, ce1, ce2, _) ->
        let scope, sf1, sf2 =
          try (scope, sf, duplicate sf)
          with Failure _ ->
            let lab, scope = create_label scope "_L" in
            ( scope,
              trans_goto scope fundec loc lab,
              append_label sf lab loc false )
        in
        let scope, st' = compile_cond scope ce2 st sf1 in
        compile_cond scope ce1 st' sf2
    | Cil.BinOp (Cil.LOr, ce1, ce2, _) ->
        let scope, st1, st2 =
          try (scope, st, duplicate st)
          with Failure _ ->
            let lab, scope = create_label scope "_L" in
            ( scope,
              trans_goto scope fundec loc lab,
              append_label st lab loc false )
        in
        let scope, sf' = compile_cond scope ce2 st1 sf in
        compile_cond scope ce1 st2 sf'
    | _ ->
        let then_block = { Cil.battrs = []; bstmts = st.stmts } in
        let else_block = { Cil.battrs = []; bstmts = sf.stmts } in
        ( scope,
          {
            Chunk.stmts =
              [ Cil.mkStmt (Cil.If (ce, then_block, else_block, loc)) ];
            labels = Chunk.LabelMap.append st.labels sf.labels;
            gotos = Chunk.GotoMap.append st.gotos sf.gotos;
            cases = [];
          } )
  in
  let scope, if_chunk = compile_cond scope cond_expr then_stmt else_stmt in
  let stmts =
    decl_stmt @ init_stmt.stmts @ cond_sl
    (*     @ [ Cil.mkStmt (Cil.If (cond_expr, then_block, else_block, loc)) ] *)
    @ if_chunk.Chunk.stmts
  in
  let cases = init_stmt.cases @ then_stmt.cases @ else_stmt.cases in
  {
    Chunk.stmts;
    cases;
    labels =
      if_chunk.labels
      (* Chunk.LabelMap.append then_stmt.labels else_stmt.labels*);
    gotos =
      if_chunk.gotos (*Chunk.GotoMap.append then_stmt.gotos else_stmt.gotos*);
  }

and trans_block scope fundec body =
  match body.C.Ast.desc with
  | C.Ast.Compound l -> trans_compound scope fundec l
  | _ -> trans_stmt scope fundec body |> fst

and trans_switch scope fundec loc init cond_var cond body =
  let init, cope = trans_stmt_opt scope fundec init in
  let decl_sl, scope = trans_var_decl_opt scope fundec loc AExp cond_var in
  let cond_sl, cond_expr_opt = trans_expr scope (Some fundec) loc AExp cond in
  let cond_expr = Option.get cond_expr_opt in
  let body_stmt = trans_stmt scope fundec body |> fst in
  let body = { Cil.battrs = []; bstmts = body_stmt.Chunk.stmts } in
  let cases =
    List.fold_left
      (fun acc s -> if List.memq s acc then acc else s :: acc)
      []
      (init.cases @ body_stmt.cases)
    |> List.rev
  in
  let stmts =
    init.Chunk.stmts @ decl_sl @ cond_sl
    @ [ Cil.mkStmt (Cil.Switch (cond_expr, body, cases, loc)) ]
  in
  { Chunk.empty with stmts }

and trans_case scope fundec loc lhs rhs body =
  let lhs_expr = trans_expr scope (Some fundec) loc ADrop lhs |> snd in
  let chunk = trans_stmt scope fundec body |> fst in
  let label = Cil.Case (Option.get lhs_expr, loc) in
  match chunk.Chunk.stmts with
  | h :: t ->
      h.labels <- h.labels @ [ label ];
      { chunk with cases = h :: chunk.cases }
  | [] -> chunk

and trans_default scope fundec loc stmt =
  let chunk = trans_stmt scope fundec stmt |> fst in
  let label = Cil.Default loc in
  match chunk.Chunk.stmts with
  | h :: t ->
      h.labels <- label :: h.labels;
      { chunk with cases = chunk.cases @ [ h ] }
  | [] -> chunk

and trans_label scope fundec loc label body =
  (* Clang frontend guarantees the uniqueness of label names,
   * so do not need to create unique names.
   * Instead, we only add the label name to the scope,
   * to avoid conflicts with CIL-generated label names *)
  let scope = Scope.add_label label scope in
  let chunk = trans_stmt scope fundec body |> fst in
  (append_label chunk label loc true, scope)

and trans_goto scope fundec loc label =
  let dummy_instr =
    Cil.Asm
      ( [],
        [ "dummy goto target " ^ string_of_int !goto_count ],
        [],
        [],
        [],
        Cil.locUnknown )
  in
  goto_count := !goto_count + 1;
  let placeholder = Cil.mkStmt (Cil.Instr [ dummy_instr ]) in
  let reference = ref placeholder in
  {
    Chunk.empty with
    stmts = [ Cil.mkStmt (Cil.Goto (reference, loc)) ];
    gotos = Chunk.GotoMap.add reference label Chunk.GotoMap.empty;
  }

and trans_stmt_opt scope fundec = function
  | Some s -> trans_stmt scope fundec s
  | None -> (Chunk.empty, scope)

let mk_uninit_arr_remainder ?(arr_len = 0) typ =
  match typ with
  | Cil.TArray (arr_type, arr_exp, _) ->
      let len_exp = Option.get arr_exp in
      let arr_len =
        if arr_len <> 0 then arr_len
        else
          match len_exp with
          | Const c -> (
              match c with
              | CInt64 (v, _, _) -> Int64.to_int v
              | _ -> failwith "not expected" )
          | _ -> failwith "not expected"
      in
      List.init arr_len (fun x -> x)
      |> List.map (fun _ ->
             Cil.SingleInit (Cil.CastE (arr_type, Cil.integer 0)))
  | _ -> failwith "not expected"

let pp_which_cil_type = function
  | Cil.TComp (ci, _) -> "struct"
  | Cil.TInt (ikind, _) -> "int"
  | Cil.TFloat (fkind, _) -> "float"
  | Cil.TPtr (typ, _) -> "pointer"
  | Cil.TNamed (typeinfo, _) -> "named type"
  | Cil.TArray (arr_type, arr_exp, _) -> "array"
  | Cil.TFun (_, _, _, _) -> "func"
  | Cil.TEnum (einfo, _) -> "enum"
  | Cil.TVoid _ -> "void"
  | Cil.TBuiltin_va_list _ -> "va_list"

let is_struct typ = match typ with Cil.TComp (_, _) -> true | _ -> false

let rec mk_init expr scope loc fi =
  (* for uninitaiized *)
  match fi.Cil.ftype with
  | Cil.TInt (ikind, _) when expr = [] ->
      (Cil.SingleInit (Cil.kinteger ikind 0), [])
  | Cil.TFloat (fkind, _) when expr = [] ->
      (Cil.SingleInit (Cil.Const (Cil.CReal (0., fkind, None))), [])
  | Cil.TPtr (typ, _) when expr = [] ->
      (Cil.SingleInit (Cil.CastE (TPtr (typ, []), Cil.integer 0)), [])
  | Cil.TEnum (einfo, _) when expr = [] -> (Cil.SingleInit (Cil.integer 0), [])
  (* for initaiized *)
  | Cil.TInt (ikind, _) when expr <> [] ->
      let e = List.hd expr in
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, List.tl expr)
  | Cil.TFloat (fkind, _) when expr <> [] ->
      let e = List.hd expr in
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, List.tl expr)
  | Cil.TPtr (typ, attr) when expr <> [] -> (
      let e = List.hd expr in
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      let actual_typ = Cil.unrollTypeDeep typ in
      match actual_typ with
      | Cil.TFun (_, _, _, _) ->
          (* function pointer *)
          ( Cil.SingleInit (Cil.CastE (Cil.TPtr (actual_typ, attr), e)),
            List.tl expr )
      | _ -> (Cil.SingleInit e, List.tl expr) )
  (* common *)
  | Cil.TComp (ci, _) ->
      (* struct in struct *)
      mk_struct_init expr scope loc fi.Cil.ftype ci
  | Cil.TNamed (typeinfo, attr) ->
      let is_struct typ =
        match typ with Cil.TComp (ci, _) -> true | _ -> false
      in
      if is_struct typeinfo.ttype = true then
        let tcomp = get_compinfo typeinfo.ttype in
        mk_struct_init expr scope loc typeinfo.ttype tcomp
      else if expr <> [] = true then
        let e = List.hd expr in
        let _, expr_opt = trans_expr scope None loc ADrop e in
        let e = Option.get expr_opt in
        (Cil.SingleInit e, List.tl expr)
      else (Cil.SingleInit (Cil.CastE (typeinfo.ttype, Cil.integer 0)), [])
  | Cil.TArray (arr_type, arr_exp, _) ->
      let len_exp = Option.get arr_exp in
      let arr_len =
        match len_exp with
        | Const c -> (
            match c with
            | CInt64 (v, _, _) -> Int64.to_int v
            | _ -> failwith "not expected" )
        | _ -> failwith "not expected"
      in
      let empty_list = List.init arr_len (fun idx -> idx) in
      let inits, expr_remainders, _ =
        List.fold_left
          (fun (inits, expr_remainders, o) _ ->
            if expr <> [] = true && List.length expr_remainders <> 0 = true then
              let e = List.hd expr_remainders in
              let _, expr_opt = trans_expr scope None loc ADrop e in
              let e = Option.get expr_opt in
              let init = Cil.SingleInit e in
              let init_with_idx =
                (Cil.Index (Cil.integer o, Cil.NoOffset), init)
              in
              (init_with_idx :: inits, List.tl expr_remainders, o + 1)
            else
              let init = Cil.SingleInit (Cil.CastE (arr_type, Cil.integer 0)) in
              let init_with_idx =
                (Cil.Index (Cil.integer o, Cil.NoOffset), init)
              in
              (init_with_idx :: inits, expr_remainders, o + 1))
          ([], expr, 0) empty_list
      in
      (Cil.CompoundInit (fi.Cil.ftype, List.rev inits), expr_remainders)
  | Cil.TFun (_, _, _, _) when expr <> [] -> failwith "not expected"
  | Cil.TEnum (einfo, _) when expr <> [] ->
      let e = List.hd expr in
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let e = Option.get expr_opt in
      (Cil.SingleInit e, List.tl expr)
  | Cil.TVoid _ when expr <> [] -> failwith "not expected"
  | Cil.TBuiltin_va_list _ when expr <> [] -> failwith "not expected"
  (* Can't reach below patterns *)
  | Cil.TInt (_, _)
  | Cil.TFloat (_, _)
  | Cil.TPtr (_, _)
  | Cil.TFun (_, _, _, _)
  | Cil.TEnum (_, _)
  | Cil.TVoid _ | Cil.TBuiltin_va_list _ ->
      failwith "not expected"

and mk_struct_init expr scope loc typ ci =
  let expr = ref expr in
  let union_flag = ref false in
  let fis = ref [] in
  let el =
    List.fold_left
      (fun (inits, idx) nfi ->
        let nfi = List.nth ci.cfields idx in

        if !union_flag = true then (inits, idx) (* if union *)
        else if !expr <> [] = true then (
          if (* if expression is given *)
             nfi.fcomp.cstruct = false then (
            let e = List.hd !expr in
            let _, expr_opt = trans_expr scope None loc ADrop e in
            let e = Option.get expr_opt in
            let init = Cil.SingleInit e in
            ignore (fis := nfi :: !fis);
            ignore (expr := List.tl !expr);
            ignore (union_flag := true);
            (init :: inits, idx + 1) )
          else
            let init, expr_remainders = mk_init !expr scope loc nfi in
            ignore (fis := nfi :: !fis);
            ignore (expr := expr_remainders);
            (init :: inits, idx + 1) )
        else if (* if expression is not given *)
                nfi.fcomp.cstruct = false then (
          let init = Cil.SingleInit (Cil.integer 0) in
          ignore (fis := nfi :: !fis);
          ignore (union_flag := true);
          (init :: inits, idx + 1) )
        else
          let init, _ = mk_init !expr scope loc nfi in
          ignore (fis := nfi :: !fis);
          (init :: inits, idx + 1))
      ([], 0) ci.cfields
  in
  let inits =
    List.fold_left2
      (fun fields_offset init fi ->
        (Cil.Field (fi, Cil.NoOffset), init) :: fields_offset)
      [] (fst el) !fis
  in
  (Cil.CompoundInit (typ, inits), !expr)

let rec trans_global_init scope loc (e : C.Ast.expr) =
  let typ = type_of_expr e |> trans_type scope in
  match (e.C.Ast.desc, typ) with
  | C.Ast.InitList el, Cil.TArray (arr_typ, arr_exp, attr) ->
      let len_exp = Option.get arr_exp in
      let arr_len =
        match len_exp with
        | Const c -> (
            match c with
            | CInt64 (v, _, _) -> Int64.to_int v
            | _ -> failwith "not expected" )
        | _ -> failwith "not expected"
      in
      let el =
        if List.length el > arr_len then BatList.take arr_len el else el
      in
      let init_list, _ =
        List.fold_left
          (fun (r, o) i ->
            let _, init = trans_global_init scope loc i in
            (r @ [ (Cil.Index (Cil.integer o, Cil.NoOffset), init) ], o + 1))
          ([], 0) el
      in
      (typ, Cil.CompoundInit (typ, init_list))
  | C.Ast.InitList el, Cil.TNamed (typeinfo, _)
    when is_struct typeinfo.ttype = true ->
      let ci = get_compinfo typeinfo.ttype in
      let inits, _ = mk_struct_init el scope loc typ ci in
      (typ, inits)
  | C.Ast.InitList el, Cil.TComp (ci, _) ->
      let inits, _ = mk_struct_init el scope loc typ ci in
      (typ, inits)
  | C.Ast.InitList el, _ ->
      let e = List.nth el 0 in
      (*accept only first scalar and ignore reminader*)
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let expr = Option.get expr_opt in
      (typ, Cil.SingleInit expr)
  | _ ->
      let _, expr_opt = trans_expr scope None loc ADrop e in
      let expr = Option.get expr_opt in
      (typ, Cil.SingleInit expr)

and trans_uninits ?(arr_len = 0) scope loc fi =
  match fi.Cil.ftype with
  | Cil.TComp (ci, _) ->
      (* struct in struct *)
      let fis = ref [] in
      let el =
        List.fold_left
          (fun (inits, idx) nfi ->
            let nfi = List.nth ci.cfields idx in
            let init, fi' = trans_uninits scope loc nfi in
            fis := fi' @ !fis;
            (init @ inits, idx + 1))
          ([], 0) ci.cfields
      in
      (fst el, !fis)
  | Cil.TInt (ikind, _) -> ([ Cil.SingleInit (Cil.kinteger ikind 0) ], [ fi ])
  | Cil.TFloat (fkind, _) ->
      ([ Cil.SingleInit (Cil.Const (Cil.CReal (0., fkind, None))) ], [ fi ])
  | Cil.TPtr (typ, _) ->
      ([ Cil.SingleInit (Cil.CastE (TPtr (typ, []), Cil.integer 0)) ], [ fi ])
  | Cil.TNamed (typeinfo, _) ->
      ([ Cil.SingleInit (Cil.CastE (typeinfo.ttype, Cil.integer 0)) ], [ fi ])
  | Cil.TArray (arr_type, arr_exp, _) ->
      let init = mk_uninit_arr_remainder fi.ftype in
      let fis =
        List.init (List.length init) (fun x -> x)
        |> List.fold_left (fun arr_fieldinfos _ -> fi :: arr_fieldinfos) []
      in
      (init, fis)
  | Cil.TFun (_, _, _, _) -> failwith "not expected"
  | Cil.TEnum (einfo, _) -> ([ Cil.SingleInit (Cil.integer 0) ], [ fi ])
  | Cil.TVoid _ | TBuiltin_va_list _ -> failwith "not expected"

let failwith_decl (decl : C.Ast.decl) =
  match decl.C.Ast.desc with
  | C.Ast.RecordDecl _ -> failwith "record decl"
  | _ -> failwith "unknown decl"

class replaceGotoVisitor gotos labels =
  object
    inherit Cil.nopCilVisitor

    method! vstmt stmt =
      match stmt.Cil.skind with
      | Cil.Goto (placeholder, loc) -> (
          match Chunk.GotoMap.find placeholder gotos with
          | label ->
              let target =
                try Chunk.LabelMap.find label labels
                with Not_found ->
                  failwith
                    ( CilHelper.s_location loc ^ ": label " ^ label
                    ^ " not found" )
              in
              stmt.Cil.skind <- Cil.Goto (target, loc);
              Cil.DoChildren
          | exception Not_found -> Cil.DoChildren )
      | _ -> Cil.DoChildren
  end

let trans_function_body scope fundec body =
  let chunk = trans_block scope fundec body in
  let vis = new replaceGotoVisitor chunk.Chunk.gotos chunk.Chunk.labels in
  {
    Cil.battrs = [];
    bstmts = List.map (Cil.visitCilStmt vis) chunk.Chunk.stmts;
  }

let trans_decl_attribute decl =
  let attrs = ref [] in
  ignore
    (C.visit_children (C.Ast.cursor_of_node decl) (fun c p ->
         ( if C.get_cursor_kind c |> C.is_attribute then
           match C.ext_attr_get_kind c with
           | C.NoThrow ->
               attrs := Cil.addAttribute (Cil.Attr ("nothrow", [])) !attrs
           | C.GNUInline ->
               attrs := Cil.addAttribute (Cil.Attr ("gnu_inline", [])) !attrs
           | _ -> () );
         C.Recurse));
  !attrs

let rec trans_global_decl scope (decl : C.Ast.decl) =
  let loc = trans_location decl in
  let storage = trans_storage decl in
  match decl.desc with
  | C.Ast.Function fdecl when fdecl.body = None ->
      let name = string_of_declaration_name fdecl.name in
      let typ = trans_function_type scope fdecl.C.Ast.function_type in
      let svar, scope = find_global_variable scope name typ in
      svar.vstorage <- storage;
      svar.vattr <- trans_decl_attribute decl;
      ([ Cil.GVarDecl (svar, loc) ], scope)
  | C.Ast.Function fdecl ->
      let name = string_of_declaration_name fdecl.name in
      let typ = trans_function_type scope fdecl.C.Ast.function_type in
      let svar, scope = find_global_variable scope name typ in
      let fundec = { Cil.dummyFunDec with svar } in
      let scope = Scope.enter scope in
      let scope = trans_params scope fdecl.function_type.parameters fundec in
      fundec.svar.vstorage <- storage;
      fundec.svar.vattr <- trans_decl_attribute decl;
      fundec.svar.vinline <-
        C.Ast.cursor_of_node decl |> C.cursor_is_function_inlined;
      fundec.sbody <- trans_function_body scope fundec (Option.get fdecl.body);
      let scope = Scope.exit scope in
      ([ Cil.GFun (fundec, loc) ], scope)
  | C.Ast.Var vdecl when vdecl.var_init = None ->
      let typ = trans_type scope vdecl.var_type in
      let vi, scope = find_global_variable scope vdecl.var_name typ in
      vi.vstorage <- storage;
      ([ Cil.GVarDecl (vi, loc) ], scope)
  | C.Ast.Var vdecl ->
      let typ = trans_type scope vdecl.var_type in
      let vi, scope = find_global_variable scope vdecl.var_name typ in
      vi.vstorage <- storage;
      let e = Option.get vdecl.var_init in
      let _, init' = trans_global_init scope loc e in
      let init = { Cil.init = Some init' } in
      ([ Cil.GVar (vi, init, loc) ], scope)
  | C.Ast.RecordDecl rdecl when rdecl.C.Ast.complete_definition ->
      let is_struct = rdecl.keyword = C.Struct in
      let globals, scope =
        List.fold_left
          (fun (globals, scope) decl ->
            let gs, scope = trans_global_decl scope decl in
            (globals @ gs, scope))
          ([], scope) rdecl.fields
      in
      let callback compinfo =
        List.fold_left
          (fun fl (decl : C.Ast.decl) ->
            match decl.C.Ast.desc with
            | C.Ast.Field _ -> fl @ [ trans_field_decl scope compinfo decl ]
            | _ -> fl)
          [] rdecl.fields
      in
      let name =
        if rdecl.name = "" then new_record_id is_struct else rdecl.name
      in
      let compinfo = Cil.mkCompInfo is_struct name callback [] in
      compinfo.cdefined <- true;
      if Scope.mem_typ name scope then (
        let typ = Scope.find_type name scope in
        let prev_ci = get_compinfo typ in
        prev_ci.cfields <- compinfo.cfields;
        (globals @ [ Cil.GCompTag (prev_ci, loc) ], scope) )
      else
        let typ = Cil.TComp (compinfo, []) in
        let scope = Scope.add_type rdecl.name typ scope in
        (globals @ [ Cil.GCompTag (compinfo, loc) ], scope)
  | C.Ast.RecordDecl rdecl ->
      let is_struct = rdecl.keyword = C.Struct in
      let name =
        if rdecl.name = "" then new_record_id is_struct else rdecl.name
      in
      if Scope.mem_typ name scope then
        let typ = Scope.find_type name scope in
        let prev_ci = get_compinfo typ in
        ([ Cil.GCompTagDecl (prev_ci, loc) ], scope)
      else
        let callback compinfo = [] in
        let compinfo = Cil.mkCompInfo is_struct name callback [] in
        let typ = Cil.TComp (compinfo, []) in
        let scope = Scope.add_type rdecl.name typ scope in
        ([ Cil.GCompTagDecl (compinfo, loc) ], scope)
  | TypedefDecl tdecl ->
      let ttype = trans_type scope tdecl.underlying_type in
      let tinfo = { Cil.tname = tdecl.name; ttype; treferenced = false } in
      let scope = Scope.add_type tdecl.name (Cil.TNamed (tinfo, [])) scope in
      ([ Cil.GType (tinfo, loc) ], scope)
  | EnumDecl edecl ->
      let eitems, scope, _ =
        List.fold_left
          (fun (eitems, scope, next) (c : C.Ast.enum_constant) ->
            let value = C.Enum_constant.get_value c |> Cil.integer in
            let scope =
              Scope.add c.desc.constant_name (EnvData.EnvEnum value) scope
            in
            (eitems @ [ (c.desc.constant_name, value, loc) ], scope, next))
          ([], scope, Cil.zero) edecl.constants
      in
      let einfo =
        {
          Cil.ename = edecl.name;
          eitems;
          eattr = [];
          ereferenced = false;
          ekind = Cil.IInt;
        }
      in
      let scope = Scope.add_type edecl.name (Cil.TEnum (einfo, [])) scope in
      ([ Cil.GEnumTag (einfo, loc) ], scope)
  | Field _ | EmptyDecl | AccessSpecifier _ | Namespace _ | UsingDirective _
  | UsingDeclaration _ | Constructor _ | Destructor _ | LinkageSpec _
  | TemplateTemplateParameter _ | Friend _ | NamespaceAlias _ | Directive _
  | StaticAssert _ | TypeAlias _ | Decomposition _
  | UnknownDecl (_, _) ->
      ([], scope)
  | TemplateDecl _ | TemplatePartialSpecialization _ | CXXMethod _ ->
      failwith "Unsupported C++ features"

and trans_field_decl scope compinfo (field : C.Ast.decl) =
  let floc = trans_location field in
  match field.C.Ast.desc with
  | C.Ast.Field fdecl ->
      let typ = trans_type ~compinfo:(Some compinfo) scope fdecl.qual_type in
      (fdecl.name, typ, None, [], floc)
  | _ -> failwith_decl field

let initialize_builtins scope =
  H.fold
    (fun name (rtyp, argtyps, isva) scope ->
      let argtyps = Some (List.map (fun at -> ("", at, [])) argtyps) in
      create_new_global_variable scope name (Cil.TFun (rtyp, argtyps, isva, []))
      |> snd)
    Cil.builtinFunctions scope

let parse fname =
  let options = { C.Ast.Options.default with ignore_implicit_cast = false } in
  let tu = C.Ast.parse_file ~options fname in
  let scope = initialize_builtins (Scope.create ()) in
  let globals =
    List.fold_left
      (fun (globals, scope) decl ->
        let new_globals, scope = trans_global_decl scope decl in
        (globals @ new_globals, scope))
      ([], scope) tu.desc.items
    |> fst
  in
  {
    Cil.fileName = fname;
    Cil.globals;
    Cil.globinit = None;
    Cil.globinitcalled = false;
  }
