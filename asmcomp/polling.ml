(**************************************************************************)
(*                                                                        *)
(*                                 OCaml                                  *)
(*                                                                        *)
(*   All rights reserved.  This file is distributed under the terms of    *)
(*   the GNU Lesser General Public License version 2.1, with the          *)
(*   special exception on linking described in the file LICENSE.          *)
(*                                                                        *)
(**************************************************************************)
open Mach
open Reg
open Cmm

(* constants *)
let lmax = 50
let k = 10
let e = lmax/k

let _is_addr_live i = 
  not (Reg.Set.is_empty (Reg.Set.filter (fun f -> f.typ = Cmm.Addr) i))

let insert_poll_aux _delta instr = instr
(*
    if (is_addr_live instr.live) then begin
        { instr with next = (insert_poll_aux delta instr.next) }
    end else begin
        match instr.desc with
        (* terminating condition *)
        | Iend -> instr

        (* reset counter *)
        | Iop (Ialloc _) ->
            { instr with next = (insert_poll_aux 0 instr.next) }

        (* | Iop (Imove) *)
        (* | Iop (Ispill) *)
        (* | Iop (Ireload) *)
        (*
        ->
            if (instr.Mach.arg.(0).loc = instr.Mach.res.(0).loc) then begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end else begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end
        *)

        (* call type *)
        (*
        | Iop (Icall_imm _) ->
            let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
            let poll_instr = insert_poll_instr updated_instr in
            (poll_instr.live <- Reg.Set.add ({Reg.dummy with loc = Reg.Reg 0 ; typ = Cmm.Val}) poll_instr.live);
            poll_instr
        *)
            
        | Iop (Iconst_int _)
        | Iop (Iconst_float _)
        | Iop (Iconst_symbol _)
        (* | Iop (Icall_ind _) *)
        (* | Iop (Itailcall_ind _) *)
        (* | Iop (Itailcall_imm _) *)
        (* | Iop (Iextcall _) *)
        | Iop (Istackoffset _)
        (* | Iop (Iload _) *)
        (* | Iop (Iintop _) (* signal_alloc.ml *) *)
        | Iop (Inegf)
        | Iop (Iabsf)
        | Iop (Iaddf)
        | Iop (Isubf)
        | Iop (Imulf)
        | Iop (Idivf)
        | Iop (Ifloatofint)
        | Iop (Iintoffloat)
        (* | Iop (Iname_for_debugger _) *)
        ->
            if (delta > lmax-e) then begin
                let updated_instr = { instr with next = insert_poll_aux 0 instr.next} in
                insert_poll_instr updated_instr
            end else begin
                { instr with next = insert_poll_aux (delta+1) instr.next}
            end
        
        (* other *)
        (* | Iop (Iintop_imm (_, _, is_addr_upd)) -> (* signals_alloc failing *)
            if (is_addr_upd) then begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end else begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end *)
        (*
        | Iop (Istore (_, _, is_assign)) ->
            if (is_assign) then begin
                let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
                insert_poll_instr updated_instr
            end else begin
                { instr with next = (insert_poll_aux delta instr.next) }
            end
        | Iop (Ispecific (Istore_int _)) ->
            { instr with next = (insert_poll_aux delta instr.next) }
        *)
        (* signal_alloc failing
        | Iop (Ispecific _) ->
            let updated_instr = { instr with next = insert_poll_aux delta instr.next} in
            insert_poll_instr updated_instr
        *)
        | Iop (Ipoll) ->
            assert false
        (* pass through - temp until all instructions handled *)
        | _ -> { instr with next = (insert_poll_aux delta instr.next) }
    end
*)

let insert_poll fun_body =
    insert_poll_aux (lmax-e) fun_body

let rec add_poll = function
  | Cconst_int _
  | Cconst_natint _
  | Cconst_float _
  | Cconst_symbol _
  | Cconst_pointer _
  | Cconst_natpointer _
  | Cblockheader _
  | Cvar _ as c -> c
  | Clet (id, e1, e2) ->
      Cpoll (Clet (id, add_poll e1, add_poll e2))
  | Cassign (id, e) ->
      Cpoll (Cassign (id, add_poll e))
  | Ctuple el ->
      Cpoll (Ctuple (List.map add_poll el))
  | Cop (op, el, dbg) ->
      Cpoll (Cop (op , List.map add_poll el, dbg))
  | Csequence (e1, e2) ->
      Cpoll (Csequence (add_poll e1, add_poll e2))
  | Cifthenelse (e1, e2, e3) ->
      Cpoll (Cifthenelse (add_poll e1, add_poll e2, add_poll e3))
  | Cswitch (e, i, el, dbg) ->
      Cpoll (Cswitch (add_poll e, i, Array.map add_poll el, dbg))
  | Cloop e ->
      Cpoll (Cloop (add_poll e))
  | Ccatch (r , el, e) ->
      Cpoll (Ccatch (r, List.map (fun (i,idl,exp) -> (i,idl, add_poll exp)) el, e))
  | Cexit (i, el) -> 
      Cpoll (Cexit (i, List.map add_poll el))
  | Ctrywith (e1, id, e2) ->
      Cpoll (Ctrywith (add_poll e1, id, add_poll e2))
  | Cpoll _ ->
      assert false

let cmm_fundecl f =
  { f with fun_body = add_poll f.fun_body }

let mach_fundecl (f:Mach.fundecl) =
    let new_body =
        insert_poll f.fun_body
    in
      { f with fun_body = new_body }
