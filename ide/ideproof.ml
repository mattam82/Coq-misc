(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2010     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)


(* tag is the tag to be hooked, item is the item covered by this tag, make_menu
 *  * is the template for building menu if needed, sel_cb is the callback if
 *  there
 *   * is a selection o said menu, hover_cb is the callback when there is only
 *    * hovering *)
let hook_tag_cb tag menu_content sel_cb hover_cb =
  ignore (tag#connect#event ~callback:
            (fun ~origin evt it ->
               let iter = new GText.iter it in
               let start = iter#backward_to_tag_toggle (Some tag) in
               let stop = iter#forward_to_tag_toggle (Some tag) in
               match GdkEvent.get_type evt with
                 | `BUTTON_PRESS ->
                     let ev = GdkEvent.Button.cast evt in
                     if (GdkEvent.Button.button ev) <> 3 then false else begin
                       let ctxt_menu = GMenu.menu () in
                       let factory = new GMenu.factory ctxt_menu in
                       List.iter
                         (fun (text,cmd) -> ignore (factory#add_item text ~callback:(sel_cb cmd)))
                         menu_content;
                       ctxt_menu#popup ~button:3 ~time:(GdkEvent.Button.time ev);
                       true
                     end
                 | `MOTION_NOTIFY ->
                     hover_cb start stop; false
                 | _ -> false))

let mode_tactic sel_cb (proof:GText.view) = function
  | [] -> assert false
  | { Ide_intf.goal_hyp = hyps; Ide_intf.goal_ccl = cur_goal; } :: rem_goals ->
      let on_hover sel_start sel_stop =
        proof#buffer#remove_tag
          ~start:proof#buffer#start_iter
          ~stop:sel_start
          Tags.Proof.highlight;
        proof#buffer#remove_tag
          ~start:sel_stop
          ~stop:proof#buffer#end_iter
          Tags.Proof.highlight;
        proof#buffer#apply_tag ~start:sel_start ~stop:sel_stop Tags.Proof.highlight
      in
      let goals_cnt = List.length rem_goals + 1 in
      let head_str = Printf.sprintf "%d subgoal%s\n" goals_cnt (if 1 < goals_cnt then "" else "s") in
      (* FIXME : add menu entries *)
      let insert_hyp h =
        let menu = [] in
        let tags = if menu <> [] then
          let tag = proof#buffer#create_tag [] in
          hook_tag_cb tag menu sel_cb on_hover;
          [tag]
          else []
        in
        proof#buffer#insert ~tags (h^"\n")
      in
      let insert_goal g menu index total =
        let tags = if menu <> [] then
          let tag = proof#buffer#create_tag [] in
          hook_tag_cb tag menu sel_cb on_hover;
          [tag]
          else []
        in
        proof#buffer#insert (Printf.sprintf
                               "\n______________________________________(%d/%d)\n" index total);
        proof#buffer#insert ~tags (g^"\n")
      in
      proof#buffer#insert head_str;
      List.iter insert_hyp hyps;
      (* FIXME : add menu entries *)
      insert_goal cur_goal [] 1 goals_cnt;
      let fold_goal i _ { Ide_intf.goal_ccl = g } = insert_goal g [] i goals_cnt in
      Minilib.list_fold_left_i fold_goal 2 () rem_goals;
      ignore(proof#buffer#place_cursor  
        ~where:((proof#buffer#get_iter_at_mark `INSERT)#backward_lines (3*goals_cnt - 2)));
      ignore(proof#scroll_to_mark `INSERT)


let mode_cesar (proof:GText.view) = function
  | [] -> assert false
  | { Ide_intf.goal_hyp = hyps; Ide_intf.goal_ccl = cur_goal; } :: _ ->
      proof#buffer#insert "    *** Declarative Mode ***\n";
      List.iter
        (fun hyp -> proof#buffer#insert (hyp^"\n"))
        hyps;
      proof#buffer#insert "______________________________________\n";
      proof#buffer#insert ("thesis := \n "^cur_goal^"\n");
      ignore (proof#scroll_to_iter (proof#buffer#get_iter_at_mark `INSERT))

let display mode (view:GText.view) goals =
  view#buffer#set_text "";
  match goals with
    | Ide_intf.No_current_proof -> ()
    | Ide_intf.Proof_completed ->
      view#buffer#insert "Proof Completed."
    | Ide_intf.Unfocused_goals l ->
      view#buffer#insert "This subproof is complete, but there are still unfocused goals:\n\n";
      let iter goal =
        let msg = Printf.sprintf "%s\n" goal.Ide_intf.goal_ccl in
        view#buffer#insert msg
      in
      List.iter iter l
    | Ide_intf.Uninstantiated_evars el ->
      view#buffer#insert "No more subgoals but non-instantiated existential variables:\n\n";
      let iter evar =
        let msg = Printf.sprintf "%s\n" evar in
        view#buffer#insert msg
      in
      List.iter iter el
    | Ide_intf.Goals g ->
      mode view g
