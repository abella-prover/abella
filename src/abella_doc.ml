(*
 * Author: Kaustuv Chaudhuri <kaustuv.chaudhuri@inria.fr>
 * Copyright (C) 2022  Inria (Institut National de Recherche
 *                     en Informatique et en Automatique)
 * See LICENSE for licensing details.
 *)

(* Generate documentation for a collection of Abella .thm files *)

(******************************************************************************)

let doc_template root =
  let root = Filename.basename root in
  let thmfile = root ^ ".thm" in
  let jsonfile = root ^ ".json" in
  {|<!DOCTYPE html>
<html lang="en">

<head>
  <meta charset="UTF-8">
  <meta http-equiv="X-UA-Compatible" content="IE=edge">
  <meta name="viewport" content="width=device-width, initial-scale=1.0">
  <title>|} ^ root ^ {|</title>
  <script src="https://code.jquery.com/jquery-3.6.0.min.js"
    integrity="sha256-/xUj+3OJU5yExlq6GSYGSHk7tPXikynS7ogEvDej/m4=" crossorigin="anonymous"></script>
  <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/@fancyapps/ui@4.0/dist/fancybox.css" />
  <!-- <link rel="stylesheet" href="https://abella-prover.org/examples/css/style.css" /> -->
  <link rel="stylesheet" href="/css/style.css">
</head>

<body>
  <div class="w-11/12 mx-auto mb-2">
    <a href="https://abella-prover.org/index.html"><img src="https://abella-prover.org/images/logo-small.png"></a>
    <h1 class="text-lg font-mono text-[maroon]">
      |} ^ root ^ {|.thm
    </h1>
  </div>
  <div class="w-11/12 mx-auto mt-2 border-rose-300 border-2">
    <div id="container">
      <div id="thmbox"
        class="font-mono italic bg-yellow-50 leading-tight w-full h-full px-2 whitespace-pre overflow-auto text-green-800">
        &nbsp;
      </div>
    </div>
  </div>

  <script src="https://cdn.jsdelivr.net/npm/@fancyapps/ui@4.0/dist/fancybox.umd.js"></script>
  <script>
    const top_builtin_re = /\b(Import|Specification|Query|Set|Show|Close)\b/g;
    const top_command_re = /\b((?:Co)?Define|Theorem|Split|by|Kind|Type)\b/g;
    const proof_command_re = /\b(abbrev|all|apply|assert|backchain|case|clear|(?:co)?induction|cut|inst|intros|keep|left|monotone|on|permute|rename|right|search|split(?:\*)?|to|unabbrev|unfold|with|witness)\b/g;
    const proof_special_re = /\b(skip|undo|abort)\b/g;
    const type_re = /\b(list|prop|o)\b/g;
    const term_re = /\b(forall|exists|nabla|pi|sigma|sig|module|end)\b/g;
    const op_re = /(=(?:&gt;)?|\|-|-&gt;|\\\/?|\/\\|\{|\})/g;
    const bg = (count) => (count & 1) === 0 ? "bg-slate-50" : "bg-slate-100";
    const seqToStr = (obj, doInsts) => {
      let repr = '<div class="flex flex-col max-w-xl whitespace-normal ml-2 bg-rose-50">';
      if (obj.name && obj.name.length > 0) {
        repr += `<div><span class="mb-3 text-rose-600 font-sans text-[.8em]">Subgoal ${obj.name}</span></div>`;
      }
      let count = 0;
      if (obj.vars && obj.vars.length > 0) {
        const vars = [], insts = [];
        obj.vars.forEach((v) => {
          if (v[1]) insts.push(v);
          else vars.push(v[0]);
        });
        if (vars.length)
          repr += `<div class="${bg(count++)}"><code>Variables: ${vars.join(" ")}</code></div>`;
        if (doInsts)
          insts.forEach((v) => {
            repr += `<div class="${bg(count++)}"><code>  ${v[0]} &larr; ${v[1]}</code></div>`;
          });
      }
      obj.hyps.forEach((h) => {
        repr += `<div class="${bg(count++)}"><code><span class="text-rose-600">${h[0]}</span>: ${h[1]}</code></div>`;
      });
      repr += `<div class="border-t-2 border-t-rose-600"></div>`;
      repr += `<div>&nbsp;<code>${obj.goal}</code></div>`;
      if (obj.more > 0)
        repr += `<div class="font-sans mt-1 text-[.8em]">(+ ${obj.more} more subgoal${obj.more > 1 ? "s" : ""})</div>`;
      repr += '</div>';
      return repr;
    }
    const make_safe = (str) => new Option(str).innerHTML;
    const getStuff = async () => {
      const init = {
        method: 'GET',
        cache: 'no-store',
        headers: { pragma: 'no-cache' }
      };
      let thm_text = await fetch('|} ^ thmfile ^ {|', init).then(resp => resp.text());
      let styled_slice = (start, stop, type) => {
        let txt = make_safe(thm_text.slice(start, stop));
        if (type) {
          // wash terms and types
          txt = txt
            .replaceAll(op_re, `<span style="color:#9d1f1f;">$1</span>`)
            .replaceAll(term_re, `<span style="color:#9d1f1f;">$1</span>`)
            .replaceAll(type_re, `<span style="color:#1640b0;">$1</span>`);
          if (type === "top_command")
            txt = txt
              .replaceAll(top_builtin_re, `<span style="color:#338fff;">$1</span>`)
              .replaceAll(top_command_re, `<span style="color:#9d1f1f;font-weight:bold;">$1</span>`);
          if (type === "proof_command")
            txt = txt
              .replaceAll(proof_special_re, `<span style="background-color:#9d1f1f;color:#c0965b;font-weight:bold;">$1</span>`)
              .replaceAll(proof_command_re, `<span style="color:#9d1f1f;font-style:italic;">$1</span>`);
        }
        return txt;
      };
      let run_data = await fetch('|} ^ jsonfile ^ {|', init).then(resp => resp.json());
      const thm_box = $('#thmbox');
      thm_box.empty();
      let last_pos = 0;
      let cmd_map = new Map();
      run_data.forEach((elm) => {
        if (elm.range) {
          const [start, , , stop, ,] = elm.range;
          const chunk_div = $(`<div id="chunk-${elm.id}" class="inline">`);
          if (last_pos < start) {
            $(chunk_div).append($(`<span>${styled_slice(last_pos, start)}</span>`));
            last_pos = start;
          }
          const ul = elm.type === "proof_command" ? "text-rose-700 not-italic text-sm" : "leading-snug not-italic text-[#000000]";
          const cmd = $(`<div class="abella-command inline-block ${ul} cursor-default hover:bg-rose-200/60">${styled_slice(start, stop, elm.type)}</div>`);
          $(cmd).data('obj', elm);
          cmd_map.set(elm.id, cmd);
          $(chunk_div).append(cmd);
          last_pos = stop;
          $(thm_box).append(chunk_div);
        }
      });
      let thm_cmds = new Set();
      cmd_map.forEach((cmd, id) => {
        const obj = $(cmd).data('obj');
        if (obj && obj.type && obj.type == 'proof_command') {
          thm_cmds.add(obj.thm_id);
          const thm_cmd = cmd_map.get(obj.thm_id);
          $(thm_cmd).parent().append($(cmd).parent());
        }
      });
      thm_cmds.forEach((thm_id) => {
        const thm_cmd = cmd_map.get(thm_id);
        const btn = $('<button class="font-sans text-[.75em] text-green-700 hover:text-green-700/70 hover:underline">[collapse proof]</button>');
        $(btn).data('state', true);
        $(btn).click((ev) => {
          const cur_state = $(btn).data('state');
          $(btn).data('state', !cur_state);
          let cur = $(btn).next();
          while (cur.length) {
            if (cur_state) cur.hide()
            else cur.show();
            cur = cur.next();
          }
          $(btn).text(cur_state ? '[expand proof]' : '[collapse proof]');
        });
        $(thm_cmd).after(btn);
        $(thm_cmd).after('<span>\n</span>');
        $(btn).click();
      });
      cmd_map.forEach((cmd, id) => {
        const obj = $(cmd).data('obj');
        let descr = "<div class=\"whitespace-pre font-mono text-sm overflow-auto\">";
        if (obj.type === "top_command") {
          descr += `Abella &lt; <strong>${$(cmd).text()}</strong>`;
        } else {
          descr += `${seqToStr(obj.start_state)}\n`;
          descr += `${obj.theorem} &lt; <strong>${$(cmd).text()}</strong>`;
          if (obj.end_state)
            descr += `\n\n${seqToStr(obj.end_state, obj.start_state.name === obj.end_state.name)}`;
          else
            descr += '\n\nProof completed.';
        }
        descr += "</div>";
        let flobj = $(`<div class="border-2 border-rose-800 bg-white p-2 shadow-lg shadow-rose-600/40">`);
        $(flobj).css({
          'position': 'absolute',
          'z-index': '10100',
          'display': 'none'
        });
        $(flobj).html(descr);
        $('#container').append(flobj);
        // setup the actions
        $(cmd).on("mousemove", function (ev) {
          const fl_width = $(flobj).outerWidth(true), fl_height = $(flobj).outerHeight(true);
          const w_width = $(window).width(), w_height = $(window).height();
          const p_x = ev.pageX, p_y = ev.pageY;
          const d = 10;
          const css = { display: 'block' };
          if (p_x + fl_width + d <= w_width) css.left = p_x + d;
          else css.left = w_width - fl_width;
          if (p_y + fl_height + d <= w_height) css.top = p_y + d;
          else if (p_y - fl_height - d >= 0) css.top = p_y - fl_height - d;
          else css.display = 'none'; // float doesn't fit above or below
          $(flobj).css(css);
        }).on("mouseleave", function () {
          $(flobj).css({ 'display': 'none' });
        }).on("click", function () {
          $(flobj).css({ 'display': 'none' });
          Fancybox.show([{ src: $(flobj).html(), type: "html" }]);
        });
      });
    }
    getStuff();
  </script>
</body>

</html>|}
;;

(******************************************************************************)

open Extensions

let abella =
  let dir = Filename.dirname Sys.executable_name in
  let ab1 = Filename.concat dir "abella" in
  let ab2 = Filename.concat dir "abella.exe" in
  ref @@ if Sys.file_exists ab1 then ab1 else ab2
;;

let options = Arg.[
    "-a", Set_string abella,
    Printf.sprintf "PROG Run PROG as abella (default: %s)" !abella ;
  ] |> Arg.align

let input_files : string list ref = ref []

let add_input_file file =
  input_files := file :: !input_files

let usage_message = Printf.sprintf "%s [options] <theorem-file> ..." begin
    if !Sys.interactive then "abella_doc" else Filename.basename Sys.executable_name
  end

let main () =
  Arg.parse options add_input_file usage_message ;
  let dep_tab = Hashtbl.create (List.length !input_files) in
  List.iter begin fun thmfile ->
    match Filename.chop_suffix thmfile ".thm" with
    | exception Invalid_argument _ ->
        failwithf "Invalid file %S; All input files must end in .thm" thmfile
    | base ->
        if not (Hashtbl.mem dep_tab thmfile) then
          let (_, deps) = Depend.get_thm_depend base in
          Hashtbl.replace dep_tab base deps
  end !input_files ;
  let seen = Hashtbl.create (List.length !input_files) in
  let topo = ref [] in
  let rec toproc file =
    if Hashtbl.mem seen file then () else begin
      Hashtbl.replace seen file () ;
      List.iter toproc (Hashtbl.find dep_tab file) ;
      topo := file :: !topo ;
    end in
  Hashtbl.iter (fun f _ -> toproc f) dep_tab ;
  List.iter begin fun root ->
    let cmd = Printf.sprintf "%s -nr -a %s.thm -o %s.json -c %s.thc"
        !abella root root root in
    Printf.printf "RUN: %s\n%!" cmd ;
    if Sys.command cmd != 0 then
      failwithf "ERROR running: %s" cmd ;
    let htmlfile = root ^ ".html" in
    let ch = open_out_bin htmlfile in
    output_string ch (doc_template root) ;
    close_out ch ;
    Printf.printf "CREATE: %s\n%!" htmlfile
  end (List.rev !topo)

let () = if not !Sys.interactive then main()
