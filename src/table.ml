type tag = Proved | Working of bool ref | Disproved | Unset
type t = tag ref Index.t ref

let create () = ref Index.empty

let add ~allow_eigenvar table args tag =
  table := Index.add ~allow_eigenvar !table args tag

let find table args = Index.find !table args

let print head table =
  Printf.printf "Table for %s contains (P=Proved, D=Disproved):\n" head ;
  let d = Term.const head 0 in
  Index.iter !table
    (fun t tag ->
       let t = Term.app t [d] in
       match !tag with
         | Proved    -> Format.printf " [P] %a\n" Pprint.pp_term t
         | Disproved -> Format.printf " [D] %a\n" Pprint.pp_term t
         | Unset     -> ()
         | Working _ -> assert false)

let reset x = x := Index.empty
