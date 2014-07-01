open Term
open Uterm
open Translation

let dummy = Lexing.(dummy_pos, dummy_pos)

let judge thing cfier = UJudge (dummy, thing, cfier)
let const c ty = UCon (dummy, c, ty)
let tycon c = const c lftypety
let obcon c = const c lfobjty
let arrow a b = UImp (dummy, a, b)
let lfpi  x a b = UPi (dummy, x, a, b)
let lfapp m n = UApp (dummy, m, n)
let rec lfapps h ts = match ts with
  | [] -> h
  | t :: ts -> lfapps (lfapp h t) ts
let _type = UType dummy

let _nat = tycon "nat"
let nat  = judge _nat _type
let _z   = obcon "z"
let z    = judge _z _nat
let _s   = obcon "s"
let s    = judge _s (arrow _nat _nat)

let _ty  = tycon "ty"
let ty   = judge _ty _type
let _tm  = tycon "tm"
let tm   = judge _tm (arrow _ty _type)

let _i   = obcon "i"
let i    = judge _i _ty
let _arr = obcon "arr"
let arr  = judge _arr (arrow _ty (arrow _ty _ty))

let app  =
  judge (obcon "app") begin
    lfpi "A" _ty begin
      lfpi "B" _ty begin
        arrow (lfapp _tm (lfapps _arr [obcon "A"; obcon "B"]))
              (arrow (lfapp _tm (obcon "A"))
                     (lfapp _tm (obcon "B")))
      end
    end
  end

let lam =
  judge (obcon "lam") begin
    lfpi "A" _ty begin
      lfpi "B" _ty begin
        arrow (arrow (lfapp _tm (obcon "A"))
                 (lfapp _tm (obcon "B")))
          (lfapp _tm (lfapps _arr [obcon "A"; obcon "B"]))
      end
    end
  end

let random =
  judge (obcon "foo") (arrow (arrow _i _i) _i)
