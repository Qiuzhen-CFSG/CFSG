/-
The Glauberman ZJ challenge.

Imports `ZJDefs`, which imports only Mathlib. The statement below and the two
definitions of `ZJDefs` are the whole audit surface.

Glauberman's ZJ theorem: if `G` is solvable of odd order and `S` is a Sylow
`p`-subgroup of `G`, then `Z(J(S)) * O_{p'}(G)` is normal in `G`. Here `Z(J(S))`
is written as the image in `G` of the centre of `J(S)`.

The Coq formalization of the Odd Order theorem does not contain this theorem: it
proves Puig's ZL theorem in its place, in `BGappendixAB.v`.
-/

import Comparator.GlaubermanZJ.Defs

namespace ZJ

theorem glauberman_zj {G : Type*} [Group G] [IsSolvable G] (hodd : Odd (Nat.card G))
    {p : ℕ} [Fact p.Prime] (S : Sylow p G) :
    ((Subgroup.center (thompsonSubgroup S.toSubgroup)).map
        (thompsonSubgroup S.toSubgroup).subtype ⊔ pPrimeCore p G).Normal :=
  sorry

end ZJ
