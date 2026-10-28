module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility.Curtis
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi.Irreducibility

/-!
# Curtis's input for the actual binary end-parabolic action

Apply the binary Curtis theorem to the finite-dimensional irreducible
dual, then use the existing Timmesfeld theorem for the literal radical
fixed space and Levi quotient. Only the four group-geometric premises
remain; no fixed-line, cyclicity, or degree premise is retained.

Source: GLS, Volume 3, Theorem 2.8.11, printed pp.95–96,
`refs/KGroup/GLS3/chapter2.tex`. The independent parabolic-geometry
construction and final unconditional assembly belong to the end-node
irreducibility development.
-/

public section

namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi
open Representation Irreducibility

/-- Curtis discharges the representation-theoretic premise of the actual binary Timmesfeld application. -/
theorem action_irreducible_of_parabolic_geometry
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (σ : Representation (ZMod 2) SL5TenDimensional.Group V) [IsIrreducible σ]
    (e : Fin 2)
    (hRU : radicalImage e ≤ upper)
    (hUL : upper ≤ radicalImage e ⊔ leviSubgroup e)
    (hTL : lower ≤ oppositeRadical e ⊔ leviSubgroup e)
    (hq : Function.Surjective (leviToQuotient e)) : IsIrreducible (action σ e) := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  let : IsIrreducible σ.dual := isIrreducible_dual
  exact action_irreducible_of_unipotent_inputs σ e (curtisInput σ.dual) hRU hUL hTL hq

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FiveDisplacement.Inner.EndNode.Levi
