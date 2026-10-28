module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.Actions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.LocalAlgebra
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.RankComparison

/-!
# Constructing the strong offender from the symmetric cover

The final argument of 15.3.49(n) combines three independently meaningful
inputs: the cross-centralization rank bound, the symmetric centralizer-cover
implication, and `L = [L,Uγ]` in `H = L(Y₀T)`. If the actual star image of
`Vγ` is not strong, rank-nullity forces all three equalities used in the book.
The cover then makes `Uγ` trivial on `V_H/U_H`; commutator generation makes
`L` trivial there, contradicting the strict span inequality from (m).

This is a conditional construction, not the completed source theorem. The
geometric cover implication and the component-generation premise must still
be derived in their respective parts of the proof. Best-offender status,
required in addition to strict offending for the source term “strong FF-star
offender”, is also a separate conclusion of (h).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1144.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative

variable {G : Type*} [Group G] [Finite G]

/-- The strict offender is constructed on `U_H/Z` for the actual actor
`H/O₂(H)`. The symmetry premise is an implication from explicit equalities,
not an assumed strong offender or contradiction. -/
theorem strong_from_symmetric_cover
    (H L R V ZS Z Ug Vg : Subgroup G)
    [IsElementaryAbelian 2 (localSpan ZS H)]
    (action : SectionAction H (localSpan ZS H) Z)
    (D : Submodule (ZMod 2) (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H))))
    (hUg : IsElementaryTwo (starImage H Ug))
    (hVg : IsElementaryTwo (starImage H Vg))
    (hUV : Ug ≤ Vg) (hVgH : Vg ≤ H)
    (hfixed : D ≤ fixedSpace action.representation (starImage H Vg))
    (hrank : Module.finrank (ZMod 2)
      (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) ≤
        rank (starImage H Ug))
    (hsymmetry : D = fixedSpace action.representation (starImage H Vg) →
      starImage H Ug = starImage H Vg →
      rank (starImage H Ug) = Module.finrank (ZMod 2)
        (Additive (localSpan ZS H ⧸ Z.subgroupOf (localSpan ZS H)) ⧸ D) →
      localSpan V H = localSpan ZS H ⊔
        (localSpan V H ⊓ centralizer (Ug : Set G)))
    (hH : H = L ⊔ R) (hZS : ZS ≤ V)
    (hRV : R ≤ normalizer (V : Set G)) (hVH : localSpan V H ≤ H)
    (hL : L = ⁅L, Ug⁆)
    (hproper : localSpan ZS H ⊔ V < localSpan V H) :
    IsStrongOffender action.representation (starImage H Vg) := by
  by_contra hnot
  have hstar : starImage H Ug ≤ starImage H Vg :=
    map_mono (fun _ hx => hUV hx)
  obtain ⟨hD, hUVstar, heqdim⟩ := equalities_of_not_strong action.representation D
    (starImage H Ug) (starImage H Vg) hUg hVg hstar hfixed hrank hnot
  have hcover := hsymmetry hD hUVstar heqdim
  have heq := localSpan_eq_sup_of_symmetric_cover H L R V ZS Ug hH hZS hRV hVH
    (hUV.trans hVgH) hL hcover
  exact hproper.ne heq.symm

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
