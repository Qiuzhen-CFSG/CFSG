module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.FixedSpaces

/-!
# Projecting the central involutions onto the component module

Set `U = [W_L,L]` and `C = C_{UZ}(L)`. Once the B.2.14 splitting
`UZ = UC` is supplied, the image of `Z` under projection onto `U` is
the actual subgroup `U ∩ ZC`. The proofs retain `C` and show
`Z ≤ Z_L C` and `C_L(Z_L) = C_L(Z)`. The natural-module alternatives
make `U ∩ C = 1`, so this is a projection along a genuine complement.

Only elementarity of `W_L` and the stated earlier splitting are used for
the containment and centralizer equality. The representation-theoretic
construction of that splitting remains with the module-alternatives proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the `Z_L` construction in 15.3.24, printed p.1129 (PDF p.1146).
-/

@[expose] public section

open Subgroup
open scoped Pointwise

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

variable {G : Type*} [Group G] (d : LocalData G)

/-- The exact central factor used in B.2.14, inside `U_L Z`. -/
abbrev centralSupplement (L : Subgroup G) : Subgroup G :=
  (spanCommutator d L ⊔ d.Z) ⊓ centralizer (L : Set G)

/-- The projected subgroup, expressed without choosing representatives
or identifying `Z` with its projection. -/
abbrev projectedCenter (L : Subgroup G) : Subgroup G :=
  spanCommutator d L ⊓ (d.Z ⊔ centralSupplement d L)

private theorem supplement_normalizes (L : Subgroup G)
    [IsElementaryAbelian 2 (d.componentSpan L)] :
    centralSupplement d L ≤ normalizer (spanCommutator d L : Set G) := by
  have hZW : d.Z ≤ d.componentSpan L :=
    (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy d.V L)
  have hCW : centralSupplement d L ≤ d.componentSpan L :=
    inf_le_left.trans (sup_le (spanCommutator_le_span d L) hZW)
  exact (hCW.trans ((d.componentSpan L).le_centralizer.trans
    (centralizer_le (spanCommutator_le_span d L)))).trans
      (Subgroup.centralizer_le_normalizer _)

/-- Every element of `Z` is a product of an element of its projected
subgroup and an element of the exact central supplement. -/
theorem center_le_projected_sup (L : Subgroup G)
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L) :
    d.Z ≤ projectedCenter d L ⊔ centralSupplement d L := by
  have hZ : d.Z ≤ spanCommutator d L ⊔ centralSupplement d L :=
    le_sup_right.trans_eq hsplit
  intro z hz
  have hprod : z ∈ (spanCommutator d L : Set G) * (centralSupplement d L : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (supplement_normalizes d L)]
    exact hZ hz
  obtain ⟨u, hu, c, hc, rfl⟩ := hprod
  have huZ : u ∈ d.Z ⊔ centralSupplement d L :=
    (mul_mem_cancel_right (mem_sup_right hc)).mp (mem_sup_left hz)
  exact mul_mem_sup (show u ∈ projectedCenter d L from ⟨hu, huZ⟩) hc

private theorem centralizer_le_of_supplement {A B C L : Subgroup G}
    (hA : A ≤ B ⊔ C) (hC : C ≤ centralizer (L : Set G)) :
    L ⊓ centralizer (B : Set G) ≤ centralizer (A : Set G) := by
  apply le_trans ?_ (centralizer_le hA)
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_right)
    (le_centralizer_iff.mp (inf_le_left.trans (le_centralizer_iff.mp hC)))

/-- The two literal relative centralizers coincide; the central
supplement is retained on both sides of the argument. -/
theorem projectedCenter_centralizer (L : Subgroup G)
    [IsElementaryAbelian 2 (d.componentSpan L)]
    (hsplit : spanCommutator d L ⊔ d.Z =
      spanCommutator d L ⊔ centralSupplement d L) :
    L ⊓ centralizer (projectedCenter d L : Set G) =
      L ⊓ centralizer (d.Z : Set G) :=
  le_antisymm
    (le_inf inf_le_left (centralizer_le_of_supplement
      (center_le_projected_sup d L hsplit) inf_le_right))
    (le_inf inf_le_left (centralizer_le_of_supplement
      (show projectedCenter d L ≤ d.Z ⊔ centralSupplement d L from inf_le_right)
      inf_le_right))

/-- In either module alternative the central supplement is disjoint
from the component module. No vanishing of the supplement is asserted. -/
theorem centralSupplement_disjoint {L : Subgroup G} (h : ModuleAlternatives d L) :
    Disjoint (spanCommutator d L) (centralSupplement d L) := by
  apply disjoint_iff.mpr
  apply eq_bot_iff.mpr
  exact (inf_le_inf_left _ (show centralSupplement d L ≤ centralizer (L : Set G)
    from inf_le_right)).trans_eq h.centralizer_eq_bot

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive

end
