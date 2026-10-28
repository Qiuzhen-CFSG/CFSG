module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.Elementary
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.Sections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Reciprocal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree.PairingAction.Duality
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Pairing radicals and the four-group action inputs in 14.7.70

For the literal E = V₁ Zα, both cross-commutators and both radicals on F
are proved from the original natural cover. F.9.7 is applied to the actual
relative subgroups of H with its centrality and normality conditions
discharged. The reciprocal argument uses an earlier marked actor on the
inverse-conjugate U, not an element interchanging the two endpoints.

This module also establishes the precise applicability conditions for the
genuine A.1.14: E is a four-group with two distinct involutions, and the
two source cores are the two-cores of their actual centralizers.

The remaining restricted-character realization must construct `CoreAxes`.
The full A.1.14 producer is qt-a-01-elementary-a114. Full E action, relative
normality, and generation by the embedded two-residual still require final
assembly in qt-14-07-rank-three-pairing-action. No completed 14.7.70 or
rank-three obstruction is asserted by these intermediate theorems.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
A.1.14, F.9.7, 14.5.21, and proof of 14.7.70, printed pp.23, 321, 1019, 1074.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
open Subgroup Representation Chapter12.Section08
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {d : Data T L V F W} {c : CriticalPath (L := L) F}

namespace Preliminary
variable (h : Preliminary d c)
include h

/-- The actual E satisfies the four-group condition of A.1.14. -/
theorem E_isKleinFour : IsKleinFour (E c) := by
  let := h.E_elementary
  let : Nontrivial (E c) := Finite.one_lt_card_iff_nontrivial.mp (by rw [h.E_card]; decide)
  exact ⟨h.E_card, IsElementaryAbelian.exponent_eq_prime⟩

/-- Both literal core actions have the exact nontrivial point commutator
required by A.1.14, rather than just a commutator upper bound. -/
theorem E_core_commutators (s : d.ActionDescent)
    (h21 : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (a : F.H) (ha : (a : G) ∈ conjugate F.U c.conjugator⁻¹)
    (t : SL2FourNatural.F) (ht : t ≠ 0)
    (hmark : d.qH a = alternatingActor d.naturalQuotient (SL2FourNatural.upper t)) :
    ⁅E c, F.H.pCoreIn 2⁆ = F.Vi 1 ∧ ⁅E c, c.Qα⁆ = c.Zα := by
  have hα : ⁅c.Uα, c.Qα⁆ = c.Zα := by
    have hm := congrArg (fun A : Subgroup G => A.map (MulAut.conj c.conjugator⁻¹).toMonoidHom) h21
    rw [map_commutator, map_pCoreIn_of_injective 2 F.H _ (MulAut.conj _).injective] at hm
    exact hm
  constructor
  · apply le_antisymm
    · exact (commutator_mono (h.E_le_intersection.trans inf_le_left) le_rfl).trans_eq h21
    · rw [← h.opposite_commutator s h21]
      exact commutator_mono le_sup_right le_rfl
  · apply le_antisymm
    · exact (commutator_mono (h.E_le_intersection.trans inf_le_right) le_rfl).trans_eq hα
    · rw [← h.point_commutator s h21 a ha t ht hmark]
      exact commutator_mono le_sup_left le_rfl

/-- Two distinct actual involutions generate the source points and have
precisely the two vertex centralizers. These are the remaining A.1.14
applicability conditions. -/
theorem E_source_involutions :
    ∃ v₁ ∈ E c, ∃ v₂ ∈ E c,
      orderOf v₁ = 2 ∧ orderOf v₂ = 2 ∧ v₁ ≠ v₂ ∧
      zpowers v₁ = F.Vi 1 ∧ zpowers v₂ = c.Zα ∧
      centralizer ({v₁} : Set G) = F.H ∧
      (centralizer ({v₂} : Set G)).pCoreIn 2 = c.Qα := by
  let e := MulAut.conj c.conjugator⁻¹
  have hz : d.z ∈ F.Vi 1 := d.point ▸ mem_zpowers d.z
  have hzα : e d.z ∈ c.Zα := mem_map_of_mem e.toMonoidHom hz
  have ho : orderOf d.z = 2 := by
    rw [← Nat.card_zpowers, ← d.point]
    simpa using F.card 1 (by decide)
  have hp : zpowers (e d.z) = c.Zα := by
    change zpowers (e d.z) = (F.Vi 1).map e.toMonoidHom
    rw [d.point, MonoidHom.map_zpowers]
    rfl
  have hne : d.z ≠ e d.z := by
    intro he
    have hZle : c.Zα ≤ d.U₀ := by rw [← hp, ← he, ← d.point]; exact d.point_le_U₀
    exact h.opposite_not_le hZle
  have hC : centralizer ({e d.z} : Set G) = conjugate F.H c.conjugator := by
    rw [d.centralizer_eq]
    change centralizer ({e d.z} : Set G) = (centralizer ({d.z} : Set G)).map e.toMonoidHom
    ext x
    rw [mem_map_equiv, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · intro hx
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using hx
    · intro hx
      simpa only [map_mul, e.apply_symm_apply] using congrArg e hx
  exact ⟨d.z, mem_sup_left hz, e d.z, mem_sup_right hzα, ho,
    (e.orderOf_eq d.z).trans ho, hne, d.point.symm, hp, d.centralizer_eq.symm,
    congrArg (pCoreIn 2) hC⟩

end Preliminary
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.LocalGeometry.RankThree
