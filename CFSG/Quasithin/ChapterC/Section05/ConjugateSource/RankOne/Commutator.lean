module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.Frattini
public import Theory.GroupTheory.Commutator.QuadraticConjugatePair
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# The full fixed subgroup in the rank-one branch

The genuine central cover is quadratic under the upper root group.
Two conjugate root groups generate the block, whose commutator module is
U itself. The quadratic conjugate-pair theorem therefore identifies the
full fixed subgroup with the commutator, including its central radical.
The symmetric span gives invariance under the original conjugator.

Source: Aschbacher–Smith C.5.6(2),(3), printed p.156. The fixed-lifting
consequence of I.2.3 is proved in Covers; no further cover input remains.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R L : Subgroup G} {F : Type*} [Field F]

/-- Two-perfection gives idempotence on the actual embedded block module. -/
theorem Setup.module_generated (h : Setup R L F) : ⁅U L, L⁆ = U L := by
  have hi : ⁅blockU L, (⊤ : Subgroup L)⁆ = blockU L :=
    commutator_isPPerfect_idempotent (⊤ : Subgroup L) (pCore 2 L)
      (h.short.twoPerfect.of_surjective (topEquiv (G := L)).symm.toMonoidHom
        (topEquiv (G := L)).symm.surjective)
      pCore_isPGroup (by rw [normalizer_eq_top])
  have hm := congrArg (map L.subtype) hi
  rwa [map_commutator, ← MonoidHom.range_eq_map, range_subtype] at hm

/-- The fixed subgroup of the original full module equals its displacement
under the noncommuting conjugate. No quotient-kernel triviality is used. -/
theorem Setup.commutator_eq_fixed (h : Setup R L F) {x : G}
    (hx : x ∈ normalizer (R : Set G))
    (hnc : ¬ (U L).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U L : Set G)) :
    let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
    ⁅U L, V⁆ = U L ⊓ centralizer (V : Set G) ∧ ⁅U L, V⁆ = U L ⊓ V := by
  let V := (U L).map (MulAut.conj x⁻¹).toMonoidHom
  let := h.elementary
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hVS := h.conjugate_le hx
  have hnU := h.coordinates.normalizes
  have hnV := h.conjugate_normalized hx
  have hi := h.indices hx hnc
  obtain ⟨y, hy, hgen⟩ := h.quotient_pair (span_of_actionIndices h hx hi)
  have hpair := lift_generating_pair h hx hy hgen
  have hquad : ⁅U L, V⁆ ≤ centralizer (V : Set G) :=
    (((commutator_mono le_rfl hVS).trans (commutator_le_fixed h.coordinates h.fixedLift)).trans
      inf_le_right).trans (centralizer_le hVS)
  have he := commutator_eq_fixed_of_quadratic_conjugate_pair (U L) L V
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (blockU L)))
    (hVS.trans hnU) h.module_generated hquad y hy hpair
  have hle : ⁅U L, V⁆ ≤ U L ⊓ V := le_inf
    (le_normalizer_iff_commutator_le_left.mp (hVS.trans hnU))
    (le_normalizer_iff_commutator_le_right.mp (h.module_le.trans hnV))
  have hfix : U L ⊓ V ≤ U L ⊓ centralizer (V : Set G) :=
    inf_le_inf_left _ (le_centralizer V)
  exact ⟨he, le_antisymm hle (hfix.trans he.ge)⟩
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
end
