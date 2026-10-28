module

public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.Core

/-!
# The additional absorption needed by the printed core equality

Source: Aschbacher–Smith, Lemma 8.2.7, printed p.718 (PDF p.735).

The pair identity implies P≤XU using O²(I)≤X, without asserting I≤X.
Once P≤O₂(H), the stronger equality V∩P=V∩O₂(X) is equivalent to U≤X.
The forward implication uses U≤V∩P; the reverse implication restricts the
normal two-core of H to X. Thus the additional source obligation is precise.
This module does not assert that the pair identity alone absorbs U into X.
The weaker containment used by the rank-ten route remains unchanged.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
variable {G : Type*} [Group G]

/-- The commutator part of P already lies in X. -/
theorem pair_core_le_residual_sup (I H X U : Subgroup G)
    (hIH : I ≤ H) (hX : X = (pResidual 2 H).map H.subtype)
    (hP : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U) :
    I.pCoreIn 2 ≤ X ⊔ U := by
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hX]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  have hc : ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ≤ X :=
    (commutator_mono le_rfl (pair_residual_le I H X hIH hX)).trans
      (le_normalizer_iff_commutator_le_right.mp ((pCoreIn_le 2 I).trans (hIH.trans hHX)))
  rw [hP]
  exact sup_le_sup_right hc U

/-- Under the actual pair identity, the stronger printed intersection equality
is equivalent to absorption of U by X. This does not assume I ≤ X or B ≤ X. -/
theorem pair_core_intersection_residual_iff (I H X U V : Subgroup G)
    (hIH : I ≤ H) (hX : X = (pResidual 2 H).map H.subtype)
    (hVI : V ≤ I) (hUB : U ≤ V ⊓ I.pCoreIn 2)
    (hP : I.pCoreIn 2 = ⁅I.pCoreIn 2, (pResidual 2 I).map I.subtype⁆ ⊔ U)
    (hc : I.pCoreIn 2 ≤ H.pCoreIn 2) :
    V ⊓ I.pCoreIn 2 = V ⊓ X.pCoreIn 2 ↔ U ≤ X := by
  have hXH : X ≤ H := hX ▸ map_subtype_le _
  have hHX : H ≤ normalizer (X : Set G) := by
    rw [hX]
    exact H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pResidual 2 H))
  constructor
  · intro he
    exact hUB.trans (he.le.trans (inf_le_right.trans (pCoreIn_le 2 X)))
  · intro hUX
    have hPX : I.pCoreIn 2 ≤ X := by
      have hh := pair_core_le_residual_sup I H X U hIH hX hP
      simpa only [sup_eq_left.mpr hUX] using hh
    have hPQ : I.pCoreIn 2 ≤ X.pCoreIn 2 :=
      (le_inf hPX hc).trans (inf_pCoreIn_le_of_le 2 hXH)
    exact le_antisymm (inf_le_inf_left V hPQ)
      (residual_core_intersection_le X H I V hXH hHX hIH hVI)
end CFSG.Quasithin.Chapter8.Section02.Normalizer.ComponentExclusion.ChiefAction.SourceInversion
