module

public import CFSG.Quasithin.ChapterD.Section01.UniqueFactor.Setup
public import CFSG.Quasithin.ChapterD.Section01.SylowResidual
public import Theory.ThreeSubgroups

/-!
# The centralizing normal closure in D.1.4

Once Q = ⟨(R ∩ R₂)ᴳ₂⟩ centralizes V, the defining equality R = C_T(V)
forces Q = R ∩ R₂. Normality of Q then propagates centralization from V to
U, proving that U is elementary abelian. The relative three-subgroups lemma
applied modulo Q turns the source identity O²(G₂) = [O²(G₂),R] into
[R₂,O²(G₂)] ≤ Q. This is the input of the original Sylow consequence.

The dual-offender and residual-generation stages must establish the explicit
premises below in the final D.1.4 assembly. No q > 1 assumption is used.
Source: Aschbacher--Smith, D.1.4, printed p.176, equations following (!).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.UniqueFactor
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G] {G₁ G₂ T V : Subgroup G}

theorem intersectionClosure_le_right_core :
    intersectionClosure G₁ G₂ ≤ twoCoreIn G₂ :=
  conjugateSpan_le _ _ _ inf_le_right (twoCore_normalized G₂)

theorem span_le_intersectionClosure (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂) :
    conjugateSpan G₂ V ≤ intersectionClosure G₁ G₂ := by
  apply conjugateSpan_le
  · exact (le_inf d.module_le_core hV).trans (le_conjugateSpan _ _)
  · exact conjugateSpan_normalized _ _

/-- If Q centralizes V, the source centralizer equality gives Q = R ∩ R₂. -/
theorem intersectionClosure_eq_of_centralizes (d : QRCConfiguration G₁ G₂ T V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    intersectionClosure G₁ G₂ = twoCoreIn G₁ ⊓ twoCoreIn G₂ := by
  apply le_antisymm _ (le_conjugateSpan _ _)
  refine le_inf ?_ intersectionClosure_le_right_core
  have hQT : intersectionClosure G₁ G₂ ≤ T :=
    (intersectionClosure_le_right_core (G₁ := G₁) (G₂ := G₂)).trans
      (right_core_le_sylow d)
  exact (le_inf hQT hc).trans_eq d.core_eq_centralizer.symm

/-- This is normality in G₂, not an ambient normality assertion. -/
theorem intersection_normalized_of_centralizes (d : QRCConfiguration G₁ G₂ T V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    G₂ ≤ normalizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G) := by
  rw [← intersectionClosure_eq_of_centralizes d hc]
  exact conjugateSpan_normalized _ _

theorem span_centralizes_intersection_of_centralizes
    (d : QRCConfiguration G₁ G₂ T V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    conjugateSpan G₂ V ≤ centralizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G) := by
  apply conjugateSpan_le
  · rw [← intersectionClosure_eq_of_centralizes d hc]
    rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  · exact (intersection_normalized_of_centralizes d hc).trans
      (normalizer_le_normalizer_centralizer _)

/-- The source Φ(U) = 1 assertion, strengthened to its elementary-abelian form. -/
theorem span_elementary_of_centralizes (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≤ twoCoreIn G₂)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G)) :
    IsElementaryAbelian 2 (conjugateSpan G₂ V) := by
  let := d.module_elementary
  have hUQ : conjugateSpan G₂ V ≤ twoCoreIn G₁ ⊓ twoCoreIn G₂ := by
    rw [← intersectionClosure_eq_of_centralizes d hc]
    exact span_le_intersectionClosure d hV
  have hab : IsMulCommutative (conjugateSpan G₂ V) :=
    le_centralizer_iff_isMulCommutative.mp
      ((span_centralizes_intersection_of_centralizes d hc).trans
        (centralizer_le hUQ))
  rw [conjugateSpan_eq] at hab ⊢
  let := hab
  exact conjugateSpanBy_elementary_of_commutative V G₂

/-- R cannot lie in R₂ once the nontrivial source intersection is G₂-normal. -/
theorem left_core_not_le_right_core (d : QRCConfiguration G₁ G₂ T V)
    (hV : V ≠ ⊥)
    (hn : G₂ ≤ normalizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G)) :
    ¬ twoCoreIn G₁ ≤ twoCoreIn G₂ := by
  intro hRR
  rw [inf_eq_left.mpr hRR] at hn
  have hR := d.eq_bot_of_normalized le_rfl (twoCore_normalized G₁) hn
  exact hV (le_bot_iff.mp (d.module_le_core.trans hR.le))

/-- Both cores are normal in the common Sylow, so their commutator lies in
their intersection, with all subgroups in the original ambient group. -/
theorem cores_commutator_le_intersection (d : QRCConfiguration G₁ G₂ T V) :
    ⁅twoCoreIn G₂, twoCoreIn G₁⁆ ≤ twoCoreIn G₁ ⊓ twoCoreIn G₂ := by
  apply le_inf
  · exact le_normalizer_iff_commutator_le_right.mp
      (((right_core_le_sylow d).trans (sylow_le_left d)).trans (twoCore_normalized G₁))
  · exact le_normalizer_iff_commutator_le_left.mp
      (((left_core_le_sylow d).trans (sylow_le_right d)).trans (twoCore_normalized G₂))

/-- The quotient-by-Q calculation following source equation (!). The residual
identity is the output of the earlier minimal-parabolic step, not a
commutator-containment premise. -/
theorem core_residual_commutator_le_intersection
    (d : QRCConfiguration G₁ G₂ T V)
    (hn : G₂ ≤ normalizer ((twoCoreIn G₁ ⊓ twoCoreIn G₂ : Subgroup G) : Set G))
    (he : (pResidual 2 G₂).map G₂.subtype =
      ⁅(pResidual 2 G₂).map G₂.subtype, twoCoreIn G₁⁆) :
    ⁅twoCoreIn G₂, (pResidual 2 G₂).map G₂.subtype⁆ ≤
      twoCoreIn G₁ ⊓ twoCoreIn G₂ := by
  let K := (pResidual 2 G₂).map G₂.subtype
  have hK : K ≤ G₂ := map_subtype_le _
  have hR : twoCoreIn G₁ ≤ G₂ := (left_core_le_sylow d).trans (sylow_le_right d)
  have hN : twoCoreIn G₂ ≤ G₂ := twoCore_le G₂
  have hNR := cores_commutator_le_intersection d
  have hRN : ⁅twoCoreIn G₁, twoCoreIn G₂⁆ ≤ twoCoreIn G₁ ⊓ twoCoreIn G₂ := by
    rwa [commutator_comm]
  have hNK : ⁅twoCoreIn G₂, K⁆ ≤ twoCoreIn G₂ :=
    le_normalizer_iff_commutator_le_left.mp (hK.trans (twoCore_normalized G₂))
  have hrot := commutator_commutator_le_of_rotate_of_le_normalizer
    (hK.trans hn) (hR.trans hn) (hN.trans hn)
    ((commutator_mono hRN le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hK.trans hn)))
    ((commutator_mono hNK le_rfl).trans hNR)
  change ⁅⁅K, twoCoreIn G₁⁆, twoCoreIn G₂⁆ ≤ _ at hrot
  rw [← he] at hrot
  rwa [commutator_comm]

/-- A usable D.1.4 export for the Sylow application. The unique-factor assembly
discharges centralization of Q and the source residual identity. -/
theorem core_residual_commutator_le_left_core
    (d : QRCConfiguration G₁ G₂ T V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G))
    (he : (pResidual 2 G₂).map G₂.subtype =
      ⁅(pResidual 2 G₂).map G₂.subtype, twoCoreIn G₁⁆) :
    ⁅twoCoreIn G₂, (pResidual 2 G₂).map G₂.subtype⁆ ≤ twoCoreIn G₁ :=
  (core_residual_commutator_le_intersection d
    (intersection_normalized_of_centralizes d hc) he).trans inf_le_left

/-- The actual downstream Sylow application. Its oddness premise is precisely
the earlier solvable B.6.8(2) assertion; F*(G₂) = O₂(G₂) is unnecessary here. -/
theorem exists_sylow_residual_sup_of_centralizes
    (d : QRCConfiguration G₁ G₂ T V)
    (hc : intersectionClosure G₁ G₂ ≤ centralizer (V : Set G))
    (he : (pResidual 2 G₂).map G₂.subtype =
      ⁅(pResidual 2 G₂).map G₂.subtype, twoCoreIn G₁⁆)
    (hodd : Odd (Nat.card (pResidual 2 (G₂ ⧸ pCore 2 G₂)))) :
    let H := (pResidual 2 G₂).map G₂.subtype ⊔ twoCoreIn G₁
    ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = twoCoreIn G₁ :=
  d.exists_sylow_residual_sup_of_core_commutator hodd
    (core_residual_commutator_le_left_core d hc he)

end CFSG.Quasithin.ChapterD.UniqueFactor
