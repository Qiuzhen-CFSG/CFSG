module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticCentralSupplement
public import Theory.Frattini.QuadraticCentralizer
public import Theory.GroupTheory.AlmostSpecialIntersection

/-!
# Frattini control of the original full quintic kernel

The original full kernel C centralizes U and has commutators with the actual
supplement in the elementary group U. Its Frattini subgroup therefore
centralizes that supplement, including its original middle span W.
Since the supplement and C generate the full core, the intersection of
Phi(C) with U lies in the original central line.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The full-kernel Frattini and derived subgroups centralize the actual
H-span of a middle span, with the same critical conjugator retained. -/
theorem source_quintic_full_kernel_frattini_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let X := sourceResidual M Mc ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (localModule T M) H
    let Q := H.pCoreIn 2
    let C := H ⊓ centralizer (U : Set G)
    ∃ g ∈ X,
      let W := conjugateSpanBy (U ⊓ Q.map (MulAut.conj g).toMonoidHom) X
      let J := conjugateSpanBy W H
      W ≤ Q ⊓ X.pCoreIn 2 ∧ X ≤ normalizer (W : Set G) ∧
      J ≤ Q ∧ H ≤ normalizer (J : Set G) ∧ J ⊔ C = Q ∧
      ⁅J,Q⁆ ≤ U ∧ (frattini C).map C.subtype ≤ centralizer (J : Set G) ∧
      ⁅C,C⁆ ≤ centralizer (J : Set G) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  obtain ⟨g,hg,_,hWQ,hXW,_,_,_,_,_,_,_,_,hWQcomm,_,hJQ,hHJ,hJC⟩ :=
    source_quintic_exact_span_full_core_supplement
      hG T hempty hM hu hmany hcard e H hH hi
  let W := conjugateSpanBy (U ⊓ Q.map (MulAut.conj g).toMonoidHom) X
  let J := conjugateSpanBy W H
  let : IsElementaryAbelian 2 U :=
    (Section02.SolvableAmalgam.source_index_five_closure_structure
      hG T hempty hM hu hmany hcard e H hH.1 hi).1
  have hCQ : C ≤ Q := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hpC : IsPGroup 2 C := (isPGroup_pCoreIn 2 H).to_le hCQ
  have hHQ : H ≤ normalizer (Q : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hHU : H ≤ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _
  have hJcomm : ⁅J,Q⁆ ≤ U := by
    change ⁅conjugateSpanBy W H,Q⁆ ≤ U
    rw [commutator_conjugateSpanBy_of_normalized_right W H Q
      ((hWQ.trans inf_le_left).trans (pCoreIn_le 2 H)) hHQ]
    exact conjugateSpanBy_le hWQcomm hHU
  have hCJ : ⁅C,J⁆ ≤ U := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hCQ).trans hJcomm
  have hphi : (frattini C).map C.subtype ≤ centralizer (J : Set G) :=
    frattini_image_le_centralizer_of_elementary_commutator C J U hpC hCJ inf_le_right
  exact ⟨g,hg,hWQ,hXW,hJQ,hHJ,hJC,hJcomm,hphi,
    derived_le_of_frattini_image_le hpC hphi⟩

/-- The full-kernel Frattini subgroup meets the original quintic span only
inside the original Sylow central line. -/
theorem source_quintic_full_kernel_frattini_span_intersection
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (U : Set G)
    (frattini C).map C.subtype ⊓ U ≤ centralInvolutions T := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (localModule T M) H
  let Q := H.pCoreIn 2
  let C := H ⊓ centralizer (U : Set G)
  let P := (frattini C).map C.subtype
  obtain ⟨g,hg,_,_,_,_,hJC,_,hphi,_⟩ :=
    source_quintic_full_kernel_frattini_centralizer
      hG T hempty hM hu hmany hcard e H hH hi
  let W := conjugateSpanBy (U ⊓ Q.map (MulAut.conj g).toMonoidHom) X
  let J := conjugateSpanBy W H
  change J ⊔ C = Q at hJC
  change P ≤ centralizer (J : Set G) at hphi
  have hfixed : P ⊓ U ≤ centralizer (Q : Set G) := by
    apply le_centralizer_iff.mpr
    rw [←hJC]
    exact sup_le
      (le_centralizer_iff.mp (inf_le_left.trans hphi))
      (le_centralizer_iff.mp (inf_le_right.trans
        (le_centralizer_iff.mp (show C ≤ centralizer (U : Set G) from inf_le_right))))
  exact (le_inf inf_le_right hfixed).trans
    (source_quintic_span_card_and_core_radical
      hG T hempty hM hu hmany hcard e H hH hi).2.le

end CFSG.Quasithin.Chapter14.Section06
