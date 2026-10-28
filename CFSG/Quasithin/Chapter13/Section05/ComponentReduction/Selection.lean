module

public import CFSG.Quasithin.ChapterF.Section09.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Selecting the actual component after 13.5.20

A nontrivial two-subgroup centralizing F(X), with O₂(X) = 1, must move a
component of X. Otherwise it lies in C_X(F*(X)); this centralizer is abelian
and normal, so its two-subgroups lie in O₂(X), a contradiction.

Apply this to V* in the actual H/O₂(H). F.9.4(1) and nonabelianness of U_H
show V* is nontrivial. Lift the selected component through the solvable kernel
to a C-component K of H and retain the exact isomorphism K/O₂(K) ≃ K*.
This is selection only: K*V*, K*, and Ũ_H/C_Ũ_H(K*) are still distinct.
Fitting centralization remains the explicit 13.5.20 premise; the component
classification and the remaining clauses of 13.5.21 are not asserted here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
paragraph after 13.5.20, printed p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction
open Section08.Source
open Theory.GroupTheory
private theorem exists_moved_component {X : Type*} [Group X] [Finite X]
    (A : Subgroup X) (hp : IsPGroup 2 A) (hne : A ≠ ⊥)
    (hcore : pCore 2 X = ⊥)
    (hf : A ≤ centralizer (fittingSubgroup X : Set X)) :
    ∃ K : Subgroup X, IsComponent X K ∧ ⁅K, A⁆ ≠ ⊥ := by
  by_contra hn
  push Not at hn
  have hc : A ≤ centralizer (generalizedFitting X : Set X) := by
    apply le_centralizer_iff.mp
    apply sup_le (le_centralizer_iff.mp hf)
    apply sSup_le
    intro K hK
    exact commutator_eq_bot_iff_le_centralizer.mp (hn K hK)
  let C := centralizer (generalizedFitting X : Set X)
  have hCF : C ≤ generalizedFitting X := centralizer_generalizedFitting_le X
  have hcomm : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp
    (fun x hx y hy => hx y (hCF hy))
  let := hcomm
  have hAC : A ≤ C := hc
  have hcoreC : A.subgroupOf C ≤ pCore 2 C :=
    le_sSup ⟨inferInstance, hp.comap_subtype⟩
  let : C.Normal := inferInstanceAs (centralizer (generalizedFitting X : Set X)).Normal
  have hncore : (C.pCoreIn 2).Normal := by
    change ((pCore 2 C).map C.subtype).Normal
    infer_instance
  have hcoreX : C.pCoreIn 2 ≤ pCore 2 X :=
    le_sSup ⟨hncore, isPGroup_pCoreIn 2 C⟩
  have ha : A ≤ pCore 2 X := by
    rw [← map_subgroupOf_eq_of_le hAC]
    exact (map_mono hcoreC).trans hcoreX
  exact hne (bot_unique (ha.trans_eq hcore))

variable {G : Type*} [Group G] [Finite G]

/-- The component selected after 13.5.20 lies in H and its star is the
literal image in H/O₂(H). The quotient equivalence retains its two-core kernel. -/
theorem exists_component_of_fitting_centralized
    (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hu : ¬ IsMulCommutative D.UH)
    (hf : starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H))) :
    ∃ K : Subgroup G, K ≤ D.H ∧ (K.subgroupOf D.H).IsCComponent ∧
      IsQuasisimple (starImage D.H K) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* starImage D.H K) ∧
      ⁅starImage D.H K, starImage D.H D.V⁆ ≠ ⊥ := by
  have hne : starImage D.H D.V ≠ ⊥ := by
    intro he
    have hk := (Subgroup.map_eq_bot_iff _).mp he
    have hVQ : D.V ≤ D.QH := by
      intro v hv
      exact mem_map.mpr ⟨⟨v, h.V_le_H hv⟩,
        (QuotientGroup.eq_one_iff _).mp (hk hv), rfl⟩
    exact hu (h.UH_elementary_of_V_le_QH hVQ).toIsMulCommutative
  have hp : IsPGroup 2 (starImage D.H D.V) :=
    h.elementary.isPGroup.comap_subtype.map (QuotientGroup.mk' (pCore 2 D.H))
  obtain ⟨Kbar, hKb, hmove⟩ := exists_moved_component (starImage D.H D.V) hp hne
    (pCore_quotient_pCore_eq_bot 2) hf
  let : Group.IsNilpotent (pCore 2 D.H) := pCore_isNilpotent
  obtain ⟨K, hK, he⟩ := hKb.isCComponent.exists_map_quotient_eq (pCore 2 D.H)
  have hKH : K.map D.H.subtype ≤ D.H := map_subtype_le _
  have hsub : (K.map D.H.subtype).subgroupOf D.H = K :=
    comap_map_eq_self_of_injective D.H.subtype_injective _
  have hstar : starImage D.H (K.map D.H.subtype) = Kbar := by
    rw [starImage, hsub, he]
  have hcomp : ((K.map D.H.subtype).subgroupOf D.H).IsCComponent := hsub.symm ▸ hK
  refine ⟨K.map D.H.subtype, hKH, hcomp, ?_,
    ⟨Section08.Components.componentStarEquiv D.H _ hKH hcomp⟩, ?_⟩
  · rw [hstar]
    exact hKb.2
  · rwa [hstar]

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction
end
