module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuinticDGSNaturalCenter
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingThreeProfile.SecondKernelLayer
public import Theory.ElementaryAbelian.Injective

/-!
# The original quintic core modulo its full second kernel

The actual cubic natural center and common Sylow supply the elementary
second-kernel theorem.  The original completion inclusion identifies both
the numerator and the entire denominator, giving the literal QH/C quotient
and its Frattini containment.  Both quintic quotient rows are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.GroupTheory.AmalgamGraph
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterF.Source ChapterF.Source.DGS85
open CommutingThreeProfile.ReducedLayer
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem elementary_quotient_image
    {A : Type*} [Group A] (f : A →* G) (hf : Function.Injective f)
    (Q N : Subgroup A) (Q' N' : Subgroup G)
    (hQ : Q.map f = Q') (hN : N.map f = N')
    [(N.subgroupOf Q).Normal] [(N'.subgroupOf Q').Normal]
    [IsElementaryAbelian 2 (Q ⧸ N.subgroupOf Q)] :
    IsElementaryAbelian 2 (Q' ⧸ N'.subgroupOf Q') := by
  let e : Q ≃* Q' := (Q.equivMapOfInjective f hf).trans (MulEquiv.subgroupCongr hQ)
  have hcomp : Q'.subtype.comp e.toMonoidHom = f.comp Q.subtype := by
    ext x
    rfl
  have hden : (N.subgroupOf Q).map e.toMonoidHom = N'.subgroupOf Q' := by
    apply map_injective Q'.subtype_injective
    rw [map_map,hcomp,←map_map,subgroupOf_map_subtype,map_inf _ _ _ hf,
      hN,hQ,subgroupOf_map_subtype]
  let eQ := QuotientGroup.congr _ _ e hden
  exact IsElementaryAbelian.of_injective eQ.symm.toMonoidHom eQ.symm.injective

/-- The full original quintic core modulo the full radius-two kernel is
elementary abelian.  Its exact Frattini containment uses the same kernel. -/
theorem source_quintic_full_kernel_elementary_quotient
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5) :
    let UH := conjugateSpanBy (localModule T M) H
    let C := H ⊓ centralizer (UH : Set G)
    C ≤ H.pCoreIn 2 ∧ ∃ hN : (C.subgroupOf (H.pCoreIn 2)).Normal,
      letI := hN
      IsElementaryAbelian 2 (H.pCoreIn 2 ⧸ C.subgroupOf (H.pCoreIn 2)) ∧
        frattini (H.pCoreIn 2) ≤ C.subgroupOf (H.pCoreIn 2) := by
  classical
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let L : Fin 2 → Subgroup G := ![H,X]
  let J := Reduction.G₀ L (T : Subgroup G)
  let F := Reduction.reducedFamily L (T : Subgroup G)
  let UH := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (UH : Set G)
  have hCQ : C ≤ H.pCoreIn 2 := source_quintic_span_centralizer_le_core hG T hM H hH hi
  have hn : H ≤ normalizer (C : Set G) :=
    (le_inf H.le_normalizer ((le_normalizer_conjugateSpanBy (localModule T M) H).trans
      (normalizer_le_normalizer_centralizer UH))).trans inf_normalizer_le_normalizer_inf
  let hN : (C.subgroupOf (H.pCoreIn 2)).Normal :=
    normal_subgroupOf_of_le_normalizer ((pCoreIn_le 2 H).trans hn)
  let := hN
  obtain ⟨hF,_,hred,_,hP,_,hmaps,_⟩ :=
    source_quintic_dgs_reduced_pair hG T hempty hM hu hmany hcard e H hH hi
  change HypothesisF11 L (T : Subgroup G) at hF
  change SuzukiContainment.reducedSylow L (T : Subgroup G) = T at hred
  have hpar : parabolic L (T : Subgroup G) 1 = Reduction.P₀ L (T : Subgroup G) 1 := by
    rw [Reduction.P₀_eq_source hF,hred]
  have hstar : star L (T : Subgroup G) true = F true := by
    change (starredParabolic L (T : Subgroup G) 1).subgroupOf J =
      (Reduction.P₀ L (T : Subgroup G) 1).subgroupOf J
    apply congrArg (fun K : Subgroup G => K.subgroupOf J)
    apply le_antisymm
    · exact (starredParabolic_le 1).trans_eq hpar
    · rw [hP]
      exact local_le_starredParabolic 1
  obtain ⟨S,hS⟩ :=
    (source_quintic_dgs_common_sylow hG T hempty hM hu hmany hcard e H hH hi).2.2 true
  have hplace : Q F (base F false) ≤ star L (T : Subgroup G) true := by
    rw [hstar]
    exact (le_sup_left.trans hS.1.ge).trans (map_subtype_le _)
  have hnat := (source_quintic_cubic_natural_center
    hG T hempty hM hu hmany hcard e H hH hi).2.1
  obtain ⟨hfirst,hspan,hkernel⟩ :=
    source_quintic_dgs_span_and_full_kernel hG T hempty hM hu hmany hcard e H hH hi
  obtain ⟨hZH,_⟩ := source_quintic_dgs_center_markings hG T hempty hM hu hmany hcard e H hH hi
  have hcomm : ⁅V F (base F false) 1,Q F (base F false)⁆ ≤ Z F (base F false) := by
    apply (map_le_map_iff_of_injective J.subtype_injective).mp
    rw [map_commutator,hspan,(hmaps false).2,hZH]
    exact (source_quintic_core_commutators hG T hempty hM hu hmany hcard e H hH hi).2.le
  let : ((ballKernel F (base F false) 2).subgroupOf (Q F (base F false))).Normal :=
    normal_subgroupOf_of_le_normalizer
      ((Q_le_stabilizer F _).trans (stabilizer_le_normalizer_ballKernel F _ 2))
  let := CommutingThreeProfile.source_second_kernel_elementary hF false hplace hnat hcomm
  have he : IsElementaryAbelian 2 (H.pCoreIn 2 ⧸ C.subgroupOf (H.pCoreIn 2)) :=
    elementary_quotient_image J.subtype J.subtype_injective
      (Q F (base F false)) (ballKernel F (base F false) 2) (H.pCoreIn 2) C
      (hmaps false).2 hkernel
  exact ⟨hCQ,hN,he,frattini_le_of_elementary_quotient (isPGroup_pCoreIn 2 H) _ he⟩

end CFSG.Quasithin.Chapter14.Section06
