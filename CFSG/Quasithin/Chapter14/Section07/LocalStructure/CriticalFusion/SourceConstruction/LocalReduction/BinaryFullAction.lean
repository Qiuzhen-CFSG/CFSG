module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryFullPoint
public import Theory.GroupTheory.CenterlessResidualCoreAction
public import Theory.GroupTheory.NormalQuotientActionSylowSupplement
public import Theory.GroupTheory.AutomorphismSquareOuterTwo
public import Theory.SpecificGroups.PSL2.FieldDegreeOuterOrder
public import Theory.GroupTheory.PResidual.PrimeToTransport

/-!
# The full point action in the exchanged field-four branch

The original component orbit is the full three-prime residual of the
point normalizer. Its actual star quotient is a centerless square of
PSL₂(4), so 14.7.35 kills its full quotient centralizer. Equivariance
through the intrinsic two-core quotient gives exactly O₂(H) as the
conjugation-action kernel. The square's outer automorphism group is a
two-group, and the Sylow supplement then proves H = K₀T.

Thus every original local with a moved component is the full point
normalizer, and its literal seed span U_H equals U. This supplies the
full-point generation and kernel used in the subsequent module argument;
it does not assume that module's orthogonal recognition.

Source: Aschbacher–Smith, proof of 14.7.32, printed p.1056,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

private theorem four_outer {X : Type*} [Group X]
    (hm : ClassicalGroup.IsPSL X 2 4) : IsPGroup 2 (MulAut.Outer X) := by
  obtain ⟨k,_,_,hk,⟨e⟩⟩ := hm
  let : CharP k 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (show Nat.card k = 2^2 by simpa using hk)
  have ho : IsPGroup 2 (MulAut.Outer PSL(2,k)) := IsPGroup.of_card (n := 1)
    (by simpa using Theory.PSL2.outer_card_eq_field_degree k (show Nat.card k = 2^2 by simpa using hk))
  exact ho.of_equiv (MulAut.outerCongr e).symm

private theorem full_residual_center_outer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    center (primeToResidual 3 (HStar F.H)) = ⊥ ∧
      IsPGroup 2 (MulAut.Outer (primeToResidual 3 (HStar F.H))) := by
  obtain ⟨hfull,hres⟩ := local_nonnormal_component_full_component d h hab structural previous faithful earlier
    I K hI hKI hK hnormal
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hKH : K ≤ F.H := hKI.trans hI.2.1
  have hTH := F.sylow_le_of_mem_Hz hH
  have hnon : ¬ (K.subgroupOf F.H).Normal := by
    intro hn
    exact hnormal ((normal_subgroupOf_iff_le_normalizer hKI).mpr
      (hI.2.1.trans ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)))
  have hm := local_nonnormal_component_field_four d h hab structural previous faithful earlier
    F.H K hH hKH hfull hnon
  have hmove : conjugateSpanBy K (T : Subgroup G) ≠ K := by
    intro he
    exact hnon (normal_of_sylow_span_eq F.H K T hKH hTH
      ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
        (local_star_sqtk h F.H hH) hfull).imp_right And.left) he)
  obtain ⟨t,ht,htn⟩ := exists_moving_element K (T : Subgroup G) hmove
  have hi := ((Chapter1.Section02.proposition_1_2_1_three_index_knownSimple
    (local_star_sqtk h F.H hH) hfull).resolve_left hnon).1
  have horbit := orbit_eq_two_conjugates F.H K T hKH hTH hi ht htn
  have hqs := (local_component_star_isComponent h hab structural previous faithful
    F.H hH _ hfull).2
  let : IsQuasisimple (Chapter13.Section08.Source.starImage F.H K) := hqs
  obtain ⟨e₀,_⟩ := exists_moving_star_coordinates F.H K hKH hfull hqs (hTH ht) htn hm
  have hr : Chapter13.Section08.Source.starImage F.H (conjugateSpanBy K (T : Subgroup G)) =
      primeToResidual 3 (HStar F.H) := by
    rw [Chapter13.Section08.Source.starImage,←hres,subgroupOf,
      comap_map_eq_self_of_injective F.H.subtype_injective,
      map_primeToResidual_of_surjective 3 _ (QuotientGroup.mk'_surjective _)]
  let e := e₀.trans (MulEquiv.subgroupCongr (horbit ▸ hr))
  have hz := center_eq_bot_of_psl2 hm
  have hzpair : center (Chapter13.Section08.Source.starImage F.H K ×
      Chapter13.Section08.Source.starImage F.H K) = ⊥ := by
    simp [Subgroup.center_prod,hz]
  have hzR : center (primeToResidual 3 (HStar F.H)) = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := ((centerCongr e).symm ⟨x,hx⟩).property
    change e.symm x ∈ center (Chapter13.Section08.Source.starImage F.H K ×
      Chapter13.Section08.Source.starImage F.H K) at hh
    rw [hzpair,mem_bot] at hh
    exact e.symm.injective (hh.trans (map_one e.symm).symm)
  exact ⟨hzR,(AutomorphismSquare.outer_isPGroup_two hz (four_outer hm)).of_equiv
    (MulAut.outerCongr e)⟩

/-- The full orbit has trivial centralizer in the actual star quotient,
and the original conjugation action on its intrinsic two-core quotient
has precisely the full point normalizer's two-core as kernel. -/
theorem local_nonnormal_component_full_centralizer
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    centralizer (primeToResidual 3 (HStar F.H) : Set (HStar F.H)) = ⊥ ∧
      (normalQuotientAction (primeToResidual 3 F.H)
        (pCore 2 (primeToResidual 3 F.H))).ker = pCore 2 F.H := by
  have hz := (full_residual_center_outer d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).1
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hc := centralizer_primeToResidual_eq_bot_of_center_eq_bot 3 hz
    (local_threePrimeCore_eq_bot d h hab structural previous faithful earlier F.H hH)
  refine ⟨hc,normalQuotientAction_pCore_ker_of_centralizer_eq_bot 2 _ ?_⟩
  rwa [map_primeToResidual_of_surjective 3 _ (QuotientGroup.mk'_surjective _)]

/-- A local with a moved component is the full point normalizer. Its
original component orbit and Sylow subgroup generate that normalizer;
therefore its literal seed span U_I is the original U. -/
theorem local_nonnormal_component_eq_full_point
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hnormal : ¬ (K.subgroupOf I).Normal) :
    F.H = conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) ∧
      I = F.H ∧ F.UH I = F.U := by
  have ho := (full_residual_center_outer d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).2
  have hk := (local_nonnormal_component_full_centralizer d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).2
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  have hTH := F.sylow_le_of_mem_Hz hH
  let S := T.subtype hTH
  let R := primeToResidual 3 F.H
  let e := (coreQuotientEquivImage 2 R).trans (MulEquiv.subgroupCongr
    (map_primeToResidual_of_surjective 3 _ (QuotientGroup.mk'_surjective (pCore 2 F.H))))
  have hoR : IsPGroup 2 (MulAut.Outer (R ⧸ pCore 2 R)) :=
    ho.of_equiv (MulAut.outerCongr e).symm
  have hg := normalQuotientAction_sup_sylow_ker S R (pCore 2 R) hoR
  rw [hk,sup_eq_left.mpr ((pCore_isPGroup.le_sylow_of_normal S).trans le_sup_right)] at hg
  have hm := congrArg (map F.H.subtype) hg
  rw [Subgroup.map_sup,Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH,
    ←MonoidHom.range_eq_map,range_subtype] at hm
  have hres := (local_nonnormal_component_full_component d h hab structural previous faithful earlier
    I K hI hKI hK hnormal).2
  change (primeToResidual 3 F.H).map F.H.subtype ⊔ (T : Subgroup G) = F.H at hm
  rw [hres] at hm
  have he : I = F.H := le_antisymm hI.2.1 (by
    rw [←hm]
    exact sup_le (conjugateSpanBy_le hKI ((F.sylow_le_of_mem_Hz hI).trans I.le_normalizer))
      (F.sylow_le_of_mem_Hz hI))
  refine ⟨hm.symm,he,?_⟩
  rw [he]
  rfl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
