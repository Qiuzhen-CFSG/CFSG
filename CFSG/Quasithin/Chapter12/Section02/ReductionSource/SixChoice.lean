module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NonnormalOuterSource.FourModels.SixNormality
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Selection
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Families

/-!
# Choosing an actual module for an A₆ local component

The component image in LT/O₂(LT) is normal by the cubic-rank obstruction,
including the central three-cover. This proves T-normalization directly
on the original local component. Its faithful intrinsic module and the
quasisimple two-core quotient give a nonzero reduced commutator by A.4.11.
Homogeneous selection inside the literal R₂(LT) constructs ChosenModule.

No maximal-local hypothesis or universal 12.2.2 theorem is used here.
T-invariance of the chosen subgroup and the five-dimensional core marking
remain distinct source conclusions. Source: Aschbacher--Smith A.3.8(3),
A.4.11 and 12.2.2, pp.45--46,61,794--795; the A₆ branch of13.3.2.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open Chapter1 Chapter1.Section02 Chapter1.Section02.LocalModels Chapter1.Section02.Adequate
open ChapterA.SQTKStructure.NonnormalOuterSource.FourModels
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem six_model_transport {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hm : IsAlternating B 6 ∨ IsAlternatingCover B 6) :
    IsAlternating A 6 ∨ IsAlternatingCover A 6 := by
  rcases hm with hm | hm
  · obtain ⟨f⟩ := hm
    exact Or.inl ⟨e.trans f⟩
  · obtain ⟨hq,⟨ez⟩,⟨eq⟩⟩ := hm
    let := hq
    refine Or.inr ⟨IsQuasisimple.of_mulEquiv e.symm,⟨(centerCongr e).trans ez⟩,?_⟩
    exact ⟨(QuotientGroup.congr _ _ e (by
      apply le_antisymm
      · rintro _ ⟨x,hx,rfl⟩
        exact (centerCongr e ⟨x,hx⟩).property
      · intro x hx
        exact ⟨e.symm x,(centerCongr e).symm ⟨x,hx⟩ |>.property,e.apply_symm_apply x⟩)).trans eq⟩

theorem local_six_sylow_normalizes
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ Chapter1.L G (T : Subgroup G))
    (hm : IsAlternating (L ⧸ pCore 2 L) 6 ∨ IsAlternatingCover (L ⧸ pCore 2 L) 6) :
    (T : Subgroup G) ≤ normalizer (L : Set G) := by
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  let eQ : (A ⧸ pCore 2 A) ≃* (L ⧸ pCore 2 L) :=
    QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  have hr : primeRank 3 J ≤ 2 := by
    have hh := (uniqueness_local_quotient_sqtk hG hL.2.2).stronglyQuasithin
      3 (by decide) (by decide)
    rw [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 J) pCore_isPGroup] at hh
    exact hh
  have hn : A.Normal := component_normal_of_six_core_quotient hL.1 hr
    (six_model_transport eQ hm)
  exact le_sup_right.trans ((normal_subgroupOf_iff_le_normalizer le_sup_left).mp hn)

theorem faithful_local_six_exists_chosen
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hL : L ∈ MainForward.faithfulLocalComponents T)
    (hm : IsAlternating (L ⧸ pCore 2 L) 6 ∨ IsAlternatingCover (L ⧸ pCore 2 L) 6) :
    (T : Subgroup G) ≤ normalizer (L : Set G) ∧
      ∃ V : Subgroup G, Nonempty (ChosenModule T L V) := by
  obtain ⟨hl,hf⟩ := (mem_faithfulLocalComponents_iff T L).mp hL
  have hn := local_six_sylow_normalizes hG hl hm
  let J := L ⊔ (T : Subgroup G)
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hn)
  let e : A ≃* L := subgroupOfEquivOfLe le_sup_left
  have htype : ChapterA.Section04.IsFaithfulSignalizerType A := by
    refine ⟨⟨?_,hf.1.2.1.of_surjective e.symm.toMonoidHom e.symm.surjective,?_⟩,?_⟩
    · exact hl.1.ne_bot
    · apply map_injective (f := e.toMonoidHom) e.injective
      rw [map_generalizedFitting_equiv,pCore_map_iso]
      exact hf.1.2.2
    · intro he
      apply hf.2
      rw [← map_subgroupOf_eq_of_le (show L ≤ J from le_sup_left),
        ChapterA.Section04.intrinsicSignalizerModule_map_of_injective J.subtype J.subtype_injective,
        he,Subgroup.map_bot]
  let : IsQuasisimple (L ⧸ pCore 2 L) := (alternatingSix_or_cover_structure hm).1
  let eQ := QuotientGroup.congr (pCore 2 A) (pCore 2 L) e (pCore_map_iso 2 e)
  let : IsQuasisimple (A ⧸ pCore 2 A) := IsQuasisimple.of_mulEquiv eQ.symm
  have hc : HasCentralPChiefFactorsAbove 2 (pCore 2 A) := by
    apply (hasCentralPChiefFactorsAbove_iff_quotient _).mpr
    let e0 : ((A ⧸ pCore 2 A) ⧸ (⊥ : Subgroup (A ⧸ pCore 2 A))) ≃* (A ⧸ pCore 2 A) :=
      QuotientGroup.quotientBot
    let : IsQuasisimple ((A ⧸ pCore 2 A) ⧸ (⊥ : Subgroup (A ⧸ pCore 2 A))) :=
      IsQuasisimple.of_mulEquiv e0.symm
    exact hasCentralTwoChiefFactors_of_odd_normal_quasisimple_quotient
      (⊥ : Subgroup (A ⧸ pCore 2 A)) (by simp) inferInstance
  have hne := ChapterA.Section04.reduced_commutator_ne_bot_of_intrinsicModule_ne_bot
    A (inferInstance : A.Normal).isSubnormal htype.1.2.1 hc htype.2
  let : Group.IsPerfect L := mem_L_isPerfect hl
  obtain ⟨V,hV,_⟩ := exists_chosen_le_reduced_witness hn (ReducedModule J)
    isPReduced_reducedPSubgroup hne
  exact ⟨hn,V,hV⟩
end CFSG.Quasithin.Chapter12.Section02
