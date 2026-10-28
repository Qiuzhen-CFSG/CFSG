module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.Normalized
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SmallAlternating
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.MovedMaximality
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Membership
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Embedding.RankOne
public import Theory.SpecificGroups.SL2.PrimeFiveEquiv
public import Theory.SpecificGroups.AlternatingFiveCore
public import Theory.GroupTheory.NormalSylowQuotientAction
public import Theory.GroupTheory.PCoreSurjective.OddExtension

/-!
# Rank-one exclusions for proper point overcomponents

Restrict the original full Sylow to its normalized containing component J.
Solvability of proper Sylow overgroups lifts through the literal O₂(J)
quotient and forces equality of local components. This excludes Bender
quotients and the small alternating groups, including the central triple
cover of A₆.

For odd-prime PSL₂, the proper point image is A₅. For quadratic-prime PSL₂,
the original binary seed first forces the parameter five, after which the
point image is again A₅. The induced two-core quotient equivalences retain
the original inclusions. In both cases the source seed would fill the point
component, contradicting strict comparison.

These are exclusions in the full proper-overcomponent sieve, not a proof
of its remaining six pairs or of Kz = K. The literal chosen-flag consumers
are in Comparison.Overcomponent.EmbeddingProof. Earlier source inputs retain
final discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith 11.4.2, printed p.776, using A.3.12(8), pp.47--48.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- Solvable proper Sylow overgroups of the literal containing quotient force equality before quotienting. -/
theorem local_eq_of_quotient_sylow_solvable {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) (hBJ : B ≤ J)
    (hproper : SolvableSylowOvergroups (J ⧸ pCore 2 J)) : B = J := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  have hb : B.subgroupOf J ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hB.1 hBJ
  have hj : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  have he := eq_of_solvable_sylow_overgroups P hb hj le_top
    (fun S Q hSQ hQ => isSolvable_proper_sylow_overgroup_of_equiv topEquiv
      (isSolvable_proper_sylow_overgroup_of_twoCore_quotient hproper) S Q hSQ hQ)
  exact le_antisymm hBJ (subgroupOf_eq_top.mp he)

/-- A proper local component in a prime PSL₂ two-core quotient has its own literal two-core quotient isomorphic to A₅. -/
theorem prime_quotient_forces_five {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) (hBJ : B < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 p) :
    Chapter1.Section02.LocalModels.IsAlternating (B ⧸ pCore 2 B) 5 := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  let C := B.subgroupOf J
  have hc : C ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hB.1 hBJ.le
  have hj : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let q := QuotientGroup.mk' (pCore 2 J)
  let := pCore_isNilpotent (p := 2) (G := J)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hcm : C.map q ∈ localCComponents Q :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hc q
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    simpa only [map_top_of_surjective (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)] using
      hj.map_quotient (pCore 2 J)
  have hne : C.map q ≠ ⊤ := by
    intro he
    have he' : C.map q = (⊤ : Subgroup J).map q := by
      rwa [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    have ht := Chapter1.Section02.MovedMaximality.eq_of_twoCore_images_eq P hc hj le_top he'
    exact hBJ.not_ge (subgroupOf_eq_top.mp ht)
  obtain ⟨_,⟨e⟩⟩ := proper_primePSL2_models Q hcm htop le_top hne hp ho
    (hm.of_mulEquiv topEquiv)
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap C)
    (q.subgroupMap_surjective C) hk
  let b := subgroupOfEquivOfLe hBJ.le
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact ⟨bq.symm.trans (a.trans ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
      QuotientGroup.quotientBot)))⟩

/-- The quadratic parameter five likewise gives the actual A₅ two-core quotient of the smaller component. -/
theorem twenty_five_quotient_forces_five {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G)) (hBJ : B < J)
    (hm : ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 25) :
    Chapter1.Section02.LocalModels.IsAlternating (B ⧸ pCore 2 B) 5 := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J hTJ
  let C := B.subgroupOf J
  have hc : C ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hB.1 hBJ.le
  have hj : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let q := QuotientGroup.mk' (pCore 2 J)
  let := pCore_isNilpotent (p := 2) (G := J)
  let : Group.IsSolvable q.ker := by rw [QuotientGroup.ker_mk']; infer_instance
  let Q := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hcm : C.map q ∈ localCComponents Q :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hc q
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    simpa only [map_top_of_surjective (QuotientGroup.mk' (pCore 2 J)) (QuotientGroup.mk'_surjective _)] using
      hj.map_quotient (pCore 2 J)
  have hne : C.map q ≠ ⊤ := by
    intro he
    have he' : C.map q = (⊤ : Subgroup J).map q := by
      rwa [map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    have ht := Chapter1.Section02.MovedMaximality.eq_of_twoCore_images_eq P hc hj le_top he'
    exact hBJ.not_ge (subgroupOf_eq_top.mp ht)
  obtain ⟨_,hm'⟩ := proper_quadraticPSL2_models Q hcm htop le_top hne
    (p := 5) (by decide) (by decide) (hm.of_mulEquiv topEquiv)
  obtain ⟨F,_,_,hF,⟨eF⟩⟩ := hm'
  let : Fintype F := Fintype.ofFinite F
  let aF : F ≃+* ZMod 5 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  let e := eF.trans ((GorensteinWalter.psl2RingEquiv aF).trans
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some)
  have hk : IsPGroup 2 (q.subgroupMap C).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := MonoidHom.quotientPCoreEquivOfSurjective (q.subgroupMap C)
    (q.subgroupMap_surjective C) hk
  let b := subgroupOfEquivOfLe hBJ.le
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact ⟨bq.symm.trans (a.trans ((QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).trans
    ((QuotientGroup.quotientMulEquivOfEq alternatingGroup.five_twoCore_eq_bot).trans
      QuotientGroup.quotientBot)))⟩

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- A proper point overcomponent cannot have solvable proper Sylow overgroups modulo its two-core. -/
theorem not_solvable_sylow_quotient (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ¬ SolvableSylowOvergroups (J ⧸ pCore 2 J) := by
  intro hp
  exact hlt.ne (local_eq_of_quotient_sylow_solvable h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) hlt.le hp)

/-- Exclude all three Bender containing families with their original quotient models. -/
theorem not_bender_quotient (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ¬ ClassificationModels.IsBenderModel (J ⧸ pCore 2 J) := by
  intro hm
  exact not_solvable_sylow_quotient h hJ hlt
    (bender_solvable_proper_sylow_overgroup hm)

/-- Exclude A₅, A₆ and the genuine central triple cover of A₆ as containing quotients. -/
theorem not_small_alternating_quotient (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ¬ (Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 5 ∨
      Chapter1.Section02.LocalModels.IsAlternating (J ⧸ pCore 2 J) 6 ∨
      Chapter1.Section02.LocalModels.IsAlternatingCover (J ⧸ pCore 2 J) 6) := by
  intro hm
  apply not_solvable_sylow_quotient h hJ hlt
  rcases hm with hm | hm | hm
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  · obtain ⟨e⟩ := hm
    exact SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable
  · obtain ⟨hq,_,⟨e⟩⟩ := hm
    let := hq
    exact SolvableSylowOvergroups.of_central_quotient (QuotientGroup.mk' (center _))
      (QuotientGroup.mk'_surjective _) (by simp)
      (SolvableSylowOvergroups.of_equiv e AlternatingSix.ProperSylowOvergroups.isSolvable)
/-- Strict comparison excludes every odd-prime PSL₂ containing quotient: the resulting A₅ point quotient cannot properly contain the original seed. -/
theorem not_prime_psl2_quotient (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hseed : E.L₁ ∈ Chapter1.L G (T : Subgroup G)) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 p := by
  intro hm
  obtain ⟨e⟩ := prime_quotient_forces_five h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) hlt hp ho hm
  have hs : SolvableSylowOvergroups (E.Kz ⧸ pCore 2 E.Kz) :=
    SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  have he := local_eq_of_quotient_sylow_solvable hseed h.point_mem_local_family
    (sylow_normalizes_point h) (le_conjugateSpanBy _ _) hs
  exact (h.strict_comparison hf hne).2.1.ne he

/-- The original nonbinary seed and strict point comparison exclude every odd quadratic-prime PSL₂ containing quotient. -/
theorem not_quadratic_psl2_quotient (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hseed : E.L₁ ∈ Chapter1.L G (T : Subgroup G))
    (hmseed : ClassicalGroup.IsPSL (E.L₁ ⧸ pCore 2 E.L₁) 2 (2 ^ E.input.field.degree))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 2 (p ^ 2) := by
  intro hm
  have hseedJ : E.L₁ < J := lt_trans (h.strict_comparison hf hne).2.1 hlt
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T J
    (sylow_normalizes_overcomponent h hJ hlt.le)
  have hs : E.L₁.subgroupOf J ∈ localCComponents P := by
    rw [hP]
    exact local_restrict hseed.1 hseedJ.le
  have hj : (⊤ : Subgroup J).IsCComponent := by
    simpa only [subgroupOf_self] using hJ.1.subgroupOf_of_le le_rfl le_sup_left
  let eS := subgroupOfEquivOfLe hseedJ.le
  let eqS := QuotientGroup.congr _ _ eS (pCore_map_iso 2 eS)
  let eqJ := QuotientGroup.congr _ _ (topEquiv (G := J))
    (pCore_map_iso 2 (topEquiv (G := J)))
  have hproper : E.L₁.subgroupOf J < ⊤ := lt_top_iff_ne_top.mpr
    (fun he => hseedJ.not_ge (subgroupOf_eq_top.mp he))
  have hp5 := (LocalGeometry.Components.Embedding.proper_quadratic_rank_one_parameters
    P hs hj hproper E.input.nonbinary (hmseed.of_mulEquiv eqS) hp ho
    (hm.of_mulEquiv eqJ)).2
  subst p
  obtain ⟨e⟩ := twenty_five_quotient_forces_five h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) hlt hm
  have hs : SolvableSylowOvergroups (E.Kz ⧸ pCore 2 E.Kz) :=
    SolvableSylowOvergroups.of_equiv e (fun _ P _ hP =>
      alternatingGroup.isSolvable_subgroup_five_of_ne_top P hP)
  have he := local_eq_of_quotient_sylow_solvable hseed h.point_mem_local_family
    (sylow_normalizes_point h) (le_conjugateSpanBy _ _) hs
  exact (h.strict_comparison hf hne).2.1.ne he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
