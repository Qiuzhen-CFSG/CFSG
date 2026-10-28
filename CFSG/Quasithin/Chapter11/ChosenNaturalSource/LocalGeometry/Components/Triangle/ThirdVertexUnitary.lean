module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexComparisonSp4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection
public import Theory.SpecificGroups.SU3.OddSylowCenter
public import Theory.SpecificGroups.SU3.Quasisimplicity

/-!
# Excluding the two unitary field-five rows at the third vertex

A normalized local A₅ section in PSU₃(5) has nontrivial two-core: otherwise
it would be an actual A₅ normalized by a full Sylow, which the odd ternary
calculation excludes. The ambient two-rank bound supplies an involution
centralized by that local subgroup and the Sylow. The Sylow center has
order two, so both original local subgroups centralize the same involution.
They cannot generate the centerless projective group.

A solvable quotient preserves the perfect locals' actual A₅ two-core
quotients and their common full Sylow. This excludes SU₃(5) through its
literal scalar projection as well. The final theorem retains the original
join I, restrictions to I and map I → I/O₂(I). Its actual common-Q triangle
application is in ThirdVertexSylowSp4, with no extra unitary recognition
premise. Common-normal existence, the remaining comparisons and both final
orientations stay with qt-d-1222-natural-relative-components.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
A.3.14 and 11.1.2, printed pp.49--50,762--764; the native Sylow-center
calculation cites ABG II.2 Lemma 1.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
public noncomputable section

private theorem involution_mem_sylow_center {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (z : A) (hz : orderOf z = 2)
    (hS : (S : Subgroup A) ≤ centralizer ({z} : Set A)) :
    ∃ w : center S, ((w : S) : A) = z := by
  have hzC : z ∈ centralizer (S : Set A) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mp (hS hs)
  have hn : zpowers z ≤ normalizer (S : Set A) :=
    (zpowers_le.mpr hzC).trans (Subgroup.centralizer_le_normalizer _)
  have htwo : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hz]; rfl)
  have hZS : zpowers z ≤ (S : Subgroup A) := sup_le_iff.mp
    (S.is_maximal' (S.isPGroup'.to_sup_of_normal_left' htwo hn) le_sup_left).le |>.2
  have hzS : z ∈ S := hZS (mem_zpowers z)
  refine ⟨⟨⟨z,hzS⟩,?_⟩,rfl⟩
  exact mem_center_iff.mpr fun s => Subtype.ext (hzC s s.property)

private theorem unitary_five_pair_impossible
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hSB : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hSC : (S : Subgroup A) ≤ normalizer (C : Set A))
    (hgen : B ⊔ C = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (hm : ClassicalGroup.IsPSU A 3 5) : False := by
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hF)
      (by simpa only [pow_one] using hconj)
  let := J.projective_isPerfect_of_fixed_card (by decide : 2 < 5) hF hfixed
  let := BenderSuzuki.External.huppert_II_10_13 J 5 (by decide) hF hfixed
  let : IsSimpleGroup A := e.isSimpleGroup
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := e.symm.toMonoidHom) e.symm.surjective
  have hcenter : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he)).elim
  have hr : primeRank 2 A ≤ 2 := by
    rw [primeRank_congr 2 e]
    exact Theory.SpecificGroups.OddThreeRank.psu3_primeRank_two_le J
      (by decide : Nat.Prime 5) (by decide) hF hconj
  have hscenter : Nat.card (center S) = 2 := by
    let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let a : S ≃* Q := (S : Subgroup A).equivMapOfInjective e.toMonoidHom e.injective
    rw [Nat.card_congr (centerCongr a).toEquiv]
    exact BenderSuzuki.MatrixGroups.HermitianForm.OddSylowCenter.card_center
      J (by decide : Nat.Prime 5) (by decide) (by decide) hF hconj Q
  have step (D : Subgroup A) (hD : D ∈ localCComponents S)
      (hSD : (S : Subgroup A) ≤ normalizer (D : Set A))
      (eD : (D ⧸ pCore 2 D) ≃* alternatingGroup (Fin 5)) :
      ∃ z : A, orderOf z = 2 ∧ D ⊔ (S : Subgroup A) ≤ centralizer ({z} : Set A) := by
    let := FiveLocalFF.SolvableQuotients.local_perfect hD
    have hc : pCore 2 D ≠ ⊥ := by
      intro hc
      let a : D ≃* D ⧸ pCore 2 D := QuotientGroup.quotientBot.symm.trans
        (QuotientGroup.quotientMulEquivOfEq hc).symm
      exact AlternatingFive.not_odd_unitary S hD hSD (a.trans eD)
        (by decide : Nat.Prime 5) (by decide)
        ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨e⟩⟩
    obtain ⟨z,_,hz,hd⟩ := exists_involution_centralized_by_perfect_sup_sylow S D hr hSD hc
    exact ⟨z,hz,hd⟩
  obtain ⟨z,hz,hzB⟩ := step B hB hSB eB
  obtain ⟨w,hw,hwC⟩ := step C hC hSC eC
  obtain ⟨zs,hzs⟩ := involution_mem_sylow_center S z hz (le_sup_right.trans hzB)
  obtain ⟨ws,hws⟩ := involution_mem_sylow_center S w hw (le_sup_right.trans hwC)
  let : IsCyclic (center S) := isCyclic_of_prime_card hscenter
  have he : zs = ws := IsCyclic.eq_of_orderOf_eq_two
    (by simpa only [←hzs,orderOf_coe] using hz)
    (by simpa only [←hws,orderOf_coe] using hw)
  have hzw : z = w := hzs.symm.trans ((congrArg (fun a : center S => ((a : S) : A)) he).trans hws)
  have hcentral : (⊤ : Subgroup A) ≤ centralizer ({z} : Set A) := by
    rw [←hgen]
    exact sup_le (le_sup_left.trans hzB) (hzw.symm ▸ le_sup_left.trans hwC)
  have hzc : z ∈ center A := mem_center_iff.mpr fun a =>
    mem_centralizer_singleton_iff.mp (hcentral (mem_top a))
  have hez : z = 1 := by simpa only [hcenter,mem_bot] using hzc
  simp [hez] at hz

/-- Two original normalized local A₅ sections cannot generate a group
with a solvable quotient PSU₃(5). The full common Sylow is essential. -/
theorem no_unitary_five_solvable_quotient_of_local_five_pair
    {A H : Type*} [Group A] [Finite A] [Group H] [Finite H]
    (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hSB : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hSC : (S : Subgroup A) ≤ normalizer (C : Set A))
    (hgen : B ⊔ C = ⊤)
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5))
    (f : A →* H) (hf : Function.Surjective f) [Group.IsSolvable f.ker]
    (hm : ClassicalGroup.IsPSU H 3 5) : False := by
  apply unitary_five_pair_impossible (S.mapSurjective hf) (B.map f) (C.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hC f)
    ((map_mono hSB).trans (le_normalizer_map f))
    ((map_mono hSC).trans (le_normalizer_map f)) ?_
    (FiveLocalFF.SolvableQuotients.section_map f B hB eB).some
    (FiveLocalFF.SolvableQuotients.section_map f C hC eC).some hm
  rw [←Subgroup.map_sup,hgen,map_top_of_surjective f hf]

/-- The actual join excludes both unitary field-five models, including
the special-unitary central cover, through the original quotient maps. -/
theorem local_join_not_unitary_five
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C I : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B ≤ I) (hCI : C ≤ I)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hTC : (T : Subgroup G) ≤ normalizer (C : Set G)) (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ¬ (ClassicalGroup.IsPSU (I ⧸ pCore 2 I) 3 5 ∨
      Chapter1.Section02.LocalModels.IsSU (I ⧸ pCore 2 I) 3 5) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI
  have hCS : C.subgroupOf I ∈ localCComponents S := hS.symm ▸ local_restrict hC hCI
  have hSB : (S : Subgroup I) ≤ normalizer (B.subgroupOf I : Set I) := by
    rw [hS,←subgroupOf_normalizer_eq hBI]
    exact comap_mono hTB
  have hSC : (S : Subgroup I) ≤ normalizer (C.subgroupOf I : Set I) := by
    rw [hS,←subgroupOf_normalizer_eq hCI]
    exact comap_mono hTC
  let q := QuotientGroup.mk' (pCore 2 I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : Group.IsNilpotent q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hgen' : B.subgroupOf I ⊔ C.subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hBI hCI,hgen,subgroupOf_self]
  have five (D : Subgroup G) (hd : D ≤ I)
      (hm : ClassicalGroup.IsPSL (D ⧸ pCore 2 D) 2 4) :
      Nonempty ((D.subgroupOf I ⧸ pCore 2 (D.subgroupOf I)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    obtain ⟨ef⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
    let d := subgroupOfEquivOfLe hd
    exact ⟨(QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans (e.trans ef)⟩
  have step {H : Type} [Group H] [Finite H]
      (k : (I ⧸ pCore 2 I) →* H) (hk : Function.Surjective k)
      (hks : Group.IsSolvable k.ker) (hm : ClassicalGroup.IsPSU H 3 5) : False := by
    let := hks
    let : Group.IsSolvable (k.comp q).ker := by
      rw [← MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker q k.ker
    exact no_unitary_five_solvable_quotient_of_local_five_pair S (B.subgroupOf I)
      (C.subgroupOf I) hBS hCS hSB hSC hgen' (five B hBI hmB).some (five C hCI hmC).some
      (k.comp q) (hk.comp hq) hm
  intro hm
  rcases hm with hm | hm
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    apply step e.toMonoidHom e.surjective ?_
      ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨MulEquiv.refl _⟩⟩
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  · obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
    let k := J.specialToProjective.comp e.toMonoidHom
    apply step k (J.specialToProjective_surjective.comp e.surjective) ?_
      ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨MulEquiv.refl _⟩⟩
    let : Group.IsSolvable J.specialToProjective.ker := Group.isSolvable_of_comm
      (fun a b => Subtype.ext ((mem_center_iff.mp (J.specialToProjective_ker_le_center a.property)) b).symm)
    let : Group.IsSolvable e.toMonoidHom.ker := by
      rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
      infer_instance
    change Group.IsSolvable (J.specialToProjective.comp e.toMonoidHom).ker
    rw [←MonoidHom.comap_ker]
    exact isSolvable_comap_of_solvable_ker e.toMonoidHom J.specialToProjective.ker


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
