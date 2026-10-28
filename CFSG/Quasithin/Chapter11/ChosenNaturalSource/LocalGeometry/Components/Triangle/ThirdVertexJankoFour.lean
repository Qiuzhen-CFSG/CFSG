module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle.ThirdVertexComparisonSp4
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.JankoFourPlacement
public import Theory.SpecificGroups.Janko4.Model.ElementarySylowFixers
public import Theory.Alternating.Aut

/-!
# The J₄ comparison for two original local A₅ sections

The native local placement puts every normalized local A₅ section with
nontrivial two-core into an involution centralizer containing the same full
Sylow. If its two-core is trivial, the Sylow order exceeds |Aut(A₅)|, giving
a nontrivial Sylow centralizer and again such an involution. These involutions
lie in the Sylow center, which has order two. Thus both sections centralize
the same nonidentity element and cannot generate the centerless J₄ carrier.

The solvable quotient and relative-subgroup transports retain both original
locals and their Sylow normalizations. ThirdVertexQuasisimpleSp4 applies the
result to the actual common-Q join; source assembly and common-normal
existence remain with qt-d-1222-natural-relative-components.
Source: Aschbacher--Smith, A.3.14(10) and 11.1.2, printed pp.49,762--764;
native involution and Sylow-center data from GLS3 Table 5.3i, with the
existing matrix-certificate provenance preserved.
-/

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open FiveLocalFF.SolvableQuotients
public noncomputable section

private theorem five_equiv {A : Type*} [Group A]
    (hm : ClassicalGroup.IsPSL A 2 4) : Nonempty (A ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).map
    (fun a => e.trans a)

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem j4_five_involution (S : Sylow 2 Janko4.Model) (B : Subgroup Janko4.Model)
    (hl : B ∈ localCComponents S)
    (hn : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5)) :
    ∃ z : Janko4.Model, orderOf z = 2 ∧
      B ⊔ (S : Subgroup Janko4.Model) ≤ centralizer ({z} : Set Janko4.Model) := by
  by_cases hc : pCore 2 B = ⊥
  · let e : B ≃* alternatingGroup (Fin 5) :=
      ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans eB
    have hne : (S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model) ≠ ⊥ := by
      intro hz
      let f := B.normalizerMonoidHom.comp (inclusion hn)
      have hf : Function.Injective f := by
        apply (MonoidHom.ker_eq_bot_iff _).mp
        apply eq_bot_iff.mpr
        intro a ha
        apply Subtype.ext
        apply mem_bot.mp
        rw [←hz]
        refine ⟨a.property,?_⟩
        change inclusion hn a ∈ B.normalizerMonoidHom.ker at ha
        rwa [normalizerMonoidHom_ker] at ha
      let a : Equiv.Perm (Fin 5) ≃* MulAut (alternatingGroup (Fin 5)) :=
        MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
          (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by decide) (by decide))
      let j := a.symm.toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp f)
      have hj : Function.Injective j := a.symm.injective.comp ((MulAut.congr e).injective.comp hf)
      have hd := card_dvd_of_injective j hj
      rw [Janko4.OuterReduction.OddIndex.ambient_sylow_card S,Nat.card_perm,Nat.card_fin] at hd
      norm_num [Nat.factorial] at hd
    have hp := S.isPGroup'.to_le
      (inf_le_left : (S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model) ≤ S)
    have heven : 2 ∣ Nat.card (centralizer (B : Set Janko4.Model)) := by
      obtain ⟨n,hcard⟩ := hp.exists_card_eq
      have hn0 : n ≠ 0 := by
        intro hn0
        rw [hn0,pow_zero] at hcard
        exact hne (((S : Subgroup Janko4.Model) ⊓ centralizer (B : Set Janko4.Model)).eq_bot_of_card_eq hcard)
      exact (hcard ▸ dvd_pow_self 2 hn0).trans (card_dvd_of_le inf_le_right)
    exact exists_involution_centralizing_normalizing_two_group B (S : Subgroup Janko4.Model)
      S.isPGroup' hn heven
  · exact FiveLocalFF.JankoFour.involution_centralizer_placement_of_core S B hl hn eB hc

private theorem involution_mem_sylow_center {A : Type*} [Group A] [Finite A]
    (S : Sylow 2 A) (z : A) (hz : orderOf z = 2)
    (hc : (S : Subgroup A) ≤ centralizer ({z} : Set A)) :
    ∃ t : center S, (t.val.val : A) = z := by
  have hzn : z ∈ normalizer (S : Set A) := Subgroup.centralizer_le_normalizer _
    (fun x hx => mem_centralizer_singleton_iff.mp (hc hx))
  have hp : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hz,pow_one])
  have hzs : z ∈ S := ((hp.inf_normalizer_sylow S).le ⟨mem_zpowers z,hzn⟩).2
  refine ⟨⟨⟨z,hzs⟩,?_⟩,rfl⟩
  apply mem_center_iff.mpr
  intro x
  exact Subtype.ext (mem_centralizer_singleton_iff.mp (hc x.property))

/-- Two original local A₅ sections cannot generate the native J₄ carrier:
both centralize the unique involution in the center of the same full Sylow. -/
theorem j4_not_generated_by_local_five_pair (S : Sylow 2 Janko4.Model)
    (B C : Subgroup Janko4.Model)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup Janko4.Model) ≤ normalizer (B : Set Janko4.Model))
    (hnC : (S : Subgroup Janko4.Model) ≤ normalizer (C : Set Janko4.Model))
    (eB : (B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 5))
    (eC : (C ⧸ pCore 2 C) ≃* alternatingGroup (Fin 5)) : B ⊔ C ≠ ⊤ := by
  obtain ⟨z,hz,hBz⟩ := j4_five_involution S B hB hnB eB
  obtain ⟨w,hw,hCw⟩ := j4_five_involution S C hC hnC eC
  obtain ⟨t,ht⟩ := involution_mem_sylow_center S z hz (le_sup_right.trans hBz)
  obtain ⟨u,hu⟩ := involution_mem_sylow_center S w hw (le_sup_right.trans hCw)
  have ht1 : t ≠ 1 := by
    intro he
    have hh : z = 1 := ht.symm.trans (congrArg (fun a : center S => (a.val.val : Janko4.Model)) he)
    rw [hh,orderOf_one] at hz
    norm_num at hz
  have hu1 : u ≠ 1 := by
    intro he
    have hh : w = 1 := hu.symm.trans (congrArg (fun a : center S => (a.val.val : Janko4.Model)) he)
    rw [hh,orderOf_one] at hw
    norm_num at hw
  have he : z = w := ht.symm.trans ((congrArg (fun a : center S => (a.val.val : Janko4.Model))
    (((Nat.card_eq_two_iff' (1 : center S)).mp (Janko4.sylow_center_card_two S)).unique ht1 hu1)).trans hu)
  intro hgen
  have htop : (⊤ : Subgroup Janko4.Model) ≤ centralizer ({z} : Set Janko4.Model) := by
    rw [←hgen]
    exact sup_le (le_sup_left.trans hBz) (he.symm ▸ le_sup_left.trans hCw)
  have hzc : z ∈ center Janko4.Model := mem_center_iff.mpr
    (fun x => mem_centralizer_singleton_iff.mp (htop (mem_top x)))
  have hez : z = 1 := mem_bot.mp (Janko4.model_center_eq_bot ▸ hzc)
  rw [hez,orderOf_one] at hz
  norm_num at hz


/-- A solvable quotient preserves both original local A₅ sections, so their
join cannot have the native J₄ as a solvable quotient. -/
theorem no_j4_solvable_quotient_of_local_five_pair
    {A : Type*} [Group A] [Finite A] (S : Sylow 2 A) (B C : Subgroup A)
    (hB : B ∈ localCComponents S) (hC : C ∈ localCComponents S)
    (hnB : (S : Subgroup A) ≤ normalizer (B : Set A))
    (hnC : (S : Subgroup A) ≤ normalizer (C : Set A))
    (hgen : B ⊔ C = ⊤)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (f : A →* Janko4.Model) (hf : Function.Surjective f)
    [Group.IsSolvable f.ker] : False := by
  apply j4_not_generated_by_local_five_pair (S.mapSurjective hf) (B.map f) (C.map f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB f)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hC f)
    ((map_mono hnB).trans (le_normalizer_map f))
    ((map_mono hnC).trans (le_normalizer_map f))
    (section_map f B hB (five_equiv hmB).some).some
    (section_map f C hC (five_equiv hmC).some).some
  rw [←Subgroup.map_sup,hgen,map_top_of_surjective f hf]

/-- The literal local join has no J₄ two-core quotient. -/
theorem local_join_not_j4
    {G : Type*} [Group G] [Finite G] (T : Sylow 2 G) {B C I : Subgroup G}
    (hB : B ∈ localCComponents T) (hC : C ∈ localCComponents T)
    (hI : I ∈ localCComponents T) (hBI : B ≤ I) (hCI : C ≤ I)
    (hnB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hnC : (T : Subgroup G) ≤ normalizer (C : Set G))
    (hgen : B ⊔ C = I)
    (hmB : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4)
    (hmC : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ¬ Nonempty ((I ⧸ pCore 2 I) ≃* Janko4.Model) := by
  obtain ⟨S,hS,hBS⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hI hBI
  have hCS : C.subgroupOf I ∈ localCComponents S := hS.symm ▸ local_restrict hC hCI
  let q := QuotientGroup.mk' (pCore 2 I)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : Group.IsNilpotent q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isNilpotent
  let : Group.IsSolvable q.ker := inferInstance
  have hgen' : B.subgroupOf I ⊔ C.subgroupOf I = ⊤ := by
    rw [←subgroupOf_sup hBI hCI,hgen,subgroupOf_self]
  let b := subgroupOfEquivOfLe hBI
  let c := subgroupOfEquivOfLe hCI
  let bq := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  rintro ⟨e⟩
  let k := e.toMonoidHom.comp q
  let : Group.IsSolvable k.ker := by
    rw [MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective]
    infer_instance
  exact no_j4_solvable_quotient_of_local_five_pair S (B.subgroupOf I) (C.subgroupOf I)
    hBS hCS (by
      rw [hS,←subgroupOf_normalizer_eq hBI]
      exact comap_mono hnB) (by
      rw [hS,←subgroupOf_normalizer_eq hCI]
      exact comap_mono hnC) hgen' (hmB.of_mulEquiv bq) (hmC.of_mulEquiv cq)
    k (e.surjective.comp hq)


end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Triangle
