module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.RankTwoSeedSource
public import Theory.GroupTheory.CComponent.NonsolvableNormalIntersection
public import Theory.GroupTheory.ComponentLocalPrimeFree
public import Theory.GroupTheory.PResidual.PrimeToTransport
/-!
# The canonical cubic residual and its simple two-core quotient

The original simple-core seed has three-prime center modulo the ambient
two-core. Rank addition makes every other component three-prime. Their
images generate a three-prime quotient of the component layer, so its cubic
residual lies in the selected component. The residual contains the nonsolvable
seed, and component minimality gives equality. The source generation theorem
identifies the layer with the solvable residual, retaining both literal maps.

The same rank argument excludes the possible cubic center of the selected
component's quasisimple head. The proved A.3.6 center bound then makes that
head simple. No universal A.3.18 proposition is assumed.

Source: Aschbacher--Smith, 12.6.3 and 12.6.13(2), printed pp.824,826,
using 1.2.1, A.3.6 and the rank argument of A.3.18.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open IndexTwo
variable {G : Type*} [Group G] [Finite G]

theorem other_component_three_free_of_simple_core_seed
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B C : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hC : C.IsCComponent) (hBC : B ≤ C) (hrB : 2 ≤ primeRank 3 B)
    {D : Subgroup G} (hD : D.IsCComponent) (hDC : D ≠ C) :
    Nat.Coprime 3 (Nat.card D) := by
  let A := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let X := B.map q
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := f) (q.subgroupMap_surjective B)
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.symm.isSimpleGroup
  have hcX : center X ≤ pCore 2 X := by
    rw [←PerfectCoreTwoExtension.radical_eq_core (G := X)]
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  have hz : Nat.Coprime 3 (Nat.card (center X)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hcX).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hf : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrX : 2 ≤ primeRank 3 X := hrB.trans (primeRank_le_of_coprime_ker 3 f hf)
  have hA : IsSQTK KnownSimple.IsKnownSimple A := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  have hcomm : D.map q ≤ centralizer (X : Set A) := by
    apply (commutator_eq_bot_iff_le_centralizer.mp
      (ChapterA.Section03.CComponentCommutation.commutator_eq_bot hA
        (pCore_quotient_pCore_eq_bot 2) (hD.map_quotient _) (hC.map_quotient _)
        (fun he => hDC (hD.eq_of_map_quotient_eq hC _ he)))).trans
    exact centralizer_le (map_mono hBC)
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime (D.map q) X hcomm hz
  have hbound : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := hA.stronglyQuasithin 3 (by decide) (by decide)
  have hzero : primeRank 3 (D.map q) = 0 := by omega
  have hcop : Nat.Coprime 3 (Nat.card (D ⧸ pCore 2 D)) := by
    rw [Nat.card_congr (cComponentTwoCoreQuotientEquiv hD).toEquiv]
    exact Nat.prime_three.coprime_iff_not_dvd.mpr (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero)
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D)]
  apply hcop.mul_right
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
  rw [hn]
  exact (by decide : Nat.Coprime 3 2).pow_right n

/-- The unique cubic component is the embedded prime-to-three residual of the layer. -/
theorem component_eq_layer_threeResidual
    (C : Subgroup G) (hC : C.IsCComponent)
    (hother : ∀ D : Subgroup G, D.IsCComponent → D ≠ C → Nat.Coprime 3 (Nat.card D))
    (B : Subgroup G) (hB : ¬ Group.IsSolvable B) (hBC : B ≤ C)
    (hB3 : primeToResidual 3 B = ⊤) :
    C = (primeToResidual 3 (cComponentLayer G)).map (cComponentLayer G).subtype := by
  classical
  let E := cComponentLayer G
  let C₀ := C.subgroupOf E
  have hCE : C ≤ E := le_cComponentLayer hC
  let : C₀.Normal := normal_subgroupOf_of_le_normalizer (cComponentLayer_le_normalizer hC)
  let q := QuotientGroup.mk' C₀
  let F (D : ComponentIndex G) : Subgroup (E ⧸ C₀) := (D.1.subgroupOf E).map q
  have hn (D : ComponentIndex G) : (F D).Normal := by
    let : (D.1.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer
      (cComponentLayer_le_normalizer D.property)
    exact (inferInstance : (D.1.subgroupOf E).Normal).map q (QuotientGroup.mk'_surjective _)
  have hfree (D : ComponentIndex G) : ¬3 ∣ Nat.card (F D) := by
    by_cases he : D.1 = C
    · have hzero : F D = ⊥ := by
        change (D.1.subgroupOf E).map q = ⊥
        rw [he]
        exact (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' C₀).ge
      rw [hzero,card_bot]
      decide
    · apply Nat.prime_three.coprime_iff_not_dvd.mp
      apply (hother D.1 D.property he).coprime_dvd_right
      have hd := card_map_dvd (D.1.subgroupOf E) q
      rw [Nat.card_congr (subgroupOfEquivOfLe (le_cComponentLayer D.property)).toEquiv] at hd
      exact hd
  have hgen : (⨆ D : ComponentIndex G, D.1.subgroupOf E) = ⊤ := by
    apply map_injective E.subtype_injective
    rw [Subgroup.map_iSup,←MonoidHom.range_eq_map,range_subtype]
    exact (iSup_congr fun D : ComponentIndex G =>
      map_subgroupOf_eq_of_le (le_cComponentLayer D.property)).trans (sSup_eq_iSup' _).symm
  have hgenF : (⨆ D, F D) = ⊤ := by
    change (⨆ D : ComponentIndex G, (D.1.subgroupOf E).map q) = ⊤
    rw [←Subgroup.map_iSup,hgen,map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  have hfreeQ : Nat.Coprime 3 (Nat.card (E ⧸ C₀)) := by
    have hh := not_dvd_card_iSup_of_normalizes Nat.prime_three F
      (fun D J => by let := hn J; rw [normalizer_eq_top]; exact le_top) hfree
    rw [hgenF,card_top] at hh
    exact Nat.prime_three.coprime_iff_not_dvd.mpr hh
  have hr : primeToResidual 3 E ≤ C₀ := primeToResidual_le C₀
    (by simpa only [index_eq_card] using hfreeQ)
  have hRC : (primeToResidual 3 E).map E.subtype ≤ C :=
    (map_mono hr).trans_eq (map_subgroupOf_eq_of_le hCE)
  let R := (primeToResidual 3 E).map E.subtype
  have hnR : R.Normal := by
    let : E.Characteristic := cComponentLayer_characteristic
    let : E.Normal := inferInstance
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←E.normalizer_eq_top]
    exact normalizer_le_normalizer_characteristic_image E (primeToResidual 3 E)
  let := hnR
  have hBR : B ≤ R := by
    have hh := embedded_primeToResidual_mono 3 (hBC.trans hCE)
    rwa [hB3,←MonoidHom.range_eq_map,range_subtype] at hh
  exact le_antisymm (hC.le_normal_of_nonsolvable_subgroup hB hBC hBR) hRC
end CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
/-- The canonical cubic residual of the perfect residual is the actual containing component. -/
theorem simple_core_rank_threeResidual_source
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 B)
    (hB3 : primeToResidual 3 B = ⊤) :
    let R := (primeToResidual 3 (solvableResidual G)).map (solvableResidual G).subtype
    R.IsCComponent ∧ B ≤ R ∧ R.Normal ∧ IsQuasisimple (R ⧸ pCore 2 R) := by
  obtain ⟨C,⟨hC,hBC,hn,hq⟩,_⟩ := simple_core_rank_component_source hG B hB hrB
  have hsol : ¬Group.IsSolvable B := by
    intro h
    let := h
    exact hB.not_isSolvable inferInstance
  have he := component_eq_layer_threeResidual C hC
    (fun D hD hDC => other_component_three_free_of_simple_core_seed hG B C hC hBC hrB hD hDC)
    B hsol hBC hB3
  have hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G) := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  have hgen : cComponentLayer G = solvableResidual G :=
    proposition_1_2_1_one_of_A_3_9
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO) hQ
  rw [hgen] at he
  exact he ▸ ⟨hC,hBC,hn,hq⟩
end CFSG.Quasithin.Chapter1.Section02

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open ChapterA.SQTKStructure
variable {G : Type*} [Group G] [Finite G]

/-- A rank-two simple-core seed excludes the possible cubic center of its containing head. -/
theorem simple_head_of_simple_core_rank_seed
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B C : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hC : C.IsCComponent) (hBC : B ≤ C) (hrB : 2 ≤ primeRank 3 B) :
    IsSimpleGroup (C ⧸ pCore 2 C) := by
  let A := G ⧸ pCore 2 G
  let q := QuotientGroup.mk' (pCore 2 G)
  let D := C.map q
  let X := B.map q
  let f := q.subgroupMap B
  have hk : IsPGroup 2 f.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective B.subtype B.subtype_injective
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := f) (q.subgroupMap_surjective B)
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f (q.subgroupMap_surjective B)
  let : IsSimpleGroup (X ⧸ pCore 2 X) := e.symm.isSimpleGroup
  have hcX : center X ≤ pCore 2 X := by
    rw [←PerfectCoreTwoExtension.radical_eq_core (G := X)]
    exact le_solvableRadical _ inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  have hzX : Nat.Coprime 3 (Nat.card (center X)) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup.to_le hcX).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hf : Nat.Coprime 3 (Nat.card f.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrX : 2 ≤ primeRank 3 X := hrB.trans (primeRank_le_of_coprime_ker 3 f hf)
  have hA : IsSQTK KnownSimple.IsKnownSimple A := by
    refine ⟨?_,hG.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hG.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isNilpotent
  let eC := cComponentTwoCoreQuotientEquiv hC
  let : IsQuasisimple (C ⧸ pCore 2 C) :=
    ChapterA.Section03.cComponent_twoCore_quasisimple_of_three_rank hG hC
      (hrB.trans (primeRank_mono 3 hBC))
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv eC
  have hD : IsComponent A D := ⟨(hC.map_quotient _).subnormal,inferInstance⟩
  let Z := (center D).map D.subtype
  have hZX : Z ≤ centralizer (X : Set A) := by
    rintro z ⟨z,hz,rfl⟩ x hx
    exact congrArg Subtype.val (mem_center_iff.mp hz ⟨x,map_mono hBC hx⟩)
  have hadd := ResidualCentralizerRank.primeRank_add_le_of_center_coprime Z X hZX hzX
  have hbound : primeRank 3 (G ⧸ pCore 2 G) ≤ 2 := hA.stronglyQuasithin 3 (by decide) (by decide)
  have hzero : primeRank 3 Z = 0 := by omega
  have h3 : ¬3 ∣ Nat.card (center D) := by
    have hh := PrimeRank.eq_zero_iff_not_dvd_card.mp hzero
    rwa [card_map_of_injective D.subtype_injective] at hh
  have hfD : fittingSubgroup D ≤ center D :=
    (le_solvableRadical _ inferInstance inferInstance).trans IsQuasisimple.solvableRadical_le_center
  have hm := (ordinary_model_of_central_fitting
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) hA D hD.isCComponent hfD).2
  have hc := NonnormalOuterSource.FourModels.center_card_of_common
    (OrdinarySource.ordinary_conclusion_of_model (pCore_quotient_pCore_eq_bot 2) D hD hm).2
  have hz : center D = ⊥ := (eq_bot_iff_card _).mpr (hc.resolve_right (fun he => h3 (he ▸ dvd_rfl)))
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : IsSimpleGroup D := ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  exact eC.isSimpleGroup
end CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter1.Section02
variable {G : Type*} [Group G] [Finite G]
/-- Recognition of the canonical cubic residual includes its simple two-core head. -/
theorem simple_core_rank_threeResidual_recognition
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (B : Subgroup G) [Group.IsPerfect B] [IsSimpleGroup (B ⧸ pCore 2 B)]
    (hB : (⊤ : Subgroup B).IsCComponent) (hrB : 2 ≤ primeRank 3 B)
    (hB3 : primeToResidual 3 B = ⊤) :
    let R := (primeToResidual 3 (solvableResidual G)).map (solvableResidual G).subtype
    R.IsCComponent ∧ B ≤ R ∧ R.Normal ∧ IsQuasisimple (R ⧸ pCore 2 R) ∧
      IsSimpleGroup (R ⧸ pCore 2 R) := by
  obtain ⟨hc,hBR,hn,hq⟩ := simple_core_rank_threeResidual_source hG B hB hrB hB3
  exact ⟨hc,hBR,hn,hq,simple_head_of_simple_core_rank_seed hG B _ hc hBR hrB⟩
end CFSG.Quasithin.Chapter1.Section02
