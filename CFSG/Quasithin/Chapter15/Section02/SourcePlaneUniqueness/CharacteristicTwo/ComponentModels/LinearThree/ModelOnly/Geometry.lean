module

public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryGeometry

/-!
# Binary component geometry from the full quotient model

The literal C.2.3 input, marked star parabolic and full X/O2(X) model
suffice for the binary geometry used in original 15.2.23. The canonical
core-to-star map is bijective. The actual H intersection is the opposite
parabolic, and its two-residual gives the original cubic factor. Quasithin
rank control makes that factor proper and supplies reducibility.

This is the model-only form of the earlier LinearThree quotient and
intersection arguments. Its separate Branch record contains no classified
MS alternatives; the established Branch and all its public APIs are kept.
The later Source module constructs this record on the original selected X.

Source: Aschbacher--Smith 15.2.23, printed p.1116, and C.2.7(g), p.145.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

variable {G : Type*} [Group G]

/-- The original C.2.3 input, star parabolic and full component quotient. -/
structure Branch (M I X : Subgroup G) (n : ℕ) (F : Type)
    [Field F] [Finite F] : Prop where
  input : Input KnownSimple.IsKnownSimple I ((M ⊓ I).pCoreIn 2) (M ⊓ I) X
  positive : 1 ≤ n
  field_card : Nat.card F = 2 ^ n
  parabolic : IsLinearMaximalParabolic
    ((starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
      (starImage X ((M ⊓ I).pCoreIn 2) X)) 3 F
  model : Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.SpecialLinearGroup (Fin 3) F)

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
open Chapter1.RadicalExclusions.ModelReduction
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

variable {G : Type*} [Group G] [Finite G]
variable {M I X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]

/-- The two displayed SL₃ models force the canonical quotient map to be bijective. -/
theorem Branch.coreToStar_bijective (b : Branch M I X n F) :
    Function.Bijective (coreToStar b.input.normalizes) := by
  obtain ⟨e⟩ := b.model
  obtain ⟨e', _⟩ := b.parabolic
  exact (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨coreToStar_surjective b.input.normalizes,
      (Nat.card_congr e.toEquiv).trans (Nat.card_congr e'.toEquiv).symm⟩

/-- The canonical identification of the core quotient with the star component. -/
noncomputable def Branch.coreStarEquiv (b : Branch M I X n F) :
    (X ⧸ pCore 2 X) ≃* starImage X ((M ⊓ I).pCoreIn 2) X :=
  MulEquiv.ofBijective (coreToStar b.input.normalizes) b.coreToStar_bijective

/-- The identification preserves the original quotient maps. -/
theorem Branch.coreStarEquiv_mk (b : Branch M I X n F) (x : X) :
    b.coreStarEquiv (QuotientGroup.mk' (pCore 2 X) x) =
      toStarImage X ((M ⊓ I).pCoreIn 2) x := by rfl

/-- On X, the actual star kernel is exactly O₂(X). -/
theorem Branch.toStarImage_ker (b : Branch M I X n F) :
    (toStarImage X ((M ⊓ I).pCoreIn 2)).ker = pCore 2 X := by
  apply le_antisymm
  · intro x hx
    apply (QuotientGroup.eq_one_iff x).mp
    apply b.coreToStar_bijective.1
    change coreToStar b.input.normalizes (QuotientGroup.mk' (pCore 2 X) x) =
      coreToStar b.input.normalizes 1
    rw [coreToStar_mk, map_one]
    exact hx
  · exact core_le_toStarImage_ker b.input.normalizes

omit [Finite G] in
private theorem map_intersection_toStar (R : Subgroup G) (hXI : X ≤ I) :
    ((M ⊓ X).subgroupOf X).map (toStarImage X R) =
      (starM X R (M ⊓ I)).subgroupOf (starImage X R X) := by
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact ⟨⟨x,mem_sup_left x.property⟩,⟨⟨hx.1,hXI hx.2⟩,hx.2⟩,rfl⟩
  · rintro ⟨x,hx,he⟩
    refine ⟨⟨x,hx.2⟩,⟨hx.1.1,hx.2⟩,?_⟩
    exact Subtype.ext he

/-- The original M ∩ X maps to the marked star parabolic. -/
theorem Branch.coreStarEquiv_map_intersection (b : Branch M I X n F) :
    (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
      b.coreStarEquiv.toMonoidHom =
        (starM X ((M ⊓ I).pCoreIn 2) (M ⊓ I)).subgroupOf
          (starImage X ((M ⊓ I).pCoreIn 2) X) := by
  rw [map_map]
  exact map_intersection_toStar _ b.input.component.1

/-- Transfer the marked parabolic through the canonical core-to-star map. -/
theorem Branch.core_parabolic (b : Branch M I X n F) :
    IsLinearMaximalParabolic
      (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 3 F := by
  obtain ⟨e,W,hn,hp,he⟩ := b.parabolic
  refine ⟨b.coreStarEquiv.trans e,W,hn,hp,?_⟩
  change (((M ⊓ X).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
    (e.toMonoidHom.comp b.coreStarEquiv.toMonoidHom) = _
  rw [← map_map, b.coreStarEquiv_map_intersection, he]

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem residual_intersection_three_dvd
    (hI : PlaneEscapes Mc ZS I) {A : Subgroup G} (hAI : A ≤ I)
    (hKA : (pResidual 2 H).map H.subtype ≤ normalizer (A : Set G))
    (hthree : 3 ∣ Nat.card A) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ A : Subgroup G) := by
  let K := (pResidual 2 H).map H.subtype
  have hKI : K ≤ I :=
    (le_sup_left.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank (G := K) (p := 3)
  let := hE
  let EI := E.map (inclusion hKI)
  let e : E ≃* EI := E.equivMapOfInjective (inclusion hKI) (inclusion_injective hKI)
  let : IsElementaryAbelian 3 EI := IsElementaryAbelian.of_injective e.symm.toMonoidHom e.symm.injective
  have hEI : Nat.card EI = 3 ^ 2 := by
    rw [← Nat.card_congr e.toEquiv, hcard, residual_rank_two d]
  have hnorm : EI ≤ normalizer (A.subgroupOf I : Set I) := by
    rw [← subgroupOf_normalizer_eq hAI]
    rintro _ ⟨x,hx,rfl⟩
    exact hKA x.property
  have hAIcard : 3 ∣ Nat.card (A.subgroupOf I) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAI).toEquiv]
    exact hthree
  have hr : primeRank 3 I ≤ 2 :=
    (Chapter1.RadicalExclusions.sqtk_of_mem_H hsource.ambient hI.1).stronglyQuasithin
      3 Nat.prime_three (by decide)
  have hne := Subgroup.inf_ne_bot_of_elementary_plane EI (A.subgroupOf I)
    hnorm hAIcard hEI hr
  have hp : IsPGroup 3 (EI ⊓ A.subgroupOf I : Subgroup I) :=
    (IsElementaryAbelian.isPGroup 3 EI).to_le inf_le_left
  have hd : 3 ∣ Nat.card (EI ⊓ A.subgroupOf I : Subgroup I) := by
    rcases hp.card_eq_or_dvd with h | h
    · exact (hne (card_eq_one.mp h)).elim
    · exact h
  let j : (EI ⊓ A.subgroupOf I : Subgroup I) →* (K ⊓ A : Subgroup G) := {
    toFun := fun x => ⟨x.val.val, by
      obtain ⟨k,hk,he⟩ := x.property.1
      exact ⟨(congrArg Subtype.val he) ▸ k.property,x.property.2⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (K ⊓ A : Subgroup G) => (z : G)) h
  exact hd.trans (card_dvd_of_injective j hj)

include d in
/-- The original rank-two residual meets X in a subgroup of order divisible by three. -/
theorem Branch.residual_component_intersection_three_dvd
    {X : Subgroup G} {n : ℕ} {F : Type} [Field F] [Finite F]
    (b : Branch M I X n F) (hI : PlaneEscapes Mc ZS I) :
    3 ∣ Nat.card ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) := by
  have hKX : (pResidual 2 H).map H.subtype ≤ normalizer (X : Set G) := by
    have hh := d.residual_normalizes_component hI b.input.component.2
    rwa [map_subgroupOf_eq_of_le b.input.component.1] at hh
  apply residual_intersection_three_dvd d hI b.input.component.1 hKX
  obtain ⟨e⟩ := b.model
  have hd : 3 ∣ Nat.card (X ⧸ pCore 2 X) := by
    rw [Nat.card_congr e.toEquiv]
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using b.field_card)
    exact Theory.SpecificGroups.three_dvd_card_sl_three F
  exact hd.trans (by simpa only [index_eq_card] using (pCore 2 X).index_dvd_card)


end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

private theorem binary_component_rank_le_one
    {F : Type} [Field F] [Finite F] (b : Branch M I X 1 F) : primeRank 3 X ≤ 1 := by
  obtain ⟨e⟩ := b.model
  let := Fintype.ofFinite F
  have hc : Nat.card F = 2 := by simpa using b.field_card
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 X) pCore_isPGroup,
    primeRank_congr 3 (e.trans (Atlas.fieldEquivSL 3 ef))]
  apply primeRank_le_one_of_square_not_dvd
  rw [Matrix.PSL3Two.card_SL]
  decide

include d in
/-- The original K ∩ X has 3-rank exactly one in the binary branch. -/
theorem Branch.binary_intersection_rank_one
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    primeRank 3 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) = 1 := by
  have hu := (primeRank_mono 3 (show (pResidual 2 H).map H.subtype ⊓ X ≤ X from inf_le_right)).trans
    (binary_component_rank_le_one b)
  have hd := b.residual_component_intersection_three_dvd d hI
  have hz : primeRank 3 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G) ≠ 0 :=
    fun hz => PrimeRank.eq_zero_iff_not_dvd_card.mp hz hd
  omega

include d in
/-- An S-invariant binary component gives a proper invariant subgroup of K/O₂(K). -/
theorem Branch.binary_reducible_of_normalized
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I)
    (hSX : planeSylow T ZS ≤ normalizer (X : Set G)) :
    ¬ IsSmallActionIrreducible (planeSylow T ZS) ((pResidual 2 H).map H.subtype) := by
  intro hirr
  let K := (pResidual 2 H).map H.subtype
  let A := K ⊓ X
  let L := K.pCoreIn 2 ⊔ A
  have hSK : planeSylow T ZS ≤ normalizer (K : Set G) := hirr.1
  have hSA : planeSylow T ZS ≤ normalizer (A : Set G) :=
    (le_inf hSK hSX).trans inf_normalizer_le_normalizer_inf
  have hSQ : planeSylow T ZS ≤ normalizer (K.pCoreIn 2 : Set G) := hSK.trans
    (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  have hSL : planeSylow T ZS ≤ normalizer (L : Set G) :=
    (le_inf hSQ hSA).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rcases hirr.2 L le_sup_left (sup_le (pCoreIn_le 2 K) inf_le_left) hSL with he | he
  · have hp : IsPGroup 2 A := (isPGroup_pCoreIn 2 K).to_le (le_sup_right.trans he.le)
    obtain ⟨r,hr⟩ := hp.exists_card_eq
    have hd := b.residual_component_intersection_three_dvd d hI
    change 3 ∣ Nat.card A at hd
    rw [hr] at hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  · let B := A.subgroupOf K
    let q := QuotientGroup.mk' (pCore 2 K)
    have hgen : pCore 2 K ⊔ B = ⊤ := by
      apply map_injective K.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show A ≤ K from inf_le_left),
        ← MonoidHom.range_eq_map,range_subtype]
      exact he
    have hm : B.map q = ⊤ := by
      have hh := congrArg (map q) hgen
      have hq : (pCore 2 K).map q = ⊥ :=
        (Subgroup.map_eq_bot_iff (pCore 2 K)).mpr (by rw [QuotientGroup.ker_mk'])
      have hsur : q.range = ⊤ :=
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective (pCore 2 K))
      simpa only [Subgroup.map_sup,hq,bot_sup_eq,← MonoidHom.range_eq_map,hsur] using hh
    have hr := ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) B
    rw [hm,primeRank_congr 3 topEquiv,
      primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 K) pCore_isPGroup,
      primeRank_congr 3 (subgroupOfEquivOfLe (show A ≤ K from inf_le_left))] at hr
    have hrK : primeRank 3 K = 2 := residual_rank_two d
    have hrA : primeRank 3 A = 1 := b.binary_intersection_rank_one d hI
    omega

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V H ZS I X : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)

include d in
private theorem component_sylow_intersection (hI : PlaneEscapes Mc ZS I)
    (hX : X ∈ Chapter1.cComponentsIn I) :
    ∃ P : Sylow 2 X, (P : Subgroup X) = (planeSylow T ZS).subgroupOf X := by
  obtain ⟨R,hR⟩ := d.sylow_in_escape hI
  obtain ⟨Q,hQ⟩ := R.exists_subgroupOf_eq_of_subnormal (X.subgroupOf I) hX.2.subnormal
  let e := subgroupOfEquivOfLe hX.1
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective,?_⟩
  change (Q : Subgroup (X.subgroupOf I)).map e.toMonoidHom = _
  rw [hQ]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact hR ▸ mem_map_of_mem I.subtype hy
  · intro hx
    have hr : (⟨x,hX.1 x.property⟩ : I) ∈ R := by
      apply (mem_map_iff_mem I.subtype_injective).mp
      rwa [hR]
    exact ⟨⟨⟨x,hX.1 x.property⟩,x.property⟩,hr,rfl⟩

include d in
private theorem local_seven_not_dvd : ¬ 7 ∣ Nat.card H := by
  obtain ⟨e⟩ := d.geometry.quotient
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := H)).exists_card_eq
  have hc : Nat.card (H ⧸ pCore 2 H) = 72 := by
    rw [Nat.card_congr e.toEquiv, RegularWreathProduct.card, Nat.card_perm]
    norm_num [Nat.card_eq_fintype_card]
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 H),hc,hn]
  intro hd
  rcases (by decide : Nat.Prime 7).dvd_mul.mp hd with hh | hh
  · norm_num at hh
  · have := (by decide : Nat.Prime 7).dvd_of_dvd_pow hh
    norm_num at this

include d in
/-- One quotient marking sends the actual H ∩ X to a maximal parabolic
and S ∩ X to its Borel in the binary branch. -/
theorem Branch.binary_local_marking
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL := by
  obtain ⟨e₀⟩ := b.model
  let := Fintype.ofFinite F
  have hc : Nat.card F = 2 := by simpa using b.field_card
  let ef : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hc)).symm
  let e₁ := e₀.trans (Atlas.fieldEquivSL 3 ef)
  let q := QuotientGroup.mk' (pCore 2 X)
  let J := H.subgroupOf X
  let A := J.map q
  let j : J →* H := {
    toFun := fun x => ⟨x.val.val,x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) he
  have hne : A ≠ ⊤ := by
    intro he
    have hd := (J.card_map_dvd q).trans (card_dvd_of_injective j hj)
    change Nat.card A ∣ Nat.card H at hd
    rw [he,Nat.card_congr topEquiv.toEquiv,Nat.card_congr e₁.toEquiv,
      Matrix.PSL3Two.card_SL] at hd
    exact local_seven_not_dvd d ((by decide : 7 ∣ 168).trans hd)
  have hd : 3 ∣ Nat.card J := by
    have hle : (pResidual 2 H).map H.subtype ⊓ X ≤ H ⊓ X :=
      inf_le_inf_right X (map_subtype_le _)
    have hh := (b.residual_component_intersection_three_dvd d hI).trans (card_dvd_of_le hle)
    rw [← card_map_of_injective (K := J) X.subtype_injective,subgroupOf_map_subtype]
    exact hh
  have htwo : ¬ IsPGroup 2 A := by
    intro hp
    have hzero : primeRank 3 A = 0 := PrimeRank.eq_zero_iff_not_dvd_card.mpr (by
      intro hd
      obtain ⟨r,hr⟩ := hp.exists_card_eq
      rw [hr] at hd
      exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd))
    rw [ResidualCentralizerRank.primeRank_map_of_twoGroup_kernel (by decide : Odd 3)
      q (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)] at hzero
    exact (PrimeRank.eq_zero_iff_not_dvd_card.mp hzero) hd
  obtain ⟨P,hP⟩ := component_sylow_intersection d hI b.input.component
  have hPJ : (P : Subgroup X) ≤ J := by
    rw [hP]
    exact comap_mono (inf_le_left.trans d.geometry.outside.1.1.2)
  obtain ⟨e,hs,ha⟩ := Matrix.PSL3Two.exists_sylow_line_marking
    (e₁.trans Matrix.PSL3Two.equiv) (P.mapSurjective (QuotientGroup.mk'_surjective _)) A
    (map_mono hPJ) hne htwo
  exact ⟨e,ha,by simpa only [Sylow.coe_mapSurjective,hP] using hs⟩


/-- Taking O² of K ∩ X or of H ∩ X gives the same actual subgroup. -/
private theorem binary_intersection_residual_eq_local :
    (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype =
    (pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype := by
  let A := (pResidual 2 H).map H.subtype ⊓ X
  let B := (pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype
  have hBA : B ≤ A := le_inf (embedded_pResidual_mono 2 inf_le_left)
    ((map_subtype_le _).trans inf_le_right)
  have hp : IsPPerfect 2 (B.subgroupOf A) :=
    (isPPerfect_embedded_pResidual 2 (H ⊓ X)).of_surjective
      (subgroupOfEquivOfLe hBA).symm.toMonoidHom (subgroupOfEquivOfLe hBA).symm.surjective
  apply le_antisymm (embedded_pResidual_mono 2 (inf_le_inf_right X (map_subtype_le _)))
  have hh := map_mono (f := A.subtype) (le_pResidual_of_isPPerfect (B.subgroupOf A) hp)
  rwa [map_subgroupOf_eq_of_le hBA] at hh

include d in
/-- The same marking identifies the literal candidate K₁ = O²(K ∩ X)
with the line-parabolic residual in the component quotient. -/
theorem Branch.binary_factor_marking
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    ∃ e : (X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.SL,
      ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.lineParabolicSL ∧
      (((planeSylow T ZS).subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map
        e.toMonoidHom = Matrix.PSL3Two.borelSL ∧
      ((L.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom =
        Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
  dsimp only
  rw [binary_intersection_residual_eq_local]
  obtain ⟨e,hJ,hS⟩ := b.binary_local_marking d hI
  refine ⟨e,hJ,hS,?_⟩
  let J := H.subgroupOf X
  have hh : ((pResidual 2 (H ⊓ X : Subgroup G)).map (H ⊓ X).subtype).subgroupOf X =
      (pResidual 2 J).map J.subtype := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le ((map_subtype_le _).trans inf_le_right),
      map_embedded_pResidual,subgroupOf_map_subtype]
  rw [hh,map_embedded_pResidual,map_embedded_pResidual,hJ]
  exact Matrix.PSL3Two.MarkedAutomorphisms.line_residual

include d in
/-- The actual candidate O²(K ∩ X) has quotient of order three by its
own two-core. The core is not confused with the two-residual. -/
theorem Branch.binary_factor_core_quotient_card
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype
    Nat.card (L ⧸ pCore 2 L) = 3 := by
  let L := (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
    ((pResidual 2 H).map H.subtype ⊓ X).subtype
  have hLX : L ≤ X := (map_subtype_le _).trans inf_le_right
  obtain ⟨e,_,_,hL⟩ := b.binary_factor_marking d hI
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 X))
  let A := L.subgroupOf X
  have hf : A.map f = Matrix.PSL3Two.MarkedAutomorphisms.lineA := by
    rw [← map_map]
    exact hL
  have hk : IsPGroup 2 f.ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hkA : IsPGroup 2 (f.subgroupMap A).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eA := f.subgroupMap A |>.pCoreQuotientEquiv (f.subgroupMap_surjective A) hkA
  let eL := subgroupOfEquivOfLe hLX
  have hc : Nat.card (A ⧸ pCore 2 A) = 3 := by
    rw [Nat.card_congr eA.toEquiv,hf]
    exact Matrix.PSL3Two.MarkedAutomorphisms.card_line_core_quotient
  rw [Nat.card_congr (QuotientGroup.congr (pCore 2 A) (pCore 2 L) eL
    (pCore_map_iso 2 eL)).toEquiv] at hc
  exact hc


include d in
/-- The original H ∩ X is a maximal subgroup of X, lifting the binary
parabolic through O₂(X). -/
theorem Branch.binary_local_isCoatom
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) :
    IsCoatom (H.subgroupOf X) := by
  obtain ⟨e,hJ,_⟩ := b.binary_local_marking d hI
  have hm : IsCoatom ((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) :=
    (e.mapSubgroup.isCoatom_iff _).mp (by
      change IsCoatom (((H.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))).map e.toMonoidHom)
      rw [hJ]
      exact Matrix.PSL3Two.isCoatom_lineParabolicSL)
  have hc := isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective (pCore 2 X)) hm
  have hcore : X.pCoreIn 2 ≤ H :=
    (pCoreAmbient_mono_of_isSubnormalIn X I 2 b.input.component.1
      b.input.component.2.subnormal).trans
      ((d.core_le_plane hI).trans (inf_le_left.trans d.geometry.outside.1.1.2))
  have hk : (QuotientGroup.mk' (pCore 2 X)).ker ≤ H.subgroupOf X := by
    rw [QuotientGroup.ker_mk']
    exact fun x hx => hcore (mem_map_of_mem X.subtype hx)
  rwa [comap_map_eq_self hk] at hc

include d in
/-- Once the preliminary block reduction puts X outside Mc, its actual
centralizer of ZS and its Mc-intersection are both H ∩ X. -/
theorem Branch.binary_centralizer_eq_local
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc) :
    Mc ⊓ X = H ⊓ X ∧ X ⊓ centralizer (ZS : Set G) = H ⊓ X := by
  have hne : Mc.subgroupOf X ≠ ⊤ := by
    intro he
    apply hout
    intro x hx
    exact (show (⟨x,hx⟩ : X) ∈ Mc.subgroupOf X from he ▸ mem_top _)
  have he := ((b.binary_local_isCoatom d hI).le_iff_eq hne).mp
    (comap_mono d.geometry.in_partner)
  have hMX : Mc ⊓ X = H ⊓ X := by
    have hh := congrArg (map X.subtype) he
    simpa only [subgroupOf_map_subtype] using hh
  refine ⟨hMX,le_antisymm ?_ ?_⟩
  · rw [← hMX]
    exact le_inf (inf_le_right.trans ((d.centralizer_le_intersection hI).trans inf_le_left))
      inf_le_left
  · apply le_inf inf_le_right
    have hh : H ⊓ X ≤ H ⊓ I := inf_le_inf_left H b.input.component.1
    rw [local_escape_intersection d hI] at hh
    exact hh.trans (sup_le d.residual_centralizes inf_le_right)

include d in
/-- The candidate cubic factor is exactly O²(M₀), where M₀ = Mc ∩ X is
the printed opposite parabolic. -/
theorem Branch.binary_factor_eq_opposite_residual
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc) :
    (pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
      ((pResidual 2 H).map H.subtype ⊓ X).subtype =
    (pResidual 2 (Mc ⊓ X : Subgroup G)).map (Mc ⊓ X).subtype := by
  rw [binary_intersection_residual_eq_local,(b.binary_centralizer_eq_local d hI hout).1]

include d in
/-- When X is normal in I, the original candidate K₁ is normal in Mᵢ.
This discharges the normality step immediately after (*) on printed p.1116. -/
theorem Branch.binary_factor_normalized
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    Mc ⊓ I ≤ normalizer
      (((pResidual 2 ((pResidual 2 H).map H.subtype ⊓ X : Subgroup G)).map
        ((pResidual 2 H).map H.subtype ⊓ X).subtype) : Set G) := by
  rw [b.binary_factor_eq_opposite_residual d hI hout]
  exact ((le_inf (inf_le_left.trans Mc.le_normalizer) (inf_le_right.trans hn)).trans
    inf_normalizer_le_normalizer_inf).trans
      (normalizer_le_normalizer_characteristic_image (Mc ⊓ X) (pResidual 2 (Mc ⊓ X : Subgroup G)))


include d in
/-- The original cubic factor candidate meets the literal 15.2.21 factor
criteria once the component-orbit step has supplied relative normality.
Its normality in Mᵢ and the required reducibility are derived here. -/
theorem Branch.binary_factor_source_data
    {F : Type} [Field F] [Finite F]
    (b : Branch M I X 1 F) (hI : PlaneEscapes Mc ZS I) (hout : ¬ X ≤ Mc)
    (hn : I ≤ normalizer (X : Set G)) :
    let K := (pResidual 2 H).map H.subtype
    let L := (pResidual 2 (K ⊓ X : Subgroup G)).map (K ⊓ X).subtype
    L ≤ K ∧ IsPPerfect 2 L ∧ Nat.card (L ⧸ pCore 2 L) = 3 ∧
      planeSylow T ZS ≤ normalizer (L : Set G) ∧
      Mc ⊓ I ≤ normalizer (L : Set G) ∧
      ¬ IsSmallActionIrreducible (planeSylow T ZS) K := by
  have hnorm := b.binary_factor_normalized d hI hout hn
  exact ⟨(map_subtype_le _).trans inf_le_left,isPPerfect_embedded_pResidual 2 _,
    b.binary_factor_core_quotient_card d hI,
    (le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans hnorm,hnorm,
    b.binary_reducible_of_normalized d hI
      (((le_sup_right.trans (d.residual_sup_planeSylow_le hI)).trans inf_le_right).trans hn)⟩

end CFSG.Quasithin.Chapter15.Section02.PlaneUniquenessPreceding.LinearThree.ModelOnly
