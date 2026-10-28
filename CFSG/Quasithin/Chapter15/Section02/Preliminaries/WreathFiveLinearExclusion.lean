module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearThree
public import Theory.SpecificGroups.SL2.ResidualSylowGeneration
public import Theory.SpecificGroups.SL2.EvenBorelResidual
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.SolvableOvergroups
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.GroupTheory.SolvableNormalSup

/-!
# Complete linear exclusions in the original marked-five wreath argument

The local A₅ component already bounds the field degree of either binary
linear quotient by two. The original residual Y is solvable and has
|Y/O₂(Y)| = 5. Its image in the actual containing-component quotient still
has order divisible by five, because the quotient kernel is a two-group.
The full Sylow normalizes this image, so together they generate a solvable
Sylow overgroup. The rank-one and linear-three Borel theorems place that
overgroup in a Borel. At degrees one and two, its order is prime to five.

Thus both linear quotient families are impossible at every field size.
The H-star application retains the original K,Y,S,W,R,L₁ and derives all
normalization and quotient-order premises from the marked-five source.
The earlier C.2.7/A.3.15 model comparison and mixed-amalgam branches remain
separate; no classification conclusion is assumed here.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.Converse
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource

private theorem rankOne_normalizer_card (F : BinaryField) (P : Sylow 2 SL(2,F.Carrier)) :
    Nat.card (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier))) =
      2 ^ F.degree * (2 ^ F.degree - 1) := by
  let Q := P.mapSurjective (f := pi F.Carrier)
    (pi_surjective (F := F.Carrier))
  rw [Nat.card_congr (equivMapOfInjective
    (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier)))
    (pi F.Carrier)
    (pi_injective (F := F.Carrier))).toEquiv]
  rw [map_normalizer_eq_of_bijective (P : Subgroup SL(2,F.Carrier))
    ⟨pi_injective (F := F.Carrier),
      pi_surjective (F := F.Carrier)⟩]
  change Nat.card (normalizer ((Q : Subgroup PSL(2,F.Carrier)) : Set PSL(2,F.Carrier))) = _
  simpa only [Sylow.coe_coe,F.card_eq] using
    (Nat.card_congr (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F.Carrier Q).toEquiv).trans
      (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.card_borel F.Carrier)

private theorem rankOne_small_solvable_overgroup_five_free
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(2,F.Carrier))
    (D : Subgroup SL(2,F.Carrier)) [Group.IsSolvable D]
    (hPD : (P : Subgroup SL(2,F.Carrier)) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro hd
  by_cases h1 : F.degree = 1
  · have hh := hd.trans D.card_subgroup_dvd_card
    rw [GorensteinWalter.sl2_card_formula,F.card_eq,h1] at hh
    norm_num at hh
  have h2 : F.degree = 2 := by have := F.degree_pos; omega
  have hl : 3 < Nat.card F.Carrier := by rw [F.card_eq,h2]; decide
  let : IsQuasisimple SL(2,F.Carrier) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hl (.refl _)
  let : IsSimpleGroup (SL(2,F.Carrier) ⧸ center SL(2,F.Carrier)) := IsQuasisimple.simple
  let : Nontrivial SL(2,F.Carrier) := (QuotientGroup.mk'_surjective (center SL(2,F.Carrier))).nontrivial
  have hn : D ≠ ⊤ := by
    intro ht
    let : Group.IsSolvable (⊤ : Subgroup SL(2,F.Carrier)) := ht ▸ inferInstance
    exact Group.IsPerfect.not_isSolvable SL(2,F.Carrier)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := SL(2,F.Carrier))).toMonoidHom)
        (topEquiv (G := SL(2,F.Carrier))).surjective)
  have hle := Matrix.SpecialLinearGroup.overgroup_le_sylowNormalizer P hPD hn
  have hh := hd.trans (card_dvd_of_le hle)
  change 5 ∣ Nat.card (normalizer ((P : Subgroup SL(2,F.Carrier)) : Set SL(2,F.Carrier))) at hh
  rw [rankOne_normalizer_card,h2] at hh
  norm_num at hh


private theorem solvable_five_section {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 5) : Group.IsSolvable A := by
  let : Group.IsNilpotent (pCore 2 A) := (pCore_isPGroup (p := 2) (G := A)).isNilpotent
  have hp : IsPGroup 5 (A ⧸ pCore 2 A) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr ⟨inferInstance,inferInstance⟩

private theorem five_dvd_image {A D : Type*} [Group A] [Finite A] [Group D]
    (f : A →* D) (hk : IsPGroup 2 f.ker)
    (hc : Nat.card (A ⧸ pCore 2 A) = 5) : 5 ∣ Nat.card f.range := by
  have hd : 5 ∣ Nat.card A := by
    have hh := (pCore 2 A).index_dvd_card
    rwa [Subgroup.index_eq_card,hc] at hh
  have hn : ¬ 5 ∣ Nat.card f.ker := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    intro hh
    have h := (by decide : Nat.Prime 5).dvd_of_dvd_pow hh
    norm_num at h
  have hcount := f.ker.index_mul_card
  rw [index_ker] at hcount
  rw [←hcount] at hd
  exact ((by decide : Nat.Prime 5).dvd_mul.mp hd).resolve_right hn

private theorem solvable_normalized_sup {A : Type*} [Group A]
    (B S : Subgroup A) [Group.IsSolvable B] [Group.IsSolvable S]
    (hn : S ≤ normalizer (B : Set A)) : Group.IsSolvable (B ⊔ S : Subgroup A) := by
  let D := B ⊔ S
  let : (B.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer
    (sup_le B.le_normalizer hn)
  let : Group.IsSolvable (B.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe (show B ≤ D from le_sup_left)).injective
  let : Group.IsSolvable (S.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).toMonoidHom)
      (subgroupOfEquivOfLe (show S ≤ D from le_sup_right)).injective
  exact Group.isSolvable_of_normal_sup_eq_top (B.subgroupOf D) (S.subgroupOf D)
    (by rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])

private theorem no_small_rankOne_normalized_five
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(2,F.Carrier))
    (B : Subgroup SL(2,F.Carrier)) [Group.IsSolvable B]
    (hPB : (P : Subgroup SL(2,F.Carrier)) ≤ normalizer (B : Set SL(2,F.Carrier)))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup SL(2,F.Carrier)) : Subgroup SL(2,F.Carrier)) :=
    solvable_normalized_sup B P hPB
  exact rankOne_small_solvable_overgroup_five_free F hF P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup SL(2,F.Carrier)) from le_sup_left)))


variable {G : Type*} [Group G] [Finite G]

private theorem no_model_normalized_five_section
    {W L Y S : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    {D : Type*} [Group D] [Finite D] (e : (L ⧸ pCore 2 L) ≃* D)
    (hmodel : ∀ (P : Sylow 2 D) (B : Subgroup D), Group.IsSolvable B →
      (P : Subgroup D) ≤ normalizer (B : Set D) → 5 ∣ Nat.card B → False) : False := by
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hL.1 hL.2.subnormal
  have hP' : (P : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  let Y₀ := Y.subgroupOf L
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 L := by ext x; simp [q]
  let P' := P.mapSurjective (f := q) hq
  let f := q.comp Y₀.subtype
  have hf : f.range = Y₀.map q := by rw [MonoidHom.range_comp,range_subtype]
  have hker : IsPGroup 2 f.ker := by
    change IsPGroup 2 (q.comp Y₀.subtype).ker
    rw [←MonoidHom.comap_ker,hqker]
    exact pCore_isPGroup.comap_of_injective Y₀.subtype Y₀.subtype_injective
  have hc₀ : Nat.card (Y₀ ⧸ pCore 2 Y₀) = 5 := by
    let a := subgroupOfEquivOfLe hYL
    rw [Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv,hc]
  let : Group.IsSolvable Y₀ := solvable_five_section hc₀
  let : Group.IsSolvable f.range := Group.isSolvable_of_surjective f.rangeRestrict_surjective
  have hn : (P' : Subgroup D) ≤ normalizer (f.range : Set D) := by
    have hPN : (P : Subgroup L) ≤ normalizer (Y₀ : Set L) := by
      rw [hP',←subgroupOf_normalizer_eq hYL]
      exact comap_mono hSN
    rw [hf]
    exact (map_mono hPN).trans (Y₀.le_normalizer_map q)
  exact hmodel P' f.range inferInstance hn (five_dvd_image f hker hc₀)

/-- The actual local A₅ and the normalized five-residual together exclude every
binary rank-one quotient, without a field-divisibility premise. -/
theorem source_local_component_rankOne_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hKW : K ≤ W) (hSyl : Chapter1.IsSylowIn 2 S W)
    (hcore : pCore 2 W ≠ ⊥)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hq : IsQuasisimple (L ⧸ pCore 2 L))
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(2,F.Carrier)) := by
  rintro ⟨e⟩
  have hF := source_local_component_rankOne_degree_le_two hK hSH heK hKW hSyl hcore hL hKL hq F e
  apply no_model_normalized_five_section hSyl hL hYL hSN hc e
  intro P B hsol hn hfive
  let := hsol
  exact no_small_rankOne_normalized_five F hF P B hn hfive

private theorem linearThree_small_solvable_overgroup_five_free
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(3,F.Carrier))
    (D : Subgroup SL(3,F.Carrier)) [Group.IsSolvable D]
    (hPD : (P : Subgroup SL(3,F.Carrier)) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro hd
  by_cases h1 : F.degree = 1
  · have hh := hd.trans D.card_subgroup_dvd_card
    rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear,F.card_eq,h1] at hh
    norm_num at hh
  have h2 : F.degree = 2 := by have := F.degree_pos; omega
  have hl : 4 ≤ Nat.card F.Carrier := by rw [F.card_eq,h2]; decide
  let U := Matrix.PSL3.CartanActions.BorelQuotient.unipotentSLSylow
    F.Carrier F.degree_pos F.card_eq
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq SL(3,F.Carrier) P U
  let a := MulAut.conj g
  have hP : (P : Subgroup SL(3,F.Carrier)).map a.toMonoidHom =
      Matrix.PSL3.LinearThree.unipotentSL F.Carrier := congrArg Sylow.toSubgroup hg
  let D' := D.map a.toMonoidHom
  let : Group.IsSolvable D' :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective D)
  have hle := Matrix.PSL3.LinearThree.SolvableOvergroups.solvable_le_borelSL
    F.Carrier hl D' (hP ▸ map_mono hPD)
  have hc : Nat.card D = Nat.card D' :=
    Nat.card_congr (equivMapOfInjective D a.toMonoidHom a.injective).toEquiv
  have hd' : 5 ∣ Nat.card D' := hc ▸ hd
  have hh := hd'.trans (card_dvd_of_le hle)
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_borelSL,F.card_eq,h2] at hh
  norm_num at hh

private theorem no_small_linearThree_normalized_five
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 SL(3,F.Carrier))
    (B : Subgroup SL(3,F.Carrier)) [Group.IsSolvable B]
    (hPB : (P : Subgroup SL(3,F.Carrier)) ≤ normalizer (B : Set SL(3,F.Carrier)))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup SL(3,F.Carrier)) : Subgroup SL(3,F.Carrier)) :=
    solvable_normalized_sup B P hPB
  exact linearThree_small_solvable_overgroup_five_free F hF P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup SL(3,F.Carrier)) from le_sup_left)))

/-- The local A₅ and the original normalized five-residual exclude every
binary linear-three two-core quotient. -/
theorem source_local_component_linearThree_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,F.Carrier)) := by
  rintro ⟨e⟩
  have hF := source_local_component_linearThree_degree_le_two hK hSH heK hSyl hL hKL F e
  apply no_model_normalized_five_section hSyl hL hYL hSN hc e
  intro P B hsol hn hfive
  let := hsol
  exact no_small_linearThree_normalized_five F hF P B hn hfive

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic wreath-five configuration has neither binary
linear-two nor linear-three two-core quotient, at any field size. -/
theorem source_HStar_wreath_five_failed_quotient_no_linearModels
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V H : Subgroup G} [IsElementaryAbelian 2 V]
    (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : PreparedChosenModule T M V)
    (hcases : SourceCases.Dihedral (imageRepresentation M V hV.normalized) ∨
      SourceCases.Omega (imageRepresentation M V hV.normalized))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃*
      RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2)))) :
    let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
    ∃ K : Subgroup G, K ∈ Chapter1.cComponentsIn H ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∧ ¬ K ≤ M ∧
      let L := ![Y ⊔ (M ⊓ Mc).pCoreIn 2,K]
      let S := (T : Subgroup G) ⊓ normalizer (K : Set G)
      let W := ChapterF.Source.generated L S
      let q := QuotientGroup.mk' (pCore 2 W)
      let R := (Y ⊔ S).pCoreIn 2
      S.relIndex (T : Subgroup G) = 2 ∧
      elementaryAbelianMaxJ (T : Subgroup G) ≤ S ∧
      (pCore 2 W ≠ ⊥ →
        (¬ ∀ i, generalizedFitting (((ChapterF.Source.parabolic L S i).subgroupOf W).map q) =
          pCore 2 (((ChapterF.Source.parabolic L S i).subgroupOf W).map q)) →
        Chapter1.IsSylowIn 2 S W ∧ V ≤ W.pCoreIn 2 ∧
        generalizedFitting W = pCore 2 W ∧
        Chapter1.RadicalExclusions.PushingUpSetup KnownSimple.IsKnownSimple W R (W ⊓ M) ∧
        ∃ L₁ : Subgroup G, L₁ ∈ Chapter1.cComponentsIn W ∧ K ≤ L₁ ∧ ¬ L₁ ≤ M ∧
          W ≤ normalizer (L₁ : Set G) ∧ W = L₁ ⊔ (W ⊓ M) ∧
          generalizedFitting L₁ = pCore 2 L₁ ∧
          ¬ Chapter1.IsSylowIn 2 R (L₁ ⊔ R) ∧ Y ≤ L₁ ∧
          IsQuasisimple (L₁ ⧸ pCore 2 L₁) ∧
          ∀ F : ChapterB.QuasisimpleSource.BinaryField,
            (¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* SL(2,F.Carrier))) ∧
            (¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* SL(3,F.Carrier)))) := by
  obtain ⟨l,hd,_⟩ := source_HStar_wreath_five_reduction
    hG T hempty hM hJ hu hmany hV hcases hH he
  obtain ⟨K,hK,heK,hout,hi,hJS,hconf⟩ :=
    source_HStar_wreath_five_failed_quotient_quasisimple_component
      hG T hempty hM hJ hu hmany hV hcases hH he
  refine ⟨K,hK,heK,hout,hi,hJS,?_⟩
  intro hcore hfailed
  obtain ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq⟩ :=
    hconf hcore hfailed
  refine ⟨hSyl,hVcore,hWfit,hsetup,L₁,hL₁,hKL,houtL,hNL,hgen,hLfit,hnot,hYL,hq,?_⟩
  intro F
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hMN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).1
  refine ⟨?_,?_⟩
  · exact source_local_component_rankOne_exclusion hK
      (inf_le_left.trans hH.1.1.2) heK (le_sup_right.trans le_sup_left)
      hSyl hcore hL₁ hKL hq hYL (inf_le_left.trans (hM.1.2.trans hMN)) hc F
  · exact source_local_component_linearThree_exclusion hK
      (inf_le_left.trans hH.1.1.2) heK hSyl hL₁ hKL hYL
      (inf_le_left.trans (hM.1.2.trans hMN)) hc F

end CFSG.Quasithin.Chapter15.Section02
