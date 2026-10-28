module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveModelTransport
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.Binary.FieldTransport
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# Symplectic exclusion in the original marked-five wreath argument

The original local A₅ maps to a proper full-Sylow local component in the
symplectic quotient. Parabolic placement and either literal SL₂ Levi
projection bound the field degree by two. The normalized residual of
two-core index five generates a solvable overgroup with the Sylow, so it
lies in a Borel. At F₄ its Borel has no factor five; at F₂, the full symplectic group
is S₆ and is not perfect, contradicting source quasisimplicity.
Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
open Theory.SpecificGroups.SymplecticFour

private theorem two_subgroup_le_determinantKernel
    (F : BinaryField) (W : Submodule F.Carrier (Vector F.Carrier))
    (T : Sylow 2 (Sp F.Carrier))
    (hT : (T : Subgroup (Sp F.Carrier)) ≤ stabilizer W) :
    (T : Subgroup (Sp F.Carrier)) ≤ determinantKernel W := by
  intro t ht
  let x : stabilizer W := ⟨t, hT ht⟩
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_pow_pow_eq_one ⟨t, ht⟩
  have hx : x ^ (2 ^ n) = 1 := Subtype.ext (congrArg (fun y : T => (y : Sp F.Carrier)) hn)
  have hp : ((determinantCharacter W x : F.Carrierˣ) : F.Carrier) ^ (2 ^ n) = 1 := by
    have he := congrArg (fun u : F.Carrierˣ => (u : F.Carrier)) (congrArg (determinantCharacter W) hx)
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using he
  have hchar : determinantCharacter W x = 1 := by
    apply Units.ext
    simpa only [pow_one, Units.val_one] using
      (ExpChar.pow_prime_pow_mul_eq_one_iff 2 n 1
      ((determinantCharacter W x : F.Carrierˣ) : F.Carrier)).mp (by simpa using hp)
  exact ⟨x, hchar, rfl⟩

private theorem degree_of_proper_symplectic_join
    {X : Type*} [Group X] [Group.IsPerfect X]
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 (Sp F.Carrier)) (f : X →* Sp F.Carrier)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (hproper : f.range ⊔ (P : Subgroup (Sp F.Carrier)) ≠ ⊤) : F.degree ≤ 2 := by
  by_contra hn
  have hd : 1 < F.degree := by omega
  have hcard : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    exact (show (2 : ℕ) ^ 1 < 2 ^ F.degree from Nat.pow_lt_pow_right (by decide) hd)
  obtain ⟨g,hg⟩ := ThreeResidualPlacement.proper_sylow_overgroup_parabolic_cover
    hcard P (f.range ⊔ (P : Subgroup (Sp F.Carrier))) le_sup_right hproper
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP' : (P' : Subgroup (Sp F.Carrier)) = (P : Subgroup (Sp F.Carrier)).map a.toMonoidHom := rfl
  let : Group.IsSolvable a.toMonoidHom.ker := by
    have he : a.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective
    rw [he]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hl' : f'.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hP']
    simpa only [f',MonoidHom.range_comp] using hl
  have hp : f'.range ⊔ (P' : Subgroup (Sp F.Carrier)) ≤ pointParabolic ∨
      f'.range ⊔ (P' : Subgroup (Sp F.Carrier)) ≤ planeParabolic := by
    rw [hP']
    simpa only [Subgroup.map_sup, f', MonoidHom.range_comp] using hg
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  rcases hp with hp | hp
  · have hb : f'.range ≤ pointLocal := by
      rw [←pointParabolic_solvableResidual_eq F.card_eq hd]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := pointLocal (F := F.Carrier)
    let q := (pointLocalCoreQuotientEquiv F.card_eq hd).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (pointLocalCoreQuotientEquiv F.card_eq hd).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (local_five_degree_of_projection hc F P' f' hl' D hb
      (two_subgroup_le_determinantKernel F (point F.Carrier) P' (le_sup_right.trans hp)) q hq)
  · have hb : f'.range ≤ planeLocal := by
      rw [←planeParabolic_solvableResidual_eq F.card_eq hd]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let D := planeLocal (F := F.Carrier)
    let q := (planeLocalCoreQuotientEquiv F.card_eq hd).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 D))
    have hq : Function.Surjective q :=
      (planeLocalCoreQuotientEquiv F.card_eq hd).surjective.comp
        (QuotientGroup.mk'_surjective _)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 D := by ext x; simp [q]
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := D)
      infer_instance
    exact hn (local_five_degree_of_projection hc F P' f' hl' D hb
      (two_subgroup_le_determinantKernel F (plane F.Carrier) P' (le_sup_right.trans hp)) q hq)

/-- Intrinsic field bound used after the actual central star quotient. -/
theorem local_five_symplectic_degree_of_proper_join
    {X : Type*} [Group X] [Group.IsPerfect X]
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 (Sp F.Carrier)) (f : X →* Sp F.Carrier)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (hproper : f.range ⊔ (P : Subgroup (Sp F.Carrier)) ≠ ⊤) : F.degree ≤ 2 :=
  degree_of_proper_symplectic_join hc F P f hlocal hproper

private theorem symplectic_card_ne_sixty (F : BinaryField) : Nat.card (Sp F.Carrier) ≠ 60 := by
  intro hc
  have hd : 2 ^ (F.degree * 4) ∣ 60 := by
    have hh := (unipotent (F := F.Carrier)).card_subgroup_dvd_card
    rw [card_unipotent,F.card_eq,←pow_mul,hc] at hh
    exact hh
  have h3 : 3 ≤ F.degree * 4 := by have := F.degree_pos; omega
  have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hd
  norm_num at hh

variable {G : Type*} [Group G] [Finite G]

/-- The original local A₅ bounds the symplectic quotient field degree by two. -/
theorem source_local_component_symplectic_degree_le_two
    {H K S W L : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (F : BinaryField) (e : (L ⧸ pCore 2 L) ≃* Sp F.Carrier) : F.degree ≤ 2 := by
  obtain ⟨P,f,hl,hp⟩ := source_local_component_model_data hK hSH heK hSyl hL hKL e
    (symplectic_card_ne_sixty F)
  let : Group.IsPerfect K := source_component_perfect hK
  have hc : Nat.card (K ⧸ pCore 2 K) = 60 := by
    rw [Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
    norm_num
  exact degree_of_proper_symplectic_join hc F P f hl hp

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

private theorem no_small_symplectic_normalized_five
    (F : BinaryField) (hF : F.degree = 2) (P : Sylow 2 (Sp F.Carrier))
    (B : Subgroup (Sp F.Carrier))
    (hn : (P : Subgroup (Sp F.Carrier)) ≤ normalizer (B : Set (Sp F.Carrier)))
    (hc : Nat.card (B ⧸ pCore 2 B) = 5) : False := by
  let : Group.IsNilpotent (pCore 2 B) := (pCore_isPGroup (p := 2) (G := B)).isNilpotent
  have hp : IsPGroup 5 (B ⧸ pCore 2 B) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent (B ⧸ pCore 2 B) := hp.isNilpotent
  let : Group.IsSolvable B :=
    (Group.isSolvable_iff_subgroup_quotient (pCore 2 B)).mpr ⟨inferInstance,inferInstance⟩
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let J := B ⊔ (P : Subgroup (Sp F.Carrier))
  let : Group.IsSolvable J := solvable_normalized_sup B P hn
  have hlarge : 2 < Nat.card F.Carrier := by rw [F.card_eq,hF]; decide
  have hle := solvable_sylow_overgroup_normalizes hlarge P J inferInstance le_sup_right
  have hfive : 5 ∣ Nat.card B := by
    have hh := (pCore 2 B).index_dvd_card
    rwa [Subgroup.index_eq_card,hc] at hh
  have hh := hfive.trans (card_dvd_of_le (le_sup_left.trans hle))
  change 5 ∣ Nat.card (normalizer (P : Set (Sp F.Carrier))) at hh
  rw [Nat.card_congr (EvenBorelTorus.sylowNormalizerEquiv F.card_eq F.degree_pos P).toEquiv,
    card_borel,F.card_eq,hF] at hh
  norm_num at hh

/-- The local A₅ and normalized five-residual exclude every nonbinary
symplectic-four quotient. The binary derived row is the separate A₆ row. -/
theorem source_local_component_nonbinary_symplectic_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) (hF : 1 < F.degree) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Sp F.Carrier) := by
  rintro ⟨e⟩
  have hd := source_local_component_symplectic_degree_le_two hK hSH heK hSyl hL hKL F e
  obtain ⟨P,B,hn,hb⟩ := source_normalized_five_section_image hSyl hL hYL hSN hc e
  exact no_small_symplectic_normalized_five F (by omega) P B hn hb

/-- The actual local A₅ and normalized five-residual exclude every full
binary symplectic-four quotient when the source quotient is quasisimple. -/
theorem source_local_component_symplectic_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hqs : IsQuasisimple (L ⧸ pCore 2 L))
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) := by
  rintro ⟨e⟩
  have hF := source_local_component_symplectic_degree_le_two hK hSH heK hSyl hL hKL F e
  by_cases h1 : F.degree = 1
  · let : IsQuasisimple (L ⧸ pCore 2 L) := hqs
    let a := (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivSp
      (Theory.SpecificGroups.SymplecticFour.Binary.fieldEquivZModTwo F.Carrier
        (by rw [F.card_eq,h1]; norm_num))).trans
      Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
    let : Group.IsPerfect (Equiv.Perm (Fin 6)) := Group.IsPerfect.ofSurjective
      (f := (e.trans a).toMonoidHom) (e.trans a).surjective
    have hh := Group.IsPerfect.mem_commutator (g := Equiv.swap (0 : Fin 6) 1)
    rw [alternatingGroup.commutator_perm_eq (by simp)] at hh
    simp at hh
  exact source_local_component_nonbinary_symplectic_exclusion hK hSH heK hSyl hL hKL
    hYL hSN hc F (by have := F.degree_pos; omega) ⟨e⟩

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic wreath-five configuration excludes the entire
binary symplectic-four two-core quotient family. -/
theorem source_HStar_wreath_five_failed_quotient_no_symplecticModels
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
            ¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Sp F.Carrier)) := by
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
  exact source_local_component_symplectic_exclusion hK
    (inf_le_left.trans hH.1.1.2) heK hSyl hL₁ hKL hq hYL
    (inf_le_left.trans (hM.1.2.trans hMN)) hc F

end CFSG.Quasithin.Chapter15.Section02
