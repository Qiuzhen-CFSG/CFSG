module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveAlternatingExclusion
public import Theory.GroupTheory.CoveringComparisonKernelCard

/-!
# Central-cover preservation of the marked five-section

A quotient whose kernel has order prime to five retains the factor five
in the original solvable residual. Full Sylow normalization also passes
through the literal surjection. Applying this to the two-core quotient
followed by a central quotient of order three excludes the triple-A₆ row,
without replacing the cover by its simple quotient.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107,
and the central-cover row of C.2.7(3), pp.145--147.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section02

private theorem solvable_five_section {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (A ⧸ pCore 2 A) = 5) : Group.IsSolvable A := by
  let : Group.IsNilpotent (pCore 2 A) := (pCore_isPGroup (p := 2) (G := A)).isNilpotent
  have hp : IsPGroup 5 (A ⧸ pCore 2 A) := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent (A ⧸ pCore 2 A) := hp.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 A)).mpr ⟨inferInstance,inferInstance⟩

private theorem five_not_dvd_pCore {A : Type*} [Group A] [Finite A] :
    ¬ 5 ∣ Nat.card (pCore 2 A) := by
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := A)).exists_card_eq
  rw [hn]
  intro hh
  have h := (by decide : Nat.Prime 5).dvd_of_dvd_pow hh
  norm_num at h

variable {G : Type*} [Group G] [Finite G]

/-- Restriction to the original component and any solvable-kernel quotient
preserves both local-component membership and the top C-component. -/
theorem source_local_component_surjective_data
    {H K S W L : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    {D : Type*} [Group D] [Finite D]
    (q : L →* D) (hq : Function.Surjective q) [Group.IsSolvable q.ker] :
    (⊤ : Subgroup D).IsCComponent ∧
      ∃ (P : Sylow 2 D) (f : K →* D),
        f.range ∈ ChapterA.Section03.localCComponents P := by
  have hlocal : K ∈ ChapterA.Section03.localCComponents S :=
    hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hL.1 hL.2.subnormal
  have hP' : (P : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  let B := K.subgroupOf L
  have hlB : B ∈ ChapterA.Section03.localCComponents P := by
    rw [hP']
    exact ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hKL
  have hLC : (⊤ : Subgroup L).IsCComponent := by
    have hh := hL.2.subgroupOf le_rfl
    rw [subgroupOf_self] at hh
    have ht := hh.map_equiv (subgroupOfEquivOfLe hL.1)
    simpa only [map_top_of_surjective (subgroupOfEquivOfLe hL.1).toMonoidHom
      (subgroupOfEquivOfLe hL.1).surjective] using ht
  have hDC : (⊤ : Subgroup D).IsCComponent := by
    have hh := cComponent_map_of_solvable_ker hLC q hq
    simpa only [map_top_of_surjective q hq] using hh
  let P' := P.mapSurjective (f := q) hq
  let f := q.comp (inclusion hKL)
  have hr : f.range = B.map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  refine ⟨hDC,P',f,?_⟩
  rw [hr]
  exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlB q

/-- A local A₅ cannot generate a larger two-core-free model with the full
Sylow if the entire model is a C-component. This works through central covers. -/
theorem local_five_join_proper_of_card
    {X D : Type*} [Group X] [Group D] [Finite D]
    (hc : Nat.card (X ⧸ pCore 2 X) = 60)
    (hD : (⊤ : Subgroup D).IsCComponent) (hcore : pCore 2 D = ⊥)
    (hcard : ¬ Nat.card D ∣ 60)
    (P : Sylow 2 D) (f : X →* D)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P) :
    f.range ⊔ (P : Subgroup D) ≠ ⊤ := by
  intro htop
  have hC : f.range.IsCComponent := by
    change (f.range.subgroupOf (f.range ⊔ (P : Subgroup D))).IsCComponent at hlocal
    rw [htop] at hlocal
    have hh := hlocal.map_subtype (show (⊤ : Subgroup D).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp (hC.eq_of_le hD le_top)
  have hk : pCore 2 X ≤ f.ker := by
    have hn : ((pCore 2 X).map f).Normal := Normal.map inferInstance f hf
    have hp : (pCore 2 X).map f ≤ pCore 2 D := le_sSup ⟨hn,pCore_isPGroup.map f⟩
    apply (Subgroup.map_eq_bot_iff (pCore 2 X)).mp
    exact bot_unique (hcore ▸ hp)
  let r := QuotientGroup.lift (pCore 2 X) f hk
  have hr : Function.Surjective r := QuotientGroup.lift_surjective_of_surjective _ f hf hk
  exact hcard (hc ▸ card_dvd_of_surjective r hr)

/-- A surjective image with five-free kernel retains the actual normalized
solvable five-section. The target need not equal the two-core quotient. -/
theorem source_normalized_five_image_of_surjective
    {W L Y S : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    {D : Type*} [Group D] [Finite D]
    (q : L →* D) (hq : Function.Surjective q) (hk : ¬ 5 ∣ Nat.card q.ker) :
    ∃ (P : Sylow 2 D) (B : Subgroup D), Group.IsSolvable B ∧
      (P : Subgroup D) ≤ normalizer (B : Set D) ∧ 5 ∣ Nat.card B := by
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hL.1 hL.2.subnormal
  have hP' : (P : Subgroup L) = S.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  let Y₀ := Y.subgroupOf L
  let P' := P.mapSurjective (f := q) hq
  let f := q.comp Y₀.subtype
  have hf : f.range = Y₀.map q := by rw [MonoidHom.range_comp,range_subtype]
  have hker : ¬ 5 ∣ Nat.card f.ker := by
    intro hh
    apply hk
    apply hh.trans
    change Nat.card (q.comp Y₀.subtype).ker ∣ _
    rw [←MonoidHom.comap_ker]
    exact card_comap_dvd_of_injective q.ker Y₀.subtype Y₀.subtype_injective
  have hc₀ : Nat.card (Y₀ ⧸ pCore 2 Y₀) = 5 := by
    let a := subgroupOfEquivOfLe hYL
    rw [Nat.card_congr (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).toEquiv,hc]
  let : Group.IsSolvable Y₀ := solvable_five_section hc₀
  refine ⟨P',f.range,Group.isSolvable_of_surjective f.rangeRestrict_surjective,?_,?_⟩
  · have hPN : (P : Subgroup L) ≤ normalizer (Y₀ : Set L) := by
      rw [hP',←subgroupOf_normalizer_eq hYL]
      exact comap_mono hSN
    rw [hf]
    exact (map_mono hPN).trans (Y₀.le_normalizer_map q)
  · have hd : 5 ∣ Nat.card Y₀ := by
      have hh := (pCore 2 Y₀).index_dvd_card
      rwa [Subgroup.index_eq_card,hc₀] at hh
    have hcount := f.ker.index_mul_card
    rw [index_ker] at hcount
    rw [←hcount] at hd
    exact ((by decide : Nat.Prime 5).dvd_mul.mp hd).resolve_right hker

/-- The central-cover alternating rows are excluded on their literal source
carriers. The kernel may contain the original two-core and a cubic center. -/
theorem source_local_component_alternating_central_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hz : ¬ 5 ∣ Nat.card (center (L ⧸ pCore 2 L)))
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8) :
    ¬ Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin n)) := by
  rintro ⟨e⟩
  let r := e.toMonoidHom.comp (QuotientGroup.mk' (center (L ⧸ pCore 2 L)))
  have hr : Function.Surjective r := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hrker : r.ker = center (L ⧸ pCore 2 L) := by ext x; simp [r]
  let a := QuotientGroup.mk' (pCore 2 L)
  let q := r.comp a
  have hq : Function.Surjective q := hr.comp (QuotientGroup.mk'_surjective _)
  have hk : ¬ 5 ∣ Nat.card q.ker := by
    rw [kernel_card_eq_mul_of_surjective_factor q r a hr
      (QuotientGroup.mk'_surjective _) rfl, hrker]
    rw [show a.ker = pCore 2 L from QuotientGroup.ker_mk' (pCore 2 L)]
    exact fun h => ((by decide : Nat.Prime 5).dvd_mul.mp h).elim five_not_dvd_pCore hz
  obtain ⟨P,B,hs,hPB,hfive⟩ := source_normalized_five_image_of_surjective hSyl hL hYL hSN hc q hq hk
  exact Theory.SpecificGroups.Alternating.SmallSolvableFive.not_five_dvd_of_sylow_normalizes
    hn B hs P hPB hfive

/-- The actual triple-A₆ central cover cannot be the source two-core quotient. -/
theorem source_local_component_tripleSix_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (hz : Nonempty (center (L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3))) :
    ¬ Nonempty (((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) ≃*
      alternatingGroup (Fin 6)) := by
  apply source_local_component_alternating_central_exclusion hSyl hL hYL hSN hc ?_ 6
    (Or.inr (Or.inl rfl))
  rw [Nat.card_congr hz.some.toEquiv]
  norm_num

open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic configuration excludes the literal triple-A₆
central-cover row, without identifying it with its central quotient. -/
theorem source_HStar_wreath_five_failed_quotient_no_tripleSixModel
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
          ¬ (Nonempty (center (L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (ZMod 3)) ∧
            Nonempty (((L₁ ⧸ pCore 2 L₁) ⧸ center (L₁ ⧸ pCore 2 L₁)) ≃*
              alternatingGroup (Fin 6)))) := by
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
  rintro ⟨hz,he⟩
  let Y := caseIIResidual T M (chosenStarredPreimage M V hV.normalized) Mc
  have hYM : Y ≤ M := source_caseIIResidual_le T hM.1.2 (map_subtype_le _)
  have hMN : M ≤ normalizer (Y : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hYM).mp
      (source_dihedral_five_residual_normal T hM.1.2 hu hV l hd)
  have hc : Nat.card (Y ⧸ pCore 2 Y) = 5 := by
    rw [←(pCore 2 Y).index_eq_card]
    exact (source_dihedral_five_residual_core_index hG T hempty hM hJ hu hmany hV l
      ((primeDimensionOptions_iff 5 2).mpr (Or.inr ⟨rfl,rfl⟩)) hd).1
  exact source_local_component_tripleSix_exclusion hSyl hL₁ hYL
    (inf_le_left.trans (hM.1.2.trans hMN)) hc hz he

end CFSG.Quasithin.Chapter15.Section02
