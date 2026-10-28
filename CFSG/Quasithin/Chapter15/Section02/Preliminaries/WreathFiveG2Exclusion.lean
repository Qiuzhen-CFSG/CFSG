module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearThree
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.AtlasPort.LinearGroups.G2.HigherFieldResiduals
public import Theory.AtlasPort.LinearGroups.G2.SolvableSylowPlacement
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder

/-!
# G₂ exclusions in the original marked-five wreath argument

Restrict the actual local A₅ component to the full Sylow in its containing
component, and map both through the literal two-core quotient. If the local
image and the Sylow generate G₂, lifting forces the two original components
to coincide, contradicting their quotient orders. Otherwise the proper Sylow
overgroup theorem puts the image in one of the root parabolics. Perfectness
places it in the parabolic residual, whose SL₂ quotient receives the whole
local image. Its order divides sixty, bounding the field degree by two.

The original normalized five-residual has solvable image with order divisible
by five. Together with the Sylow that image generates a solvable overgroup.
For degree two it lies in a Borel of order 4⁶·3², a contradiction. For degree
one the full model and its derived subgroup both have order prime to five.
The original H-star consumer supplies all normalization and order premises.

Source: Aschbacher--Smith, original 15.2.4, printed pp.1106--1107. This is a
direct exclusion of the G₂ rows in the C.2.7/A.3.15 comparison; it does not
assume that the two-core quotient exhausts those model rows.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
namespace WreathFiveG2
variable {X : Type*} [Group X] [Finite X] [Group.IsPerfect X]
omit [Finite X] in
private theorem rankOne_degree_of_surjective
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (f : X →* SL(2,F.Carrier)) (hf : Function.Surjective f) : F.degree ≤ 2 := by
  have hk := Matrix.SpecialLinearGroup.perfect_hom_twoCore_le_ker f
  let q := QuotientGroup.lift (pCore 2 X) f hk
  have hq : Function.Surjective q := QuotientGroup.lift_surjective_of_surjective _ f hf hk
  have hd : 2 ^ F.degree ∣ 60 := by
    have hh : 2 ^ F.degree ∣ Nat.card SL(2,F.Carrier) := by
      rw [GorensteinWalter.sl2_card_formula,F.card_eq]
      exact dvd_mul_right _ _
    exact hc ▸ hh.trans (card_dvd_of_surjective q hq)
  by_contra hn
  have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 (by omega : 3 ≤ F.degree)).trans hd
  norm_num at hh

private theorem rankOne_local_eq_top (F : BinaryField) (hF : 1 < F.degree)
    (P : Sylow 2 SL(2,F.Carrier)) (B : Subgroup SL(2,F.Carrier))
    (hB : B ∈ ChapterA.Section03.localCComponents P) : B = ⊤ := by
  have hlarge : 3 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    omega
  let : IsQuasisimple SL(2,F.Carrier) :=
    Theory.SpecificGroups.SL2.ResidualTwoExtension.quasisimple_of_equiv hlarge (.refl _)
  have ht : (⊤ : Subgroup SL(2,F.Carrier)).IsCComponent :=
    (show IsComponent SL(2,F.Carrier) ⊤ from
      ⟨.top,IsQuasisimple.of_mulEquiv topEquiv.symm⟩).isCComponent
  have hj : B ⊔ (P : Subgroup SL(2,F.Carrier)) = ⊤ := by
    by_contra hn
    let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup P _ le_sup_right hn
    exact hB.not_isSolvable inferInstance
  change (B.subgroupOf (B ⊔ (P : Subgroup SL(2,F.Carrier)))).IsCComponent at hB
  rw [hj] at hB
  have hc : B.IsCComponent := by
    have h := hB.map_subtype (show (⊤ : Subgroup SL(2,F.Carrier)).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using h
  exact hc.eq_of_le ht le_top

omit [Finite X] in
private theorem degree_of_local_projection
    {A : Type*} [Group A] [Finite A]
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 A) (f : X →* A)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (D : Subgroup A) (hBD : f.range ≤ D) (hPD : (P : Subgroup A) ≤ D)
    (q : D →* SL(2,F.Carrier)) (hq : Function.Surjective q)
    [Group.IsSolvable q.ker] : F.degree ≤ 2 := by
  by_contra hn
  have hF : 1 < F.degree := by omega
  let P₀ := P.subtype hPD
  have hl := ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hBD
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl q
  have he : (f.range.subgroupOf D).map q = ⊤ :=
    rankOne_local_eq_top F hF (P₀.mapSurjective hq) _ hl'
  let f₀ := f.codRestrict D (fun x => hBD ⟨x,rfl⟩)
  have hr : f₀.range = f.range.subgroupOf D := by
    ext x
    constructor
    · rintro ⟨y,rfl⟩
      exact ⟨y,rfl⟩
    · rintro ⟨y,hy⟩
      exact ⟨y,Subtype.ext hy⟩
  have hs : Function.Surjective (q.comp f₀) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,hr,he]
  exact hn (rankOne_degree_of_surjective hc F (q.comp f₀) hs)

omit [Finite X] in
/-- The local A₅ quotient bounds the field of a proper full-Sylow G₂ join.
This intrinsic form also applies to source maps through solvable kernels. -/
theorem degree_of_proper_g2_join
    (hc : Nat.card (X ⧸ pCore 2 X) = 60) (F : BinaryField)
    (P : Sylow 2 (Atlas.G2.Model F.Carrier)) (f : X →* Atlas.G2.Model F.Carrier)
    (hlocal : f.range ∈ ChapterA.Section03.localCComponents P)
    (hproper : f.range ⊔ (P : Subgroup (Atlas.G2.Model F.Carrier)) ≠ ⊤) : F.degree ≤ 2 := by
  by_contra hn
  have hcard : 2 < Nat.card F.Carrier := by
    rw [F.card_eq]
    have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
    omega
  let U := Atlas.G2.LieParabolicSetup.sylow (F := F.Carrier)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F.Carrier) P U
  let a := MulAut.conj g
  let f' := a.toMonoidHom.comp f
  let P' := P.mapSurjective (f := a.toMonoidHom) a.surjective
  have hP : (P : Subgroup (Atlas.G2.Model F.Carrier)).map a.toMonoidHom =
      Atlas.G2.unipotent := congrArg Sylow.toSubgroup hg
  have hP' : (P' : Subgroup (Atlas.G2.Model F.Carrier)) = Atlas.G2.unipotent := hP
  let : Group.IsSolvable a.toMonoidHom.ker := by
    have he : a.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff a.toMonoidHom).mpr a.injective
    rw [he]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hlocal a.toMonoidHom
  have hl' : f'.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hP',←hP]
    simpa only [f',MonoidHom.range_comp] using hl
  have hj : f'.range ⊔ (P' : Subgroup (Atlas.G2.Model F.Carrier)) ≠ ⊤ := by
    intro hh
    apply hproper
    apply (map_injective (f := a.toMonoidHom) a.injective)
    dsimp only [f'] at hh
    rw [MonoidHom.range_comp,hP',←hP] at hh
    simpa only [Subgroup.map_sup,map_top_of_surjective a.toMonoidHom a.surjective,
      MonoidHom.range_comp] using hh
  have hp := Atlas.G2.ProperSylowOvergroups.le_parabolic
    (f'.range ⊔ (P' : Subgroup (Atlas.G2.Model F.Carrier))) (hP' ▸ le_sup_right)
    (lt_top_iff_ne_top.mpr hj)
  let : Group.IsPerfect f'.range := Group.IsPerfect.range f'
  rcases hp with hp | hp
  · have hd : f'.range ≤ Atlas.G2.LieParabolicSetup.local₁ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₁_residual hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let q := Atlas.G2.LieParabolicSetup.shortSLHom (F := F.Carrier)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 (Atlas.G2.LieParabolicSetup.local₁ (F := F.Carrier)) := by
        rw [Atlas.G2.LieParabolicSetup.local₁_intrinsic_pCore]
        exact Atlas.G2.LieParabolicSetup.shortSLHom_ker
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := Atlas.G2.LieParabolicSetup.local₁ (F := F.Carrier))
      infer_instance
    exact hn (degree_of_local_projection hc F P' f' hl' _ hd
      (hP' ▸ Atlas.G2.LieParabolicSetup.unipotent_le_local₁) q
      Atlas.G2.LieParabolicSetup.shortSLHom_surjective)
  · have hd : f'.range ≤ Atlas.G2.LieParabolicSetup.local₂ := by
      rw [←Atlas.G2.HigherFieldResiduals.parabolic₂_residual hcard]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    let q := Atlas.G2.LieParabolicSetup.longSLHom (F := F.Carrier)
    let : Group.IsSolvable q.ker := by
      have he : q.ker = pCore 2 (Atlas.G2.LieParabolicSetup.local₂ (F := F.Carrier)) := by
        rw [Atlas.G2.LieParabolicSetup.local₂_pCore]
        exact Atlas.G2.LieParabolicSetup.longSLHom_ker
      rw [he]
      let := pCore_isNilpotent (p := 2) (G := Atlas.G2.LieParabolicSetup.local₂ (F := F.Carrier))
      infer_instance
    exact hn (degree_of_local_projection hc F P' f' hl' _ hd
      (hP' ▸ Atlas.G2.LieParabolicSetup.unipotent_le_local₂) q
      Atlas.G2.LieParabolicSetup.longSLHom_surjective)

end WreathFiveG2
open WreathFiveG2
variable {G : Type*} [Group G] [Finite G]

/-- A full-Sylow local A₅ bounds the degree of a binary G₂
containing-component quotient. Every parabolic placement and projection
hypothesis is proved from the displayed local component data. -/
public theorem source_local_component_g2_degree_le_two
    {H K S W L₁ : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL₁ : L₁ ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L₁)
    (F : BinaryField)
    (e : (L₁ ⧸ pCore 2 L₁) ≃* (Atlas.G2.Model F.Carrier)) : F.degree ≤ 2 := by
  have hlocal : K ∈ ChapterA.Section03.localCComponents S :=
    hK.2.subgroupOf_of_le le_sup_left (sup_le hK.1 hSH)
  obtain ⟨P,hP⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    hSyl hL₁.1 hL₁.2.subnormal
  have hP' : (P : Subgroup L₁) = S.subgroupOf L₁ := by
    apply map_injective L₁.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  let B := K.subgroupOf L₁
  have hlB : B ∈ ChapterA.Section03.localCComponents P := by
    rw [hP']
    exact ChapterA.Section03.SourceEmbeddings.local_restrict hlocal hKL
  let : Group.IsPerfect (B.subgroupOf (B ⊔ (P : Subgroup L₁))) := hlB.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup L₁) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show B ≤ B ⊔ (P : Subgroup L₁) from le_sup_left)).surjective
  let b := subgroupOfEquivOfLe hKL
  have hcB : Nat.card (B ⧸ pCore 2 B) = 60 := by
    let be := (QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans heK.some
    rw [Nat.card_congr be.toEquiv,nat_card_alternatingGroup]
    norm_num
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L₁))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 L₁ := by ext x; simp [q]
  let : Group.IsSolvable q.ker := by
    rw [hqker]
    let := pCore_isNilpotent (p := 2) (G := L₁)
    infer_instance
  let P' := P.mapSurjective (f := q) hq
  have hPmap : (P' : Subgroup (Atlas.G2.Model F.Carrier)) = (P : Subgroup L₁).map q := rfl
  let f := q.comp B.subtype
  have hl : f.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hPmap]
    simpa only [f,MonoidHom.range_comp,range_subtype] using
      Chapter1.Section02.localCComponents_map_of_solvable_ker hlB q
  have hp : f.range ⊔ (P' : Subgroup (Atlas.G2.Model F.Carrier)) ≠ ⊤ := by
    intro ht
    dsimp only [f] at ht
    rw [MonoidHom.range_comp,range_subtype,hPmap] at ht
    have hmap : (B ⊔ (P : Subgroup L₁)).map q = ⊤ := by
      simpa only [Subgroup.map_sup] using ht
    have hcore : pCore 2 L₁ ≤ B ⊔ (P : Subgroup L₁) :=
      (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right
    have hj : B ⊔ (P : Subgroup L₁) = ⊤ := by
      have hh := congrArg (comap q) hmap
      simpa only [comap_map_eq,hqker,sup_eq_left.mpr hcore,comap_top] using hh
    have hBC : B.IsCComponent := by
      have hb := hlB
      change (B.subgroupOf (B ⊔ (P : Subgroup L₁))).IsCComponent at hb
      rw [hj] at hb
      have hh := hb.map_subtype (show (⊤ : Subgroup L₁).IsSubnormal from .top)
      simpa only [map_subgroupOf_eq_of_le le_top] using hh
    have hLC : (⊤ : Subgroup L₁).IsCComponent := by
      have hh := hL₁.2.subgroupOf le_rfl
      rw [subgroupOf_self] at hh
      have ht := hh.map_equiv (subgroupOfEquivOfLe hL₁.1)
      simpa only [map_top_of_surjective (subgroupOfEquivOfLe hL₁.1).toMonoidHom
        (subgroupOfEquivOfLe hL₁.1).surjective] using ht
    have hb : B = ⊤ := hBC.eq_of_le hLC le_top
    have heq : K = L₁ := le_antisymm hKL (subgroupOf_eq_top.mp hb)
    subst L₁
    have hc : Nat.card (Atlas.G2.Model F.Carrier) = 60 := by
      rw [←Nat.card_congr e.toEquiv,Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
      norm_num
    have hd : 2 ^ (F.degree * 6) ∣ 60 := by
      have hh := (Atlas.G2.unipotent (K := F.Carrier)).card_subgroup_dvd_card
      rw [Atlas.G2.card_unipotent,F.card_eq,←pow_mul,hc] at hh
      exact hh
    have h3 : 3 ≤ F.degree * 6 := by have := F.degree_pos; omega
    have hh : 8 ∣ 60 := (Nat.pow_dvd_pow 2 h3).trans hd
    norm_num at hh
  exact WreathFiveG2.degree_of_proper_g2_join hcB F P' f hl hp


namespace WreathFiveG2
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


private theorem small_solvable_overgroup_five_free
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 (Atlas.G2.Model F.Carrier))
    (D : Subgroup (Atlas.G2.Model F.Carrier)) [Group.IsSolvable D]
    (hPD : (P : Subgroup (Atlas.G2.Model F.Carrier)) ≤ D) : ¬ 5 ∣ Nat.card D := by
  intro hd
  by_cases h1 : F.degree = 1
  · have hh := hd.trans D.card_subgroup_dvd_card
    rw [Atlas.G2.card_Model,F.card_eq,h1] at hh
    norm_num at hh
  have h2 : F.degree = 2 := by have := F.degree_pos; omega
  have hl : 2 < Nat.card F.Carrier := by rw [F.card_eq,h2]; decide
  let U := Atlas.G2.LieParabolicSetup.sylow (F := F.Carrier)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Atlas.G2.Model F.Carrier) P U
  let a := MulAut.conj g
  have hP : (P : Subgroup (Atlas.G2.Model F.Carrier)).map a.toMonoidHom =
      Atlas.G2.unipotent := congrArg Sylow.toSubgroup hg
  let D' := D.map a.toMonoidHom
  let : Group.IsSolvable D' :=
    Group.isSolvable_of_surjective (a.toMonoidHom.subgroupMap_surjective D)
  have hle := Atlas.G2.SolvableSylowPlacement.le_borel hl D'
    (hP ▸ map_mono hPD) inferInstance
  have hc : Nat.card D = Nat.card D' :=
    Nat.card_congr (equivMapOfInjective D a.toMonoidHom a.injective).toEquiv
  have hd' : 5 ∣ Nat.card D' := hc ▸ hd
  have hh := hd'.trans (card_dvd_of_le hle)
  rw [Atlas.G2.card_borel,F.card_eq,h2] at hh
  norm_num at hh

/-- A normalized solvable subgroup of a small binary G₂ model cannot have
order divisible by five. -/
theorem no_small_normalized_five
    (F : BinaryField) (hF : F.degree ≤ 2) (P : Sylow 2 (Atlas.G2.Model F.Carrier))
    (B : Subgroup (Atlas.G2.Model F.Carrier)) [Group.IsSolvable B]
    (hPB : (P : Subgroup (Atlas.G2.Model F.Carrier)) ≤ normalizer (B : Set (Atlas.G2.Model F.Carrier)))
    (hfive : 5 ∣ Nat.card B) : False := by
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  let : Group.IsSolvable (B ⊔ (P : Subgroup (Atlas.G2.Model F.Carrier)) : Subgroup (Atlas.G2.Model F.Carrier)) :=
    solvable_normalized_sup B P hPB
  exact small_solvable_overgroup_five_free F hF P _ le_sup_right
    (hfive.trans (card_dvd_of_le (show B ≤ B ⊔ (P : Subgroup (Atlas.G2.Model F.Carrier)) from le_sup_left)))

end WreathFiveG2

/-- The actual local A₅ and normalized five-residual exclude every full
binary G₂ quotient, including the field of two elements. -/
theorem source_local_component_g2_exclusion
    {H K S W L Y : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    (F : BinaryField) : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.G2.Model F.Carrier) := by
  rintro ⟨e⟩
  have hF := source_local_component_g2_degree_le_two hK hSH heK hSyl hL hKL F e
  apply WreathFiveG2.no_model_normalized_five_section hSyl hL hYL hSN hc e
  intro P B hsol hn hfive
  let := hsol
  exact WreathFiveG2.no_small_normalized_five F hF P B hn hfive

/-- The binary derived G₂ row has order prime to five, so cannot contain
the image of the actual five-residual through the two-core quotient. -/
theorem source_local_component_g2_derived_exclusion
    {S W L Y : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5) :
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) := by
  rintro ⟨e⟩
  apply WreathFiveG2.no_model_normalized_five_section hSyl hL hYL hSN hc e
  intro _ B _ _ hfive
  have hh := hfive.trans B.card_subgroup_dvd_card
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hh
  norm_num at hh
open Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative
open Section01 Section03 ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor ChapterD.CyclicSource

/-- The original failed-parabolic wreath-five configuration has neither binary
full G₂ two-core quotient at any field size, nor the binary derived row. -/
theorem source_HStar_wreath_five_failed_quotient_no_g2Models
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
          (∀ F : ChapterB.QuasisimpleSource.BinaryField,
            ¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Atlas.G2.Model F.Carrier)) ∧
          ¬ Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* commutator (Atlas.G2.Model (ZMod 2)))) := by
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
  · intro F
    exact source_local_component_g2_exclusion hK
      (inf_le_left.trans hH.1.1.2) heK hSyl hL₁ hKL hYL
      (inf_le_left.trans (hM.1.2.trans hMN)) hc F
  · exact source_local_component_g2_derived_exclusion hSyl hL₁ hYL
      (inf_le_left.trans (hM.1.2.trans hMN)) hc

end CFSG.Quasithin.Chapter15.Section02
