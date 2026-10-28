module
public import CFSG.Quasithin.Chapter15.Section02.Preliminaries.WreathFiveLinearExclusion
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Actual quotient transports for the marked-five model comparison

The original local A₅ remains a local component after restriction to the
full Sylow in a containing component and after its two-core quotient. If
the target model has order different from sixty, its local-component join
with that Sylow is proper. A solvable-kernel rank-one projection then bounds
the field degree by two. Separately, the normalized residual of two-core
index five retains that exact index under the actual quotient map.

These are the maps used by the remaining non-linear model exclusions in
original 15.2.4; no group classification or whole-module identification is
assumed. Source: Aschbacher--Smith, printed pp.1106--1107.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section02
open ChapterB.QuasisimpleSource
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
theorem local_five_degree_of_projection
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


variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A source component is perfect on its original carrier. -/
theorem source_component_perfect {H K : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) : Group.IsPerfect K := by
  let : Group.IsPerfect (K.subgroupOf H) := hK.2.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hK.1).toMonoidHom)
    (subgroupOfEquivOfLe hK.1).surjective

/-- The local A₅ and full Sylow map to a proper local-component join in any
actual two-core quotient model whose order differs from sixty. -/
theorem source_local_component_model_data
    {H K S W L : Subgroup G}
    (hK : K ∈ Chapter1.cComponentsIn H) (hSH : S ≤ H)
    (heK : Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)))
    (hSyl : Chapter1.IsSylowIn 2 S W)
    (hL : L ∈ Chapter1.cComponentsIn W) (hKL : K ≤ L)
    {D : Type*} [Group D] [Finite D]
    (e : (L ⧸ pCore 2 L) ≃* D) (hD : Nat.card D ≠ 60) :
    ∃ (P : Sylow 2 D) (f : K →* D),
      f.range ∈ ChapterA.Section03.localCComponents P ∧
      f.range ⊔ (P : Subgroup D) ≠ ⊤ := by
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
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqker : q.ker = pCore 2 L := by ext x; simp [q]
  let : Group.IsSolvable q.ker := by
    rw [hqker]
    let := pCore_isNilpotent (p := 2) (G := L)
    infer_instance
  let P' := P.mapSurjective (f := q) hq
  let f := q.comp (inclusion hKL)
  have hr : f.range = B.map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨y,rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  have hl : f.range ∈ ChapterA.Section03.localCComponents P' := by
    rw [hr]
    exact Chapter1.Section02.localCComponents_map_of_solvable_ker hlB q
  refine ⟨P',f,hl,?_⟩
  intro ht
  rw [hr] at ht
  have hmap : (B ⊔ (P : Subgroup L)).map q = ⊤ := by
    simpa only [Subgroup.map_sup, P', Sylow.coe_mapSurjective] using ht
  have hcore : pCore 2 L ≤ B ⊔ (P : Subgroup L) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans le_sup_right
  have hj : B ⊔ (P : Subgroup L) = ⊤ := by
    have hh := congrArg (comap q) hmap
    simpa only [comap_map_eq,hqker,sup_eq_left.mpr hcore,comap_top] using hh
  have hBC : B.IsCComponent := by
    have hb := hlB
    change (B.subgroupOf (B ⊔ (P : Subgroup L))).IsCComponent at hb
    rw [hj] at hb
    have hh := hb.map_subtype (show (⊤ : Subgroup L).IsSubnormal from .top)
    simpa only [map_subgroupOf_eq_of_le le_top] using hh
  have hLC : (⊤ : Subgroup L).IsCComponent := by
    have hh := hL.2.subgroupOf le_rfl
    rw [subgroupOf_self] at hh
    have ht := hh.map_equiv (subgroupOfEquivOfLe hL.1)
    simpa only [map_top_of_surjective (subgroupOfEquivOfLe hL.1).toMonoidHom
      (subgroupOfEquivOfLe hL.1).surjective] using ht
  have hb : B = ⊤ := hBC.eq_of_le hLC le_top
  have heq : K = L := le_antisymm hKL (subgroupOf_eq_top.mp hb)
  subst L
  apply hD
  rw [←Nat.card_congr e.toEquiv,Nat.card_congr heK.some.toEquiv,nat_card_alternatingGroup]
  norm_num

/-- The original normalized five-residual retains its exact two-core index
under the actual containing-component quotient. -/
theorem source_normalized_five_section_image
    {W L Y S : Subgroup G}
    (hSyl : Chapter1.IsSylowIn 2 S W) (hL : L ∈ Chapter1.cComponentsIn W)
    (hYL : Y ≤ L) (hSN : S ≤ normalizer (Y : Set G))
    (hc : Nat.card (Y ⧸ pCore 2 Y) = 5)
    {D : Type*} [Group D] [Finite D] (e : (L ⧸ pCore 2 L) ≃* D) :
    ∃ (P : Sylow 2 D) (B : Subgroup D),
      (P : Subgroup D) ≤ normalizer (B : Set D) ∧
      Nat.card (B ⧸ pCore 2 B) = 5 := by
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
  refine ⟨P',f.range,?_,?_⟩
  · have hPN : (P : Subgroup L) ≤ normalizer (Y₀ : Set L) := by
      rw [hP',←subgroupOf_normalizer_eq hYL]
      exact comap_mono hSN
    rw [hf]
    exact (map_mono hPN).trans (Y₀.le_normalizer_map q)
  · have hk : IsPGroup 2 f.rangeRestrict.ker := by
      have he : f.rangeRestrict.ker = f.ker := by ext x; simp
      rw [he]
      exact hker
    rw [←Nat.card_congr (f.rangeRestrict.pCoreQuotientEquiv
      f.rangeRestrict_surjective hk).toEquiv,hc₀]

end CFSG.Quasithin.Chapter15.Section02
