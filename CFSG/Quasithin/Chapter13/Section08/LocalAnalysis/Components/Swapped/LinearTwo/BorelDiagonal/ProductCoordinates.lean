module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.Orbit
public import CFSG.Quasithin.ClassicalModels
public import Theory.GroupTheory.DisjointCommutingProduct.Projections
public import GorensteinWalter.PSL2Center

/-!
# Marked coordinates on the moving component orbit

The two distinct relative C-components have distinct images in H/O₂(H).
When those images are quasisimple, component calculus makes them commute.
The actual PSL₂ model makes the first image centerless, so multiplication
gives a direct product, with both inclusions retained. In particular the
first projection has the second component as its exact kernel.

These are the group coordinates used in Aschbacher–Smith, proof of
13.8.16(1), printed p.952 (combined manuscript of 1 March 2004). No
normality in the ambient simple group or diagonal marking is assumed.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo
variable {G : Type*} [Group G]

/-- Conjugation commutes with the actual quotient map, including its marked image. -/
theorem starImage_conjBy (H K : Subgroup G) (hKH : K ≤ H)
    {t : G} (ht : t ∈ H) :
    (Source.starImage H K).map
        (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)).toMonoidHom =
      Source.starImage H (K.conjBy t) := by
  let tH : H := ⟨t, ht⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  have hJH : K.conjBy t ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem ht (hKH hk)) (H.inv_mem ht)
  have he : (K.subgroupOf H).map (MulAut.conj tH).toMonoidHom =
      (K.conjBy t).subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le hJH, map_map]
    change (K.subgroupOf H).map ((MulAut.conj t).toMonoidHom.comp H.subtype) = _
    rw [← map_map, map_subgroupOf_eq_of_le hKH]
    rfl
  have hq : (MulAut.conj (q tH)).toMonoidHom.comp q =
      q.comp (MulAut.conj tH).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  unfold Source.starImage
  rw [map_map, hq, ← map_map, he]

/-- The second star factor is identified by the specified moving element. -/
noncomputable def starConjugateEquiv (H K : Subgroup G) (hKH : K ≤ H)
    {t : G} (ht : t ∈ H) : Source.starImage H K ≃* Source.starImage H (K.conjBy t) :=
  ((Source.starImage H K).equivMapOfInjective
    (MulAut.conj (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)).toMonoidHom
    (MulAut.conj _).injective).trans (MulEquiv.subgroupCongr (starImage_conjBy H K hKH ht))

theorem starConjugateEquiv_apply (H K : Subgroup G) (hKH : K ≤ H)
    {t : G} (ht : t ∈ H) (a : Source.starImage H K) :
    (starConjugateEquiv H K hKH ht a : Source.Hstar H) =
      QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩ * a *
        (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)⁻¹ := rfl

variable [Finite G]

/-- Distinct relative C-components remain distinct in the literal star quotient. -/
theorem starImages_ne (H K J : Subgroup G) (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) : Source.starImage H K ≠ Source.starImage H J := by
  intro he
  let _ := pCore_isNilpotent (p := 2) (G := H)
  have hh := hK.eq_of_map_quotient_eq hJ (pCore 2 H) he
  apply hne
  have hm := congrArg (fun A : Subgroup H => A.map H.subtype) hh
  simpa only [map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hJH] using hm

/-- Quasisimple star images commute because they are distinct components. -/
theorem starImages_commute (H K J : Subgroup G) (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) (hqK : IsQuasisimple (Source.starImage H K))
    (hqJ : IsQuasisimple (Source.starImage H J)) :
    ⁅Source.starImage H K, Source.starImage H J⁆ = ⊥ := by
  have hA : IsComponent (Source.Hstar H) (Source.starImage H K) :=
    ⟨(starImage_isCComponent H K hK).subnormal, hqK⟩
  have hB : IsComponent (Source.Hstar H) (Source.starImage H J) :=
    ⟨(starImage_isCComponent H J hJ).subnormal, hqJ⟩
  exact hA.commutator_eq_bot_of_ne hB (starImages_ne H K J hKH hJH hK hJ hne)

/-- An actual PSL₂ isomorphism, rather than a family label, kills the center. -/
theorem center_eq_bot_of_psl2 {D : Type*} [Group D] {q : ℕ}
    (hmodel : ClassicalGroup.IsPSL D 2 q) : center D = ⊥ := by
  obtain ⟨F, _, _, _, ⟨e⟩⟩ := hmodel
  apply le_bot_iff.mp
  intro x hx
  have hz : e x ∈ center (GorensteinWalter.PSL2 F) :=
    (Subgroup.centerCongr e ⟨x, hx⟩).property
  rw [GorensteinWalter.psl2_center_eq_bot F] at hz
  exact e.injective ((mem_bot.mp hz).trans (map_one e).symm)

private theorem disjoint_of_centerless_of_commuting {D : Type*} [Group D]
    (A B : Subgroup D) (hz : center A = ⊥) (hc : ⁅A, B⁆ = ⊥) : Disjoint A B := by
  apply disjoint_def.mpr
  intro x hx hy
  have hz' : (⟨x, hx⟩ : A) ∈ center A := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (commutator_eq_bot_iff_le_centralizer.mp hc y.property x hy).symm
  rw [hz] at hz'
  exact congrArg Subtype.val (mem_bot.mp hz')

omit [Finite G] in
/-- The star image of the actual product is the join of the two star images. -/
theorem starImage_sup (H K J : Subgroup G) (hKH : K ≤ H) (hJH : J ≤ H) :
    Source.starImage H (K ⊔ J) = Source.starImage H K ⊔ Source.starImage H J := by
  unfold Source.starImage
  rw [subgroupOf_sup hKH hJH, Subgroup.map_sup]

/-- Construct product coordinates and retain the values on both actual factors. -/
theorem exists_star_product_coordinates (H K J : Subgroup G)
    (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) (hqK : IsQuasisimple (Source.starImage H K))
    (hqJ : IsQuasisimple (Source.starImage H J))
    {q : ℕ} (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 q) :
    ∃ e : Source.starImage H K × Source.starImage H J ≃* Source.starImage H (K ⊔ J),
      ∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) * b := by
  have hc := starImages_commute H K J hKH hJH hK hJ hne hqK hqJ
  have hd := disjoint_of_centerless_of_commuting _ _ (center_eq_bot_of_psl2 hmodel) hc
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting _ _ hd
    (commutator_eq_bot_iff_le_centralizer.mp hc)
  exact ⟨e.trans (MulEquiv.subgroupCongr (starImage_sup H K J hKH hJH).symm), he⟩

/-- The first factor projection, including its kernel and both inclusion formulas. -/
theorem exists_star_first_projection (H K J : Subgroup G)
    (hKH : K ≤ H) (hJH : J ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hJ : (J.subgroupOf H).IsCComponent)
    (hne : K ≠ J) (hqK : IsQuasisimple (Source.starImage H K))
    (hqJ : IsQuasisimple (Source.starImage H J))
    {q : ℕ} (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 q) :
    ∃ f : Source.starImage H (K ⊔ J) →* Source.starImage H K,
      Function.Surjective f ∧
      f.ker = (Source.starImage H J).subgroupOf (Source.starImage H (K ⊔ J)) ∧
      (∀ a : Source.starImage H K, ∀ ha,
        f ⟨a, ha⟩ = a) ∧
      (∀ b : Source.starImage H J, ∀ hb,
        f ⟨b, hb⟩ = 1) := by
  have hc := starImages_commute H K J hKH hJH hK hJ hne hqK hqJ
  have hd := disjoint_of_centerless_of_commuting _ _ (center_eq_bot_of_psl2 hmodel) hc
  rw [starImage_sup H K J hKH hJH]
  obtain ⟨f, hf, hk, hleft, hright⟩ := exists_left_projection_of_disjoint_of_commuting
    _ _ hd (commutator_eq_bot_iff_le_centralizer.mp hc)
  exact ⟨f, hf, hk, fun a _ => hleft a, fun b _ => hright b⟩

/-- Coordinates by two copies of K*, with the second inclusion given by the
actual moving conjugation. Quasisimplicity of the second factor is derived. -/
theorem exists_moving_star_coordinates (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent)
    (hqK : IsQuasisimple (Source.starImage H K)) {t : G} (ht : t ∈ H)
    (hm : t ∉ normalizer (K : Set G))
    {q : ℕ} (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 q) :
    ∃ e : Source.starImage H K × Source.starImage H K ≃*
        Source.starImage H (K ⊔ K.conjBy t),
      ∀ a b, (e (a, b) : Source.Hstar H) = (a : Source.Hstar H) *
        (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩ * b *
          (QuotientGroup.mk' (pCore 2 H) ⟨t, ht⟩)⁻¹) := by
  let c := starConjugateEquiv H K hKH ht
  let _ := hqK
  have hqJ : IsQuasisimple (Source.starImage H (K.conjBy t)) :=
    IsQuasisimple.of_mulEquiv c
  obtain ⟨hJH, hJ⟩ := conjugate_isCComponent H K hKH hK ht
  have hne : K ≠ K.conjBy t := fun he => hm (mem_normalizer_iff_map_conj_eq.mpr he.symm)
  obtain ⟨e, he⟩ := exists_star_product_coordinates H K (K.conjBy t)
    hKH hJH hK hJ hne hqK hqJ hmodel
  refine ⟨(MulEquiv.prodCongr (MulEquiv.refl _) c).trans e, ?_⟩
  intro a b
  exact he a (c b)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

end
