module

public import Stellmacher.ElementaryAbelianMaxFamilyMap
public import Theory.GroupTheory.DisjointCommutingProduct
public import Stellmacher.ElementaryAbelianMaxOrderSpecification

/-!
# Maximum elementary families of finite direct products

A maximum-order elementary subgroup is the product of its two projections:
the product is elementary and contains it, so maximality forces equality.
Its projections have maximum order in their factors, and conversely products
of maximum-order subgroups have maximum order. Taking generated subgroups
gives the corresponding elementary Thompson product formula.

This is the product step in Aschbacher--Smith, 16.3.12, printed p.1182.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace Stellmacher
variable {G H : Type*} [Group G] [Group H]

private theorem elementary_prod (A : Subgroup G) (B : Subgroup H)
    (hA : IsElementaryAbelian 2 A) (hB : IsElementaryAbelian 2 B) :
    IsElementaryAbelian 2 (A.prod B) := by
  let := hA
  let := hB
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · refine ⟨⟨fun x y => ?_⟩⟩
    apply (A.prodEquiv B).injective
    exact mul_comm ((A.prodEquiv B) x) ((A.prodEquiv B) y)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply Subtype.ext
    exact Prod.ext (elemPow_eq_one_of_isElementaryAbelian x.val.1 x.property.1)
      (elemPow_eq_one_of_isElementaryAbelian x.val.2 x.property.2)

private theorem card_prod (A : Subgroup G) (B : Subgroup H) :
    Nat.card (A.prod B) = Nat.card A * Nat.card B :=
  (Nat.card_congr (A.prodEquiv B).toEquiv).trans (Nat.card_prod A B)

variable [Finite G] [Finite H]

/-- Each largest elementary subgroup splits as the product of its projections. -/
theorem maxFamily_eq_prod_projections {S : Subgroup G} {T : Subgroup H}
    {E : Subgroup (G × H)} (hE : E ∈ elementaryAbelianMaxSubgroups (S.prod T)) :
    E = (E.map (MonoidHom.fst G H)).prod (E.map (MonoidHom.snd G H)) := by
  let := hE.2.1
  have hp := le_prod_iff.mp hE.1
  apply eq_of_le_of_card_ge (le_prod_iff.mpr ⟨le_rfl, le_rfl⟩)
  exact hE.2.2 _ (prod_mono hp.1 hp.2)
    (elementary_prod _ _ (hE.2.1.map _) (hE.2.1.map _))

/-- A product of members of the maximum elementary families is maximum. -/
theorem maxFamily_prod {S A : Subgroup G} {T B : Subgroup H}
    (hA : A ∈ elementaryAbelianMaxSubgroups S)
    (hB : B ∈ elementaryAbelianMaxSubgroups T) :
    A.prod B ∈ elementaryAbelianMaxSubgroups (S.prod T) := by
  refine ⟨prod_mono hA.1 hB.1, elementary_prod _ _ hA.2.1 hB.2.1, ?_⟩
  intro E hEST hE
  let := hE
  have hp := le_prod_iff.mp hEST
  calc
    Nat.card E ≤ Nat.card ((E.map (MonoidHom.fst G H)).prod
        (E.map (MonoidHom.snd G H))) :=
      card_le_of_le (le_prod_iff.mpr ⟨le_rfl, le_rfl⟩)
    _ = Nat.card (E.map (MonoidHom.fst G H)) * Nat.card (E.map (MonoidHom.snd G H)) :=
      card_prod _ _
    _ ≤ Nat.card A * Nat.card B := Nat.mul_le_mul
      (hA.2.2 _ hp.1 (hE.map _)) (hB.2.2 _ hp.2 (hE.map _))
    _ = Nat.card (A.prod B) := (card_prod _ _).symm

/-- The projections of a largest elementary subgroup are largest in their factors. -/
theorem maxFamily_projections {S : Subgroup G} {T : Subgroup H}
    {E : Subgroup (G × H)} (hE : E ∈ elementaryAbelianMaxSubgroups (S.prod T)) :
    E.map (MonoidHom.fst G H) ∈ elementaryAbelianMaxSubgroups S ∧
      E.map (MonoidHom.snd G H) ∈ elementaryAbelianMaxSubgroups T := by
  let := hE.2.1
  have hp := le_prod_iff.mp hE.1
  have hc : Nat.card E = Nat.card (E.map (MonoidHom.fst G H)) *
      Nat.card (E.map (MonoidHom.snd G H)) := by
    conv_lhs => rw [maxFamily_eq_prod_projections hE]
    exact card_prod _ _
  constructor
  · refine ⟨hp.1, hE.2.1.map _, ?_⟩
    intro A hAS hA
    have hb := hE.2.2 (A.prod (E.map (MonoidHom.snd G H))) (prod_mono hAS hp.2)
      (elementary_prod _ _ hA (hE.2.1.map _))
    rw [card_prod, hc] at hb
    exact Nat.le_of_mul_le_mul_right hb (Nat.card_pos (α := E.map (MonoidHom.snd G H)))
  · refine ⟨hp.2, hE.2.1.map _, ?_⟩
    intro B hBT hB
    have ha := hE.2.2 ((E.map (MonoidHom.fst G H)).prod B) (prod_mono hp.1 hBT)
      (elementary_prod _ _ (hE.2.1.map _) hB)
    rw [card_prod, hc] at ha
    exact Nat.le_of_mul_le_mul_left ha (Nat.card_pos (α := E.map (MonoidHom.fst G H)))

/-- Exact classification of the maximum elementary family of a direct product. -/
theorem maxFamily_prod_iff {S : Subgroup G} {T : Subgroup H} {E : Subgroup (G × H)} :
    E ∈ elementaryAbelianMaxSubgroups (S.prod T) ↔
      ∃ A ∈ elementaryAbelianMaxSubgroups S, ∃ B ∈ elementaryAbelianMaxSubgroups T,
        E = A.prod B := by
  constructor
  · intro hE
    exact ⟨_, (maxFamily_projections hE).1, _, (maxFamily_projections hE).2,
      maxFamily_eq_prod_projections hE⟩
  · rintro ⟨A, hA, B, hB, rfl⟩
    exact maxFamily_prod hA hB

/-- Elementary Thompson subgroups commute with finite direct products. -/
theorem elementaryAbelianMaxJ_prod (S : Subgroup G) (T : Subgroup H) :
    elementaryAbelianMaxJ (S.prod T) = (elementaryAbelianMaxJ S).prod (elementaryAbelianMaxJ T) := by
  apply le_antisymm
  · apply sSup_le
    intro E hE
    obtain ⟨A, hA, B, hB, rfl⟩ := maxFamily_prod_iff.mp hE
    exact prod_mono (le_sSup hA) (le_sSup hB)
  · apply prod_le_iff.mpr
    constructor
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro A hA
      obtain ⟨B, hB⟩ := elementaryAbelianMaxSubgroups_nonempty T
      exact map_le_iff_le_comap.mp
        ((prod_le_iff.mp (le_sSup (maxFamily_prod hA hB))).1)
    · apply map_le_iff_le_comap.mpr
      apply sSup_le
      intro B hB
      obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty S
      exact map_le_iff_le_comap.mp
        ((prod_le_iff.mp (le_sSup (maxFamily_prod hA hB))).2)
variable {K : Type*} [Group K]

/-- Largest elementary subgroups in any specified internal product. -/
theorem maxFamily_equiv_prod_iff (S : Subgroup K) (e : G × H ≃* S) (A : Subgroup K) :
    A ∈ elementaryAbelianMaxSubgroups S ↔
      ∃ B ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G),
      ∃ C ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup H),
        A = (B.prod C).map (S.subtype.comp e.toMonoidHom) := by
  rw [maxFamily_equiv_iff S e]
  constructor
  · rintro ⟨E, hE, rfl⟩
    rw [← top_prod_top] at hE
    obtain ⟨B, hB, C, hC, rfl⟩ := maxFamily_prod_iff.mp hE
    exact ⟨B, hB, C, hC, rfl⟩
  · rintro ⟨B, hB, C, hC, rfl⟩
    exact ⟨B.prod C, by simpa only [Subgroup.top_prod_top] using maxFamily_prod hB hC, rfl⟩

omit [Finite G] [Finite H] in
private theorem map_prod_join (f : G × H →* K) (A : Subgroup G) (B : Subgroup H) :
    (A.prod B).map f = (A.map (f.comp (MonoidHom.inl G H))) ⊔
      (B.map (f.comp (MonoidHom.inr G H))) := by
  apply le_antisymm
  · rintro x ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
    have h := (A.map (f.comp (MonoidHom.inl G H)) ⊔
      B.map (f.comp (MonoidHom.inr G H))).mul_mem
      (mem_sup_left (mem_map_of_mem _ ha)) (mem_sup_right (mem_map_of_mem _ hb))
    simpa only [MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
      ← map_mul, Prod.mk_mul_mk, mul_one, one_mul] using h
  · apply sup_le
    · rintro x ⟨a, ha, rfl⟩
      exact ⟨(a, 1), ⟨ha, B.one_mem⟩, rfl⟩
    · rintro x ⟨b, hb, rfl⟩
      exact ⟨(1, b), ⟨A.one_mem, hb⟩, rfl⟩

/-- The elementary Thompson subgroup of an internal direct product. -/
theorem elementaryAbelianMaxJ_sup_of_disjoint_of_commuting
    [Finite K] (A B : Subgroup K) (hd : Disjoint A B)
    (hc : A ≤ centralizer (B : Set K)) :
    elementaryAbelianMaxJ (A ⊔ B) = elementaryAbelianMaxJ A ⊔ elementaryAbelianMaxJ B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting A B hd hc
  let f := (A ⊔ B).subtype.comp e.toMonoidHom
  have hf : Function.Injective f := (A ⊔ B).subtype_injective.comp e.injective
  have hr : (⊤ : Subgroup (A × B)).map f = A ⊔ B := by
    ext x
    constructor
    · rintro ⟨a, _, rfl⟩
      exact (e a).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, mem_top _, congrArg Subtype.val (e.apply_symm_apply _)⟩
  have hl : f.comp (MonoidHom.inl A B) = A.subtype := by
    ext a
    exact (he a 1).trans (mul_one _)
  have hh : f.comp (MonoidHom.inr A B) = B.subtype := by
    ext b
    exact (he 1 b).trans (one_mul _)
  calc
    elementaryAbelianMaxJ (A ⊔ B) = (elementaryAbelianMaxJ (⊤ : Subgroup (A × B))).map f := by
      rw [← elementaryAbelianMaxJ_map_injective f hf, hr]
    _ = ((elementaryAbelianMaxJ (⊤ : Subgroup A)).prod
        (elementaryAbelianMaxJ (⊤ : Subgroup B))).map f := by
      rw [← top_prod_top, elementaryAbelianMaxJ_prod]
    _ = elementaryAbelianMaxJ A ⊔ elementaryAbelianMaxJ B := by
      rw [map_prod_join, hl, hh, ← elementaryAbelianMaxJ_map_injective A.subtype A.subtype_injective,
        ← elementaryAbelianMaxJ_map_injective B.subtype B.subtype_injective, ← MonoidHom.range_eq_map, ← MonoidHom.range_eq_map,
        range_subtype, range_subtype]
/-- Exact maximum-family classification for an internal direct product. -/
theorem maxFamily_sup_iff_of_disjoint_of_commuting
    [Finite K] (C D : Subgroup K) (hd : Disjoint C D)
    (hc : C ≤ centralizer (D : Set K)) (E : Subgroup K) :
    E ∈ elementaryAbelianMaxSubgroups (C ⊔ D) ↔
      ∃ A ∈ elementaryAbelianMaxSubgroups C, ∃ B ∈ elementaryAbelianMaxSubgroups D,
        E = A ⊔ B := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C D hd hc
  let f := (C ⊔ D).subtype.comp e.toMonoidHom
  have hl : f.comp (MonoidHom.inl C D) = C.subtype := by
    ext a
    exact (he a 1).trans (mul_one _)
  have hr : f.comp (MonoidHom.inr C D) = D.subtype := by
    ext b
    exact (he 1 b).trans (one_mul _)
  constructor
  · intro hE
    obtain ⟨A, hA, B, hB, hEeq⟩ := (maxFamily_equiv_prod_iff (C ⊔ D) e E).mp hE
    refine ⟨A.map C.subtype, ?_, B.map D.subtype, ?_, ?_⟩
    · have h := (maxFamily_map_injective_iff C.subtype C.subtype_injective ⊤ A).mpr hA
      simpa only [← MonoidHom.range_eq_map, range_subtype] using h
    · have h := (maxFamily_map_injective_iff D.subtype D.subtype_injective ⊤ B).mpr hB
      simpa only [← MonoidHom.range_eq_map, range_subtype] using h
    · change E = (A.prod B).map f at hEeq
      rw [hEeq, map_prod_join, hl, hr]
  · rintro ⟨A, hA, B, hB, rfl⟩
    obtain ⟨A', hA', hAA⟩ := (maxFamily_equiv_iff C (MulEquiv.refl C) A).mp hA
    obtain ⟨B', hB', hBB⟩ := (maxFamily_equiv_iff D (MulEquiv.refl D) B).mp hB
    change A = A'.map C.subtype at hAA
    change B = B'.map D.subtype at hBB
    apply (maxFamily_equiv_prod_iff (C ⊔ D) e (A ⊔ B)).mpr
    refine ⟨A', hA', B', hB', ?_⟩
    change A ⊔ B = (A'.prod B').map f
    rw [map_prod_join, hl, hr, ← hAA, ← hBB]

end Stellmacher
