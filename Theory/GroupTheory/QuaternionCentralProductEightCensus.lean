module
public import Theory.GroupTheory.QuaternionCentralProductCenter
public import Theory.GroupTheory.NormalizedSupCard
public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.Group.Graph
public import Mathlib.Data.Fintype.Perm

/-!
# Counting elementary eights in a quaternion central product

An elementary eight contains the common center and projects onto both central
quotients. Its inverse image in the direct product consequently determines the
graph of an isomorphism of the two central quotients of order four. There are
at most six such isomorphisms: each permutes their three nonidentity elements.

This is the intrinsic quaternion geometry supporting Stellmacher (8.6)(a),
`refs/latex/stellmacher-n-group.tex`.
-/

open scoped Pointwise
namespace Subgroup

private theorem quaternion_square_one_central : ∀ x : QuaternionGroup 2,
    x ^ 2 = 1 → ∀ y, y * x = x * y := by decide

private theorem inf_le_shared_center_of_elementary
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] : U ⊓ B ≤ B ⊓ C := by
  obtain ⟨e⟩ := hB
  rw [intersection_eq_factor_center B C ⟨e⟩ hinter hcomm]
  intro x hx
  refine ⟨⟨x, hx.2⟩, mem_center_iff.mpr ?_, rfl⟩
  intro y
  apply e.injective
  simp only [map_mul]
  apply quaternion_square_one_central
  rw [← map_pow]
  have hx2 : (⟨x, hx.2⟩ : B) ^ 2 = 1 :=
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) x hx.1)
  rw [hx2, map_one]

private theorem elementary_eight_intersections
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUV : U ≤ B ⊔ C) :
    U ⊓ B = B ⊓ C ∧ U ⊓ C = B ⊓ C ∧
      U ⊔ B = B ⊔ C ∧ U ⊔ C = B ⊔ C := by
  classical
  have hBn : C ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  have hVBn : B ⊔ C ≤ normalizer (B : Set G) := sup_le B.le_normalizer hBn
  have hVCn : B ⊔ C ≤ normalizer (C : Set G) := sup_le hCn C.le_normalizer
  have hBcard : Nat.card B = 8 := by
    obtain ⟨e⟩ := hB
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hCcard : Nat.card C = 8 := by
    obtain ⟨e⟩ := hC
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hVcard : Nat.card (B ⊔ C : Subgroup G) = 32 := by
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B C hBn
    rw [hBcard, hCcard, hinter] at hh
    omega
  have hUBI := inf_le_shared_center_of_elementary B C U hB hinter hcomm
  have hUCI : U ⊓ C ≤ B ⊓ C := by
    rw [inf_comm B C]
    exact inf_le_shared_center_of_elementary C B U hC
      (by simpa only [inf_comm] using hinter) (fun c hc b hb => (hcomm b hb c hc).symm)
  have hUBcard : Nat.card (U ⊓ B : Subgroup G) = 2 := by
    have hle : Nat.card (U ⊓ B : Subgroup G) ≤ 2 := by
      simpa only [hinter] using card_le_of_le hUBI
    have hsup : Nat.card (U ⊔ B : Subgroup G) ≤ 32 := by
      simpa only [hVcard] using card_le_of_le (sup_le hUV le_sup_left)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B U (hUV.trans hVBn)
    rw [hBcard, hU, inf_comm B U, sup_comm B U] at hh
    interval_cases hc : Nat.card (U ⊓ B : Subgroup G) <;> omega
  have hUCcard : Nat.card (U ⊓ C : Subgroup G) = 2 := by
    have hle : Nat.card (U ⊓ C : Subgroup G) ≤ 2 := by
      simpa only [hinter] using card_le_of_le hUCI
    have hsup : Nat.card (U ⊔ C : Subgroup G) ≤ 32 := by
      simpa only [hVcard] using card_le_of_le (sup_le hUV le_sup_right)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C U (hUV.trans hVCn)
    rw [hCcard, hU, inf_comm C U, sup_comm C U] at hh
    interval_cases hc : Nat.card (U ⊓ C : Subgroup G) <;> omega
  have hUB : U ⊔ B = B ⊔ C := by
    apply eq_of_le_of_card_ge (sup_le hUV le_sup_left)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes B U (hUV.trans hVBn)
    rw [hBcard, hU, inf_comm B U, hUBcard, sup_comm B U] at hh
    rw [hVcard]
    omega
  have hUC : U ⊔ C = B ⊔ C := by
    apply eq_of_le_of_card_ge (sup_le hUV le_sup_right)
    have hh := card_mul_eq_card_inf_mul_card_sup_of_normalizes C U (hUV.trans hVCn)
    rw [hCcard, hU, inf_comm C U, hUCcard, sup_comm C U] at hh
    rw [hVcard]
    omega
  exact ⟨eq_of_le_of_card_ge hUBI (by rw [hUBcard, hinter]),
    eq_of_le_of_card_ge hUCI (by rw [hUCcard, hinter]), hUB, hUC⟩

private theorem card_mulEquiv_le_six
    {A D : Type*} [Group A] [Group D] [Finite A] [Finite D]
    (hA : Nat.card A = 4) : Nat.card (A ≃* D) ≤ 6 := by
  classical
  let _ := Fintype.ofFinite A
  cases isEmpty_or_nonempty (A ≃* D) with
  | inl h => simp
  | inr h =>
    let e := h.some
    let X := {a : A // a ≠ 1}
    let f : (A ≃* D) → Equiv.Perm X := fun g =>
      (g.trans e.symm).toEquiv.subtypeEquiv (by simp)
    have hf : Function.Injective f := by
      intro g k hgk
      ext a
      by_cases ha : a = 1
      · simp [ha]
      · have hh := congrArg Subtype.val (Equiv.congr_fun hgk (⟨a,ha⟩ : X))
        exact e.symm.injective hh
    have hX : Nat.card X = 3 := by
      change Nat.card ↥(({1} : Set A)ᶜ) = 3
      rw [Nat.card_eq_fintype_card, Fintype.card_compl_set,
        ← Nat.card_eq_fintype_card, hA]
      simp
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_eq_fintype_card (α := Equiv.Perm X), Fintype.card_perm,
      ← Nat.card_eq_fintype_card, hX] at hh
    exact hh

-- The line-test argument follows Mathlib.GroupTheory.Goursat
-- (Yaël Dillies, 2024; Apache 2.0), with specified coordinate kernels.
private theorem exists_quotient_graph
    {A D : Type*} [Group A] [Group D]
    (I : Subgroup (A × D)) (N : Subgroup A) (M : Subgroup D)
    [N.Normal] [M.Normal]
    (h₁ : Function.Surjective (Prod.fst ∘ I.subtype))
    (h₂ : Function.Surjective (Prod.snd ∘ I.subtype))
    (hN : ∀ a, (a, 1) ∈ I ↔ a ∈ N) (hM : ∀ d, (1, d) ∈ I ↔ d ∈ M) :
    ∃ e : A ⧸ N ≃* D ⧸ M,
      I = e.toMonoidHom.graph.comap ((QuotientGroup.mk' N).prodMap (QuotientGroup.mk' M)) := by
  let q := (QuotientGroup.mk' N).prodMap (QuotientGroup.mk' M)
  have hline (x y : I) : (q x.val).1 = (q y.val).1 ↔ (q x.val).2 = (q y.val).2 := by
    change (x.val.1 : A ⧸ N) = y.val.1 ↔ (x.val.2 : D ⧸ M) = y.val.2
    rw [eq_comm]
    simp only [QuotientGroup.eq_iff_div_mem, ← hN, ← hM]
    constructor <;> intro h
    · simpa [Prod.mul_def, Prod.div_def] using I.div_mem (I.mul_mem h x.property) y.property
    · simpa [Prod.mul_def, Prod.div_def] using I.div_mem (I.mul_mem h y.property) x.property
  obtain ⟨e, he⟩ := (q.comp I.subtype).exists_mulEquiv_range_eq_graph
    ((QuotientGroup.mk'_surjective N).comp h₁)
    ((QuotientGroup.mk'_surjective M).comp h₂) hline
  refine ⟨e, ?_⟩
  rw [← he, MonoidHom.range_comp, range_subtype, comap_map_eq_self]
  rintro ⟨a,d⟩ h
  have hh : a ∈ N ∧ d ∈ M := by
    simpa [q, MonoidHom.mem_ker, Prod.ext_iff, QuotientGroup.eq_one_iff] using h
  simpa using I.mul_mem ((hN a).mpr hh.1) ((hM d).mpr hh.2)

private def commutingProductHom
    {G : Type*} [Group G] (B C : Subgroup G)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) : B × C →* G where
  toFun x := (x.1 : G) * x.2
  map_one' := by simp
  map_mul' x y := by
    change ((x.1 : G) * y.1) * ((x.2 : G) * y.2) =
      ((x.1 : G) * x.2) * ((y.1 : G) * y.2)
    rw [mul_assoc, ← mul_assoc (y.1 : G), hcomm y.1 y.1.property x.2 x.2.property]
    simp only [mul_assoc]

private theorem product_preimage_fst_surjective
    {G : Type*} [Group G] (B C U : Subgroup G)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hn : U ≤ normalizer (C : Set G)) (hUC : U ⊔ C = B ⊔ C) :
    Function.Surjective (Prod.fst ∘ (U.comap (commutingProductHom B C hcomm)).subtype) := by
  intro b
  have hb : (b : G) ∈ U ⊔ C := hUC ▸ mem_sup_left b.property
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right U C hn] at hb
  obtain ⟨u, hu, c, hc, huc⟩ := hb
  refine ⟨⟨(b, ⟨c⁻¹, C.inv_mem hc⟩), ?_⟩, rfl⟩
  change (b : G) * c⁻¹ ∈ U
  rw [← huc, mul_inv_cancel_right]
  exact hu

private theorem product_preimage_snd_surjective
    {G : Type*} [Group G] (B C U : Subgroup G)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hn : U ≤ normalizer (B : Set G)) (hUB : U ⊔ B = B ⊔ C) :
    Function.Surjective (Prod.snd ∘ (U.comap (commutingProductHom B C hcomm)).subtype) := by
  intro c
  have hc : (c : G) ∈ U ⊔ B := hUB ▸ mem_sup_right c.property
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right U B hn] at hc
  obtain ⟨u, hu, b, hb, hub⟩ := hc
  refine ⟨⟨(⟨b⁻¹, B.inv_mem hb⟩, c), ?_⟩, rfl⟩
  change b⁻¹ * (c : G) ∈ U
  rw [hcomm _ (B.inv_mem hb) _ c.property, ← hub, mul_inv_cancel_right]
  exact hu

private theorem elementary_eight_quotient_graph
    {G : Type*} [Group G] [Finite G] (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 8) (hUV : U ≤ B ⊔ C) :
    ∃ e : B ⧸ center B ≃* C ⧸ center C,
      U.comap (commutingProductHom B C hcomm) =
        e.toMonoidHom.graph.comap
          ((QuotientGroup.mk' (center B)).prodMap (QuotientGroup.mk' (center C))) := by
  obtain ⟨hUB, hUC, hsupB, hsupC⟩ :=
    elementary_eight_intersections B C U hB hC hinter hcomm hU hUV
  have hBn : C ≤ normalizer (B : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro c hc b hb
    exact hcomm b hb c hc
  have hCn : B ≤ normalizer (C : Set G) := by
    apply le_trans ?_ (centralizer_le_normalizer _)
    intro b hb c hc
    exact (hcomm b hb c hc).symm
  apply exists_quotient_graph
    (U.comap (commutingProductHom B C hcomm)) (center B) (center C)
    (product_preimage_fst_surjective B C U hcomm
      (hUV.trans (sup_le hCn C.le_normalizer)) hsupC)
    (product_preimage_snd_surjective B C U hcomm
      (hUV.trans (sup_le B.le_normalizer hBn)) hsupB)
  · intro b
    have hh : (b : G) ∈ U ⊓ B ↔ (b : G) ∈ (center B).map B.subtype := by
      rw [hUB, intersection_eq_factor_center B C hB hinter hcomm]
    simpa [commutingProductHom] using hh
  · intro c
    have hc : B ⊓ C = (center C).map C.subtype := by
      rw [inf_comm]
      exact intersection_eq_factor_center C B hC (by simpa [inf_comm] using hinter)
        (fun c hc b hb => (hcomm b hb c hc).symm)
    have hh : (c : G) ∈ U ⊓ C ↔ (c : G) ∈ (center C).map C.subtype := by
      rw [hUC, hc]
    simpa [commutingProductHom] using hh

/-- A central product of two quaternion eights with common center of order two
has at most six elementary abelian subgroups of order eight. -/
public theorem card_elementary_eights_le_six_of_quaternion_factors
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) :
    Nat.card {U : Subgroup G // U ≤ B ⊔ C ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8} ≤ 6 := by
  classical
  let X := {U : Subgroup G // U ≤ B ⊔ C ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8}
  let m := commutingProductHom B C hcomm
  let q := (QuotientGroup.mk' (center B)).prodMap (QuotientGroup.mk' (center C))
  have hex (U : X) : ∃ e : B ⧸ center B ≃* C ⧸ center C,
      U.val.comap m = e.toMonoidHom.graph.comap q := by
    let _ : IsElementaryAbelian 2 U.val := U.property.2.1
    exact elementary_eight_quotient_graph B C U.val hB hC hinter hcomm
      U.property.2.2 U.property.1
  choose f hf using hex
  have hrange : B ⊔ C ≤ m.range := by
    apply sup_le
    · intro b hb
      exact ⟨(⟨b,hb⟩,1), by simp [m, commutingProductHom]⟩
    · intro c hc
      exact ⟨(1,⟨c,hc⟩), by simp [m, commutingProductHom]⟩
  have hinj : Function.Injective f := by
    intro U V h
    apply Subtype.ext
    have hh : U.val.comap m = V.val.comap m := by rw [hf U, hf V, h]
    have hm := congrArg (Subgroup.map m) hh
    simpa only [map_comap_eq_self (U.property.1.trans hrange),
      map_comap_eq_self (V.property.1.trans hrange)] using hm
  have hcenter : Nat.card (center B) = 2 := by
    rw [← card_subtype B (center B), ← intersection_eq_factor_center B C hB hinter hcomm]
    exact hinter
  have hBcard : Nat.card B = 8 := by
    obtain ⟨e⟩ := hB
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hquot : Nat.card (B ⧸ center B) = 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup (center B)
    rw [hBcard, hcenter] at hh
    omega
  exact (Nat.card_le_card_of_injective f hinj).trans (card_mulEquiv_le_six hquot)

/-- In particular, fewer than nine elementary eights lie in the join of two
commuting quaternion factors meeting in order two. -/
public theorem card_elementary_eights_lt_nine_of_quaternion_factors
    {G : Type*} [Group G] [Finite G] (B C : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b) :
    Nat.card {U : Subgroup G // U ≤ B ⊔ C ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 8} < 9 :=
  lt_of_le_of_lt (card_elementary_eights_le_six_of_quaternion_factors B C hB hC hinter hcomm)
    (by decide)

end Subgroup
