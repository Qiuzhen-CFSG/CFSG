module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Source
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Canonical

/-!
# Transporting the cyclic centralizer factors

A change of the SL₂ subgroup by an element normalizing B transports both
cyclic factors and their generation equality. Once such a change identifies
the SL₂ with the canonical centralizer residual, its intersection with B is
normalized by N_S(B).

The concrete existence of that change is a separate hypothesis here, not a
consequence of the arbitrary A.3.15 witness. Alternatively, the concrete
model calculation can establish the canonical decomposition directly.

Source: Aschbacher–Smith, proof of 1.3.4, printed pp. 510–511.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J]

/-- The two cyclic factors commute, so B is abelian. -/
theorem CyclicDecomposition.isMulCommutative {B K : Subgroup J} (h : CyclicDecomposition B K) : IsMulCommutative B := by
  let _ := h.left_cyclic
  let _ := h.right_cyclic
  have hc : B ⊓ centralizer (K : Set J) ≤ centralizer (B ⊓ K : Set J) :=
    inf_le_right.trans (centralizer_le inf_le_right)
  rw [← h.generated]
  apply le_centralizer_iff_isMulCommutative.mp
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le (B ⊓ K).le_centralizer hc)
  · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hc)
      (B ⊓ centralizer (K : Set J)).le_centralizer)

/-- The join factorization is the actual setwise product of the two factors. -/
theorem CyclicDecomposition.exists_factors {B K : Subgroup J} (h : CyclicDecomposition B K) {b : J} (hb : b ∈ B) :
    ∃ a ∈ B ⊓ K, ∃ c ∈ B ⊓ centralizer (K : Set J), a * c = b := by
  have hc : B ⊓ centralizer (K : Set J) ≤ centralizer (B ⊓ K : Set J) :=
    inf_le_right.trans (centralizer_le inf_le_right)
  have he := coe_mul_of_right_le_normalizer_left (B ⊓ K)
    (B ⊓ centralizer (K : Set J)) (hc.trans (centralizer_le_normalizer _))
  rw [← h.generated, ← SetLike.mem_coe, he] at hb
  exact hb

/-- An element of K inverting the left factor normalizes B and fixes its centralizer factor. -/
theorem CyclicDecomposition.inverter_mem_normalizer [Finite J] {B K : Subgroup J} (h : CyclicDecomposition B K)
    {t : J} (htK : t ∈ K) (hi : ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹) :
    t ∈ normalizer B := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rw [map_le_iff_le_comap, ← h.generated]
    apply sup_le
    · intro b hb
      change t * b * t⁻¹ ∈ (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set J))
      rw [hi b hb]
      exact (show B ⊓ K ≤ (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set J)) from
        le_sup_left) ((B ⊓ K).inv_mem hb)
    · intro c hc
      change t * c * t⁻¹ ∈ (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set J))
      have he : t * c = c * t := hc.2 t htK
      rw [he, mul_inv_cancel_right]
      exact (show B ⊓ centralizer (K : Set J) ≤
        (B ⊓ K) ⊔ (B ⊓ centralizer (K : Set J)) from le_sup_right) hc
  · rw [card_map_of_injective (MulAut.conj t).injective]

private theorem centralizer_map_equiv (K : Subgroup J) (f : J ≃* J) :
    (centralizer (K : Set J)).map f.toMonoidHom =
      centralizer (K.map f.toMonoidHom : Set J) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

theorem CyclicDecomposition.map {B K : Subgroup J} (h : CyclicDecomposition B K)
    (f : J ≃* J) : CyclicDecomposition (B.map f.toMonoidHom) (K.map f.toMonoidHom) := by
  have hl : IsCyclic ((B ⊓ K).map f.toMonoidHom) := by
    let _ := h.left_cyclic
    exact isCyclic_of_surjective ((f.subgroupMap (B ⊓ K)).toMonoidHom)
      (f.subgroupMap (B ⊓ K)).surjective
  have hr : IsCyclic ((B ⊓ centralizer (K : Set J)).map f.toMonoidHom) := by
    let _ := h.right_cyclic
    exact isCyclic_of_surjective ((f.subgroupMap (B ⊓ centralizer (K : Set J))).toMonoidHom)
      (f.subgroupMap (B ⊓ centralizer (K : Set J))).surjective
  rw [map_inf _ _ _ f.injective] at hl
  rw [map_inf _ _ _ f.injective, centralizer_map_equiv] at hr
  refine ⟨hl, hr, ?_⟩
  have hgen := congrArg (Subgroup.map f.toMonoidHom) h.generated
  simpa only [Subgroup.map_sup, map_inf _ _ f.toMonoidHom f.injective, centralizer_map_equiv] using hgen

theorem CyclicDecomposition.of_conjugate {B K R : Subgroup J}
    (h : CyclicDecomposition B K) {g : J} (hg : g ∈ normalizer B)
    (hR : K.map (MulAut.conj g).toMonoidHom = R) : CyclicDecomposition B R := by
  have hb : B.map (MulAut.conj g).toMonoidHom = B :=
    mem_normalizer_iff_map_conj_eq.mp hg
  simpa only [hb, hR] using h.map (MulAut.conj g)

theorem CyclicDecomposition.internal {B K : Subgroup J} (h : CyclicDecomposition B K) :
    IsCyclic (K.subgroupOf B) ∧ IsCyclic ((centralizer (K : Set J)).subgroupOf B) ∧
      K.subgroupOf B ⊔ (centralizer (K : Set J)).subgroupOf B = ⊤ := by
  have hl : IsCyclic ((B ⊓ K).subgroupOf B) := by
    let _ := h.left_cyclic
    exact isCyclic_of_injective (subgroupOfEquivOfLe (show B ⊓ K ≤ B from inf_le_left)).toMonoidHom
      (subgroupOfEquivOfLe (show B ⊓ K ≤ B from inf_le_left)).injective
  have hr : IsCyclic ((B ⊓ centralizer (K : Set J)).subgroupOf B) := by
    let _ := h.right_cyclic
    exact isCyclic_of_injective
      (subgroupOfEquivOfLe (show B ⊓ centralizer (K : Set J) ≤ B from inf_le_left)).toMonoidHom
      (subgroupOfEquivOfLe (show B ⊓ centralizer (K : Set J) ≤ B from inf_le_left)).injective
  rw [inf_subgroupOf_left] at hl hr
  refine ⟨hl, hr, ?_⟩
  apply map_injective B.subtype_injective
  simpa only [Subgroup.map_sup, subgroupOf_map_subtype, ← MonoidHom.range_eq_map, range_subtype, inf_comm] using h.generated

/-- The canonical decomposition gives the required invariant cyclic factor.
Its concrete model-theoretic premise must still be established. -/
theorem factorization_of_canonical_decomposition {D B : Subgroup J} (S : Subgroup J) [D.Normal]
    (h : CyclicDecomposition B (canonicalResidual D S)) :
    ∃ A C : Subgroup B, IsCyclic A ∧ IsCyclic C ∧ A ⊔ C = ⊤ ∧
      S ⊓ normalizer B ≤ normalizer (A.map B.subtype) := by
  obtain ⟨hl, hr, hg⟩ := h.internal
  exact ⟨canonicalFactor D S B, (centralizer (canonicalResidual D S : Set J)).subgroupOf B,
    hl, hr, hg, canonicalFactor_normalized D S B⟩

/-- The cyclic case needs no choice of an SL₂ subgroup. -/
theorem factorization_of_cyclic {B : Subgroup J} (S : Subgroup J) (h : IsCyclic B) :
    ∃ A C : Subgroup B, IsCyclic A ∧ IsCyclic C ∧ A ⊔ C = ⊤ ∧
      S ⊓ normalizer B ≤ normalizer (A.map B.subtype) := by
  let _ := h
  refine ⟨⊥, ⊤, inferInstance, inferInstance, bot_sup_eq _, ?_⟩
  rw [Subgroup.map_bot]
  exact le_normalizer_of_normal

/-- Conditional assembly from the concrete change of SL₂ subgroup. -/
theorem factorization_of_conjugate [Finite J] {D B K : Subgroup J}
    (S : Subgroup J) [D.Normal] (h : CyclicDecomposition B K)
    (hc : ∃ g ∈ normalizer B,
      K.map (MulAut.conj g).toMonoidHom = canonicalResidual D S) :
    ∃ A C : Subgroup B, IsCyclic A ∧ IsCyclic C ∧ A ⊔ C = ⊤ ∧
      S ⊓ normalizer B ≤ normalizer (A.map B.subtype) := by
  obtain ⟨g, hg, he⟩ := hc
  exact factorization_of_canonical_decomposition S (h.of_conjugate hg he)

/-- The source inverter is an actual element of N_S(B), with its original action. -/
theorem CaseThree.exists_normalizing_inverter [Finite J]
    {D B S K : Subgroup J} {q : ℕ} [Fact q.Prime] {δ ε : Sign}
    (h : CaseThree D B S K q δ ε) :
    ∃ t ∈ S ⊓ normalizer B, t ∈ K ∧
      ∀ b ∈ B ⊓ K, t * b * t⁻¹ = b⁻¹ := by
  obtain ⟨t, ht, hi⟩ := h.inverted
  exact ⟨t, ⟨ht.1, h.toCyclicDecomposition.inverter_mem_normalizer ht.2 hi⟩, ht.2, hi⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
