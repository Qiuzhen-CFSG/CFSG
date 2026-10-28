module

public import Theory.AlgebraicGroup.BNPair.Representatives

/-! Multiplication of double cosets in a Tits system. -/

namespace Theory.AlgebraicGroup.TitsSystem

open scoped Pointwise

variable {X : Type*} [Group X]

/-- A double coset is stable under multiplication by elements of `B` on both
sides. -/
public lemma mul_mem_doubleCoset (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (w : N ⧸ (B ⊓ N).subgroupOf N) {b₁ b₂ x : X}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B)
    (hx : x ∈ (B : Set X) * representativeSet B N w * (B : Set X)) :
    b₁ * x * b₂ ∈ (B : Set X) * representativeSet B N w * (B : Set X) := by
  obtain ⟨y, hy, c, hc, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨d, hd, n, hn, rfl⟩ := Set.mem_mul.mp hy
  refine ⟨(b₁ * d) * n, ⟨b₁ * d, B.mul_mem hb₁ hd, n, hn, rfl⟩,
    c * b₂, B.mul_mem hc hb₂, ?_⟩
  simp only [mul_assoc]

/-- Multiplying the double coset of a distinguished involution by the double
coset of `w` can only produce the double cosets of `s * w` and `w`. -/
public lemma doubleCoset_mul_doubleCoset_subset_of_mem_S
    (T : TitsSystem (X := X)) {s : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N}
    (hs : s ∈ T.S) (w : T.N ⧸ (T.B ⊓ T.N).subgroupOf T.N) :
    ((T.B : Set X) * representativeSet T.B T.N s * (T.B : Set X)) *
        ((T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X)) ⊆
      ((T.B : Set X) * representativeSet T.B T.N (s * w) * (T.B : Set X)) ∪
        ((T.B : Set X) * representativeSet T.B T.N w * (T.B : Set X)) := by
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨y₁, hy₁, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hy
  obtain ⟨b₁, hb₁, ns, hns, rfl⟩ := Set.mem_mul.mp hy₁
  obtain ⟨z₁, hz₁, b₄, hb₄, rfl⟩ := Set.mem_mul.mp hz
  obtain ⟨b₃, hb₃, nw, hnw, rfl⟩ := Set.mem_mul.mp hz₁
  have hinner : ns * (b₂ * b₃) * nw ∈
      representativeSet T.B T.N s * (T.B : Set X) *
        representativeSet T.B T.N w := by
    exact ⟨ns * (b₂ * b₃),
      ⟨ns, hns, b₂ * b₃, T.B.mul_mem hb₂ hb₃, rfl⟩, nw, hnw, rfl⟩
  have hreassoc :
      (b₁ * ns * b₂) * (b₃ * nw * b₄) =
        b₁ * (ns * (b₂ * b₃) * nw) * b₄ := by
    simp only [mul_assoc]
  rw [hreassoc]
  rcases T.exchange s hs w hinner with hsw | hw
  · exact Or.inl (mul_mem_doubleCoset T.B T.N (s * w) hb₁ hb₄ hsw)
  · exact Or.inr (mul_mem_doubleCoset T.B T.N w hb₁ hb₄ hw)

/-- The double coset indexed by a quotient product is contained in the product
of the two corresponding double cosets. -/
public lemma doubleCoset_mul_subset_product (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal]
    (u v : N ⧸ (B ⊓ N).subgroupOf N) :
    (B : Set X) * representativeSet B N (u * v) * (B : Set X) ⊆
      ((B : Set X) * representativeSet B N u * (B : Set X)) *
        ((B : Set X) * representativeSet B N v * (B : Set X)) := by
  obtain ⟨nu, hnu⟩ := QuotientGroup.mk'_surjective ((B ⊓ N).subgroupOf N) u
  obtain ⟨nv, hnv⟩ := QuotientGroup.mk'_surjective ((B ⊓ N).subgroupOf N) v
  have hnuv : QuotientGroup.mk' ((B ⊓ N).subgroupOf N) (nu * nv) = u * v := by
    rw [map_mul, hnu, hnv]
  rw [B_mul_representativeSet_mul_B B N (u * v) (nu * nv) hnuv]
  intro x hx
  obtain ⟨y, hy, b₂, hb₂, rfl⟩ := Set.mem_mul.mp hx
  obtain ⟨b₁, hb₁, n, hn, rfl⟩ := Set.mem_mul.mp hy
  rw [Set.mem_singleton_iff] at hn
  subst n
  refine ⟨b₁ * (nu : X), ?_, (nv : X) * b₂, ?_, ?_⟩
  · exact ⟨b₁ * (nu : X), ⟨b₁, hb₁, nu, ⟨nu, hnu, rfl⟩, rfl⟩,
      1, B.one_mem, mul_one _⟩
  · exact ⟨(nv : X), ⟨1, B.one_mem, nv, ⟨nv, hnv, rfl⟩, one_mul (nv : X)⟩,
      b₂, hb₂, rfl⟩
  · simp only [Subgroup.coe_mul, mul_assoc]

/-- The double coset indexed by the identity quotient class is `B`. -/
public lemma doubleCoset_one_eq_B (B N : Subgroup X)
    [((B ⊓ N).subgroupOf N).Normal] :
    (B : Set X) * representativeSet B N 1 * (B : Set X) = (B : Set X) := by
  rw [B_mul_representativeSet_mul_B B N 1 1 (map_one _)]
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hx
    obtain ⟨b₁, hb₁, z, hz, rfl⟩ := Set.mem_mul.mp hy
    rw [Set.mem_singleton_iff] at hz
    subst z
    simpa only [Subgroup.coe_one, mul_one, SetLike.mem_coe] using B.mul_mem hb₁ hb
  · intro hx
    exact ⟨x, ⟨x, hx, 1, Set.mem_singleton 1, mul_one x⟩,
      1, B.one_mem, mul_one x⟩

end Theory.AlgebraicGroup.TitsSystem
