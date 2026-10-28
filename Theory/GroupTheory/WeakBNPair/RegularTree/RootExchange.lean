module
public import Theory.AlgebraicGroup.BNPair.SimpleLiftCoverage

/-!
# Root factorization gives the DGS exchange inclusion

Factor the Borel as `B₀ R`, where the reflection normalizes `B₀`.
If `R^n ≤ B`, moving the root factor past `n` gives the upper cell.
Otherwise the opposite half-apartment gives `R^(tn) ≤ B`. Insert the
reflection twice and use the two-cell decomposition of the actual endpoint
subgroup; absorption at `tn` then gives the two required cells.

This is the algebra in DGS, *Groups and Graphs* (1985), Part II, (3.7),
printed p.80. The root-containment alternative is a geometric input, not
an assumed BN exchange law or an assumed Tits system.
-/

@[expose] public section
namespace Theory.GroupTheory.WeakBNPair.RegularTree
open Theory.AlgebraicGroup.BruhatGeneration
variable {X : Type*} [Group X]

/-- The root factor moves to the right when its conjugate lies in the Borel. -/
theorem root_absorption (B B₀ R : Subgroup X) (t n : X)
    (hfactor : ∀ b ∈ B, ∃ b₀ ∈ B₀, ∃ r ∈ R, b = b₀ * r)
    (hconj : ∀ b₀ ∈ B₀, t * b₀ * t⁻¹ ∈ B)
    (hroot : ∀ r ∈ R, n⁻¹ * r * n ∈ B) :
    ∀ b ∈ B, ∃ a c, a ∈ B ∧ c ∈ B ∧ t * b * n = a * (t * n) * c := by
  intro b hb
  obtain ⟨b₀, hb₀, r, hr, rfl⟩ := hfactor b hb
  exact ⟨t * b₀ * t⁻¹, n⁻¹ * r * n, hconj b₀ hb₀, hroot r hr, by group⟩

/-- The two-cell endpoint and the two possible root signs prove full local
exchange, including the case in which multiplication folds the apartment. -/
theorem root_exchange (B B₀ R P : Subgroup X) (t n : X)
    (hBP : B ≤ P) (htP : t ∈ P) (hsquare : t * t ∈ B)
    (hcells : ∀ x ∈ P, x ∈ B ∨ ∃ a c, a ∈ B ∧ c ∈ B ∧ x = a * t * c)
    (hfactor : ∀ b ∈ B, ∃ b₀ ∈ B₀, ∃ r ∈ R, b = b₀ * r)
    (hconj : ∀ b₀ ∈ B₀, t * b₀ * t⁻¹ ∈ B)
    (hsign : (∀ r ∈ R, n⁻¹ * r * n ∈ B) ∨
      (∀ r ∈ R, (t * n)⁻¹ * r * (t * n) ∈ B)) :
    ∀ b ∈ B, ∃ a c, a ∈ B ∧ c ∈ B ∧
      (t * b * n = a * (t * n) * c ∨ t * b * n = a * n * c) := by
  intro b hb
  rcases hsign with hpos | hneg
  · obtain ⟨a, c, ha, hc, he⟩ := root_absorption B B₀ R t n hfactor hconj hpos b hb
    exact ⟨a, c, ha, hc, Or.inl he⟩
  · let z := t * (b * (t * t)⁻¹) * t
    have hzP : z ∈ P :=
      P.mul_mem (P.mul_mem htP (hBP (B.mul_mem hb (B.inv_mem hsquare)))) htP
    have hz : t * b * n = z * (t * n) := by dsimp [z]; group
    rcases hcells z hzP with hzB | ⟨a, c, ha, hc, he⟩
    · exact ⟨z, 1, hzB, B.one_mem, Or.inl (by simpa only [mul_one] using hz)⟩
    · obtain ⟨d, e, hd, heB, hde⟩ :=
        root_absorption B B₀ R t (t * n) hfactor hconj hneg c hc
      refine ⟨a * d * (t * t), e, B.mul_mem (B.mul_mem ha hd) hsquare,
        heB, Or.inr ?_⟩
      calc
        t * b * n = (a * t * c) * (t * n) := by rw [hz, he]
        _ = a * (t * c * (t * n)) := by simp only [mul_assoc]
        _ = a * (d * (t * (t * n)) * e) := by rw [hde]
        _ = a * d * (t * t) * n * e := by simp only [mul_assoc]

/-- Apply the root calculation at each of the marked endpoints. -/
theorem simpleLiftExchange_of_roots (B N : Subgroup X) {I : Type*}
    (P B₀ R : I → Subgroup X) (t : I → X)
    (hBP : ∀ i, B ≤ P i) (htP : ∀ i, t i ∈ P i)
    (hsquare : ∀ i, t i * t i ∈ B)
    (hcells : ∀ i x, x ∈ P i →
      x ∈ B ∨ ∃ a c, a ∈ B ∧ c ∈ B ∧ x = a * t i * c)
    (hfactor : ∀ i b, b ∈ B → ∃ b₀ ∈ B₀ i, ∃ r ∈ R i, b = b₀ * r)
    (hconj : ∀ i b₀, b₀ ∈ B₀ i → t i * b₀ * (t i)⁻¹ ∈ B)
    (hsign : ∀ i n, n ∈ N →
      (∀ r ∈ R i, n⁻¹ * r * n ∈ B) ∨
      (∀ r ∈ R i, (t i * n)⁻¹ * r * (t i * n) ∈ B)) :
    SimpleLiftExchange B N (Set.range t) := by
  rintro s ⟨i, rfl⟩ b hb n hn
  exact root_exchange B (B₀ i) (R i) (P i) (t i) n (hBP i) (htP i)
    (hsquare i) (hcells i) (hfactor i) (hconj i) (hsign i n hn) b hb

end Theory.GroupTheory.WeakBNPair.RegularTree
