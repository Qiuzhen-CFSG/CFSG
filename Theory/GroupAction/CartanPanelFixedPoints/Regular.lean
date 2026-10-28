module
public import Theory.GroupAction.CartanPanelFixedPoints.Supplements

/-!
# A sharp Cartan element from regular root geometry

If R fixes the base point and acts regularly on its complement, an element
normalizing R with trivial centralizer in R fixes exactly one point of that
complement. The finite commutator bijection first constructs the fixed point;
regularity then proves uniqueness. This is the elementary rank-one action
argument used by the unitary matrix calculation.
-/

public section
namespace Theory.CartanPanel
variable {G X : Type*} [Group G] [MulAction G X]

/-- Trivial root centralizer gives exactly one fixed point off the base point. -/
theorem two_fixed_of_regular (R : Subgroup G) [Finite R]
    (α : X) (hR : R ≤ MulAction.stabilizer G α)
    (hreg : ∀ x y : X, x ≠ α → y ≠ α → ∃! r : R, (r : G) • x = y)
    (hne : ∃ x : X, x ≠ α) (t : G)
    (ht : t ∈ Subgroup.normalizer (R : Set G)) (hta : t • α = α)
    (hfree : ∀ r : R, t * r * t⁻¹ = r → r = 1) :
    ∃ β : X, β ≠ α ∧ ∀ ω : X, t • ω = ω ↔ ω = α ∨ ω = β := by
  obtain ⟨x, hx⟩ := hne
  have htx : t • x ≠ α := by
    intro he
    exact hx ((MulAction.injective t) (he.trans hta.symm))
  obtain ⟨u, hu, _⟩ := hreg x (t • x) hx htx
  obtain ⟨r, hr⟩ := root_mul_conjugate R t ht hfree u⁻¹
  have hfix : t • ((r : G)⁻¹ • x) = (r : G)⁻¹ • x := by
    apply (MulAction.injective (r : G))
    have hh : ((r : G) * t * (r : G)⁻¹) • x = x := by
      rw [hr, mul_smul, ← hu]
      exact inv_smul_smul (u : G) x
    simpa only [mul_smul, smul_inv_smul] using hh
  let β := (r : G)⁻¹ • x
  have hβ : β ≠ α := by
    intro he
    apply hx
    have hh := congrArg ((r : G) • ·) he
    exact (show x = (r : G) • α by simpa only [β, smul_inv_smul] using hh).trans
      (hR r.property)
  refine ⟨β, hβ, ?_⟩
  intro ω
  constructor
  · intro hω
    by_cases ha : ω = α
    · exact Or.inl ha
    obtain ⟨s, hs, huniq⟩ := hreg β ω hβ ha
    let s' : R := ⟨t * s * t⁻¹, (Subgroup.mem_normalizer_iff.mp ht _).mp s.property⟩
    have hs' : (s' : G) • β = ω := by
      change (t * (s : G) * t⁻¹) • β = ω
      rw [mul_smul, mul_smul, inv_smul_eq_iff.mpr hfix.symm, hs, hω]
    have he : s' = s := huniq s' hs'
    have hs1 := hfree s (congrArg Subtype.val he)
    right
    simpa only [hs1, Subgroup.coe_one, one_smul] using hs.symm
  · rintro (rfl | rfl)
    · exact hta
    · exact hfix
end Theory.CartanPanel
