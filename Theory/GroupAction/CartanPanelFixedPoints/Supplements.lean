module
public import Theory.GroupAction.CartanPanelFixedPoints
public import Mathlib.GroupTheory.FixedPointFree
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.Group

/-!
# Sharp Cartan elements in supplied Borel supplements

If conjugation by t has trivial fixed subgroup on a finite root group R,
its commutator map is bijective. Every element of Rt is consequently an
R-conjugate of t. This places a conjugate of t in any supplied supplement
to R. When t fixes exactly two points and R fixes the base point, the
conjugate retains that base point and exactly one other fixed point.

The finite commutator argument is the elementary fixed-point-free
lemma; no complement-conjugacy or automorphism classification is required.
-/

public section
open scoped Pointwise
namespace Theory.CartanPanel
variable {G X : Type*} [Group G] [MulAction G X]

/-- A finite root group with trivial centralizer makes its torus coset one
root-conjugacy class. -/
theorem root_mul_conjugate (R : Subgroup G) [Finite R] (t : G)
    (ht : t ∈ Subgroup.normalizer (R : Set G))
    (hfree : ∀ r : R, t * r * t⁻¹ = r → r = 1) (u : R) :
    ∃ r : R, (r : G) * t * (r : G)⁻¹ = (u : G) * t := by
  let φ := R.normalizerMonoidHom ⟨t, ht⟩
  have hφ : MonoidHom.FixedPointFree φ := fun r hr => hfree r (congrArg Subtype.val hr)
  obtain ⟨r, hr⟩ := hφ.commutatorMap_surjective u
  refine ⟨r, ?_⟩
  have he : (r : G) * (t * (r : G) * t⁻¹)⁻¹ = u := by
    have he' : (r : G) / (t * (r : G) * t⁻¹) = (u : G) := congrArg Subtype.val hr
    simpa only [div_eq_mul_inv] using he'
  calc
    _ = ((r : G) * (t * (r : G) * t⁻¹)⁻¹) * t := by group
    _ = _ := by rw [he]

/-- A supplied Borel supplement contains a conjugate of any sharp torus element.
This needs no choice of a preferred complement. -/
theorem two_fixed_in_supplement (R D : Subgroup G) [Finite R]
    (α β : X) (hβ : β ≠ α) (hR : R ≤ MulAction.stabilizer G α)
    (hD : D ≤ Subgroup.normalizer (R : Set G)) (t : G)
    (ht : t ∈ Subgroup.normalizer (R : Set G)) (htsup : t ∈ R ⊔ D)
    (hfree : ∀ r : R, t * r * t⁻¹ = r → r = 1)
    (hfix : ∀ ω : X, t • ω = ω ↔ ω = α ∨ ω = β) :
    ∃ d ∈ D, ∃ γ : X, γ ≠ α ∧
      ∀ ω : X, d • ω = ω ↔ ω = α ∨ ω = γ := by
  have hprod : t ∈ (R : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hD]
    exact htsup
  obtain ⟨u, hu, d, hd, hud⟩ := hprod
  obtain ⟨r, hr⟩ := root_mul_conjugate R t ht hfree (⟨u, hu⟩ : R)⁻¹
  have hr' : (r : G) * t * (r : G)⁻¹ = d := by
    rw [hr, ← hud]
    exact inv_mul_cancel_left u d
  have hα : (r : G) • α = α := hR r.property
  refine ⟨d, hd, (r : G) • β, ?_, ?_⟩
  · intro he
    exact hβ ((MulAction.injective (r : G)) (he.trans hα.symm))
  · intro ω
    rw [← hr']
    have hh := hfix ((r : G)⁻¹ • ω)
    constructor
    · intro he
      have he' : t • ((r : G)⁻¹ • ω) = (r : G)⁻¹ • ω := by
        have he'' := congrArg ((r : G)⁻¹ • ·) he
        simpa only [mul_smul, inv_smul_smul] using he''
      simpa only [inv_smul_eq_iff, hα] using hh.mp he'
    · intro he
      have he' : (r : G)⁻¹ • ω = α ∨ (r : G)⁻¹ • ω = β := by
        simpa only [inv_smul_eq_iff, hα] using he
      have he'' := congrArg ((r : G) • ·) (hh.mpr he')
      simpa only [mul_smul, smul_inv_smul] using he''
end Theory.CartanPanel
