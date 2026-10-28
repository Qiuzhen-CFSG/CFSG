module

public import Theory.FieldTheory.QuadraticUnitSquares
public import GorensteinWalter.PGL2ConcreteSplitTorusCentralizer
public import GorensteinWalter.DihedralOddRotationCentralizer
/-!
# Semilinear actions on the full split torus

The actual split-involution centralizer in PGL₂ is a reflected cyclic
torus. Its semilinear extension acts on the torus by the coefficient map,
possibly followed by inversion. Fixing all torus squares therefore kills
the coefficient map over an odd quadratic field of prime greater than three.
Source application: Aschbacher–Smith E.2.7, printed pp.218–219.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2
private theorem semilinear_conj_inl {F : Type*} [Field F]
    (x : PGammaL2 F) (a : PGL2 F) :
    x * SemidirectProduct.inl a * x⁻¹ =
      SemidirectProduct.inl (x.left * pgl2FieldAut F x.right a * x.left⁻¹) := by
  calc
    _ = (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right) *
        SemidirectProduct.inl a *
        (SemidirectProduct.inl x.left * SemidirectProduct.inr x.right)⁻¹ :=
      congrArg (fun y : PGammaL2 F => y * SemidirectProduct.inl a * y⁻¹)
        (SemidirectProduct.inl_left_mul_inr_right x).symm
    _ = SemidirectProduct.inl x.left *
        (SemidirectProduct.inr x.right * SemidirectProduct.inl a *
          (SemidirectProduct.inr x.right)⁻¹) * (SemidirectProduct.inl x.left)⁻¹ := by group
    _ = _ := by rw [← map_inv, ← SemidirectProduct.inl_aut, ← map_mul, ← map_inv, ← map_mul]

/-- A semilinear element centralizing the canonical split involution acts
on the full split torus by its coefficient automorphism or its inverse. -/
theorem split_involution_centralizer_torus_action
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (x : PGammaL2 F)
    (hx : Commute x (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1)))) :
    (∀ a : Fˣ, x * SemidirectProduct.inl (pGammaL2FullSplitTorus F a) * x⁻¹ =
      SemidirectProduct.inl (pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a))) ∨
    (∀ a : Fˣ, x * SemidirectProduct.inl (pGammaL2FullSplitTorus F a) * x⁻¹ =
      SemidirectProduct.inl ((pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a))⁻¹)) := by
  have hfield : pgl2FieldAut F x.right (pGammaL2FullSplitTorus F (-1)) =
      pGammaL2FullSplitTorus F (-1) := by
    rw [pGammaL2FullSplitTorus_map_field]
    congr 1
    apply Units.ext
    simp
  have hleft : x.left ∈ centralizer ({pGammaL2FullSplitTorus F (-1)} : Set (PGL2 F)) := by
    apply mem_centralizer_singleton_iff.mpr
    have hh := congrArg SemidirectProduct.left hx.eq
    simpa only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, MulAut.one_apply, hfield] using hh
  obtain ⟨w, hcyc, _, _, _, hw, hw2, hwi, hc, _⟩ := pgl2_fullSplitTorus_centralizer_data F hF
  rw [hc] at hleft
  obtain ⟨u, hu, he | he⟩ := (mem_sup_zpowers_of_involution_inverts hw hw2 hwi).mp hleft
  · left
    intro a
    rw [semilinear_conj_inl, pGammaL2FullSplitTorus_map_field, he]
    congr 1
    obtain ⟨b, rfl⟩ := hu
    rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    simp [mul_comm, mul_left_comm]
  · right
    intro a
    rw [semilinear_conj_inl, pGammaL2FullSplitTorus_map_field, he]
    congr 1
    calc
      (u * w) * pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a) * (u * w)⁻¹ =
          u * (w * pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a) * w⁻¹) * u⁻¹ := by group
      _ = u * (pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a))⁻¹ * u⁻¹ := by
        rw [hwi _ ⟨_, rfl⟩]
      _ = (pGammaL2FullSplitTorus F (Units.map x.right.toRingHom a))⁻¹ := by
        obtain ⟨b, rfl⟩ := hu
        simp only [← map_inv, ← map_mul]
        congr 1
        simp [mul_comm, mul_left_comm]

/-- Fixing all squares of the full split torus excludes a nontrivial field coordinate. -/
theorem field_eq_one_of_centralizes_split_torus_squares
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p ^ 2) (hp : 3 < p)
    (x : PGammaL2 F)
    (hx : Commute x (SemidirectProduct.inl (pGammaL2FullSplitTorus F (-1))))
    (hs : ∀ a : Fˣ, Commute x ((SemidirectProduct.inl (pGammaL2FullSplitTorus F a) : PGammaL2 F) ^ 2)) :
    x.right = 1 := by
  apply FiniteField.ringAut_eq_one_of_unit_squares_fixed_or_inverted hF hp x.right
  obtain ha | ha := split_involution_centralizer_torus_action
    ⟨p, 2, Fact.out, ho, by decide, hF⟩ x hx
  · left
    intro a
    have hh := ha (a ^ 2)
    rw [map_pow, map_pow] at hh
    have hc : x * (SemidirectProduct.inl (pGammaL2FullSplitTorus F a)) ^ 2 * x⁻¹ =
        (SemidirectProduct.inl (pGammaL2FullSplitTorus F a)) ^ 2 :=
      (mul_inv_eq_iff_eq_mul).mpr (hs a).eq
    rw [hc, ← map_pow, ← map_pow] at hh
    exact (pGammaL2FullSplitTorus_injective F (SemidirectProduct.inl_injective hh)).symm
  · right
    intro a
    have hh := ha (a ^ 2)
    rw [map_pow, map_pow] at hh
    have hc : x * (SemidirectProduct.inl (pGammaL2FullSplitTorus F a)) ^ 2 * x⁻¹ =
        (SemidirectProduct.inl (pGammaL2FullSplitTorus F a)) ^ 2 :=
      (mul_inv_eq_iff_eq_mul).mpr (hs a).eq
    rw [hc, ← map_pow, ← map_pow, ← map_inv] at hh
    have he := pGammaL2FullSplitTorus_injective F (SemidirectProduct.inl_injective hh)
    simpa only [inv_inv] using (congrArg Inv.inv he).symm
end Theory.PSL2
