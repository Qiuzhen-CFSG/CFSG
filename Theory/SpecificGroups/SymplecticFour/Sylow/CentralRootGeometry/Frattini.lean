module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.Frattini.BinarySquares
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
/-!
# The symplectic Sylow Frattini subgroup

All squares lie in the central two-root plane. For a field with more than two
elements, the squares with first parameters 1 and a scalar outside {0,1}
span that plane. The finite two-group square-generation theorem identifies Φ.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

omit [CharP F 2] in
private theorem exists_scalar {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 := by
  have hc : 2 < Nat.card F := by
    rw [hF]
    exact (by norm_num : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) hn
  let := Fintype.ofFinite Fˣ
  have : Nontrivial Fˣ := Fintype.one_lt_card_iff_nontrivial.mp (by
    rw [← Nat.card_eq_fintype_card, Nat.card_units]
    omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  exact ⟨a, a.ne_zero, fun h => ha (Units.ext h)⟩

theorem frattini_eq_center {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    frattini (unipotent (F := F)) = center (unipotent (F := F)) := by
  rw [(isPGroup_unipotent hF).frattini_eq_closure_squares]
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro _ ⟨x,rfl⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    change (element b u w v)^2 ∈ center (unipotent (F := F))
    rw [element_square]
    exact theta_mem_center _ _
  · intro x hx
    rw [← theta_range] at hx
    obtain ⟨⟨s,t⟩,rfl⟩ := hx
    obtain ⟨a,ha0,ha1⟩ := exists_scalar hF hn
    have hd : a^2+a ≠ 0 := by
      rw [pow_two, ← mul_add_one]
      exact mul_ne_zero ha0 (fun h => ha1 (by simpa using (CharTwo.add_eq_zero.mp h)))
    let y : F := (s.toAdd+t.toAdd)/(a^2+a)
    let z : F := t.toAdd+a*y
    have hy : (a^2+a)*y = s.toAdd+t.toAdd := mul_div_cancel₀ _ hd
    have hz : z+a^2*y = s.toAdd := by
      calc
        z+a^2*y = (a^2+a)*y+t.toAdd := by dsimp [z]; ring
        _ = s.toAdd := by rw [hy, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have ht : z+a*y = t.toAdd := by
      dsimp [z]
      rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
    have he : thetaHom (s,t) = (element 1 0 0 z)^2 * (element a 0 0 y)^2 := by
      rw [element_square, element_square, theta_add]
      change theta s.toAdd t.toAdd = _
      simp only [one_pow, one_mul, hz, ht]
    rw [he]
    exact mul_mem (subset_closure ⟨element 1 0 0 z,rfl⟩)
      (subset_closure ⟨element a 0 0 y,rfl⟩)

theorem embedded_frattini_eq_center {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    (frattini (unipotent (F := F))).map (unipotent (F := F)).subtype =
      (center (unipotent (F := F))).map (unipotent (F := F)).subtype := by
  rw [frattini_eq_center hF hn]
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
