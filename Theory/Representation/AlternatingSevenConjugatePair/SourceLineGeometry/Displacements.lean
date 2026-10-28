module

public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry.Stabilizer
public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry.Planes

/-!
# Displacement inclusions for the two moved planes

Two cubic norms produce the marked vector as a mixed displacement. The first
cubic commutes with the two relevant swaps. For the second cubic, seven further
norms give a sum of two mixed displacements. All identities hold on the supplied
pair; the finite checks here are only equalities and coset membership in S₇.

This proves the containment needed in Aschbacher–Smith 14.4.11 without the
printed final equality involving an element of the Sylow stabilizer.
-/

@[expose] public section
namespace Representation.AlternatingSevenConjugatePair.SourceLineGeometry
open BinaryOffender
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

local instance decidableThreeCycleDisplacements (t : S7) : Decidable t.IsThreeCycle :=
  inferInstanceAs (Decidable (t.cycleType = {3}))

private def u : S7 := Equiv.swap 1 2
private def v : S7 := Equiv.swap 5 6

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

def mixed (ρ : Representation (ZMod 2) S7 V) (t w : S7) (x : V) : V :=
  ρ w (ρ t x - x) - (ρ t x - x)

private theorem mixed_mem (ρ : Representation (ZMod 2) S7 V) (t w : S7)
    (hw : w ∈ B8) (x : V) :
    mixed ρ t w x ∈ subspaceCommutator ρ (displacement ρ t) B8 := by
  apply Submodule.subset_span
  exact ⟨w, hw, ρ t x - x, ⟨x, rfl⟩, rfl⟩

private theorem mixed_commute (ρ : Representation (ZMod 2) S7 V)
    (t w r : S7) (ht : t*r=r*t) (hw : w*r=r*w) (x : V) :
    mixed ρ t w (ρ r x) = ρ r (mixed ρ t w x) := by
  have hc (z : V) : ρ t (ρ r z) = ρ r (ρ t z) := by
    simp only [← Module.End.mul_apply, ← map_mul, ht]
  have hd (z : V) : ρ w (ρ r z) = ρ r (ρ w z) := by
    simp only [← Module.End.mul_apply, ← map_mul, hw]
  simp only [mixed, hc, ← map_sub, hd]

private theorem a_mem : a ∈ B8 := Subgroup.subset_closure (Or.inl rfl)
private theorem b_mem : b ∈ B8 := Subgroup.subset_closure (Or.inr (Or.inl rfl))

variable [FiniteDimensional (ZMod 2) V]

private theorem seed_mixed (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s)
    (t : S7) (ht : t = a ∨ t = c) :
    mixed D.representation t b (D.representation (u*v) s) = s := by
  have hn := orbit_norm D s standardTwo hs (t*u) v (t*u*v) (u*v)
    (by rcases ht with rfl | rfl <;> decide)
    (by rw [inv_mul_cancel]; exact standardTwo.one_mem)
    (by rcases ht with rfl | rfl <;> decide)
  have hb := orbit_norm D s standardTwo hs (b*v) 1 (b*v) v
    (by decide) (by simp) (by decide)
  have he : D.representation t (D.representation (u*v) s) -
      D.representation (u*v) s = D.representation v s := by
    have hh := eq_neg_of_add_eq_zero_right
      (show D.representation v s + (D.representation (t*u*v) s +
        D.representation (u*v) s) = 0 by simpa only [add_assoc] using hn)
    simpa only [sub_eq_add_neg, ZModModule.neg_eq_self,
      ← Module.End.mul_apply, ← map_mul, mul_assoc] using hh
  rw [mixed, he]
  have hh := eq_neg_of_add_eq_zero_right
    (show s + (D.representation (b*v) s + D.representation v s) = 0 by
      simpa only [map_one, Module.End.one_apply, add_assoc] using hb)
  simpa only [sub_eq_add_neg, ZModModule.neg_eq_self,
    ← Module.End.mul_apply, ← map_mul] using hh

/-- The first moved plane is contained in the commutator of the first swap displacement. -/
theorem first_moved_le (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    movedLine D.representation s cubicOvergroup ≤
      subspaceCommutator D.representation (displacement D.representation a) B8 := by
  rw [first_moved_eq]
  apply Submodule.span_le.mpr
  intro x hx
  have he := seed_mixed D s hs a (Or.inl rfl)
  rcases (show x = s ∨ x = D.representation firstCubic s from hx) with hx | hx
  · rw [hx]
    exact he ▸ mixed_mem D.representation a b b_mem (D.representation (u*v) s)
  · rw [hx]
    have hh := mixed_mem D.representation a b b_mem
      (D.representation firstCubic (D.representation (u*v) s))
    rwa [mixed_commute D.representation a b firstCubic (by decide) (by decide), he] at hh

private def p0 : S7 := (1 : S7)
private def p1 : S7 := Equiv.swap 1 2
private def p2 : S7 := Equiv.swap 3 4
private def p4 : S7 := Equiv.swap 0 1 * Equiv.swap 1 2
private def p7 : S7 := Equiv.swap 2 3 * Equiv.swap 3 4
private def p8 : S7 := Equiv.swap 3 4 * Equiv.swap 5 6
private def p14 : S7 := Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 6
private def p21 : S7 := Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 3 4 * Equiv.swap 5 6
private def p24 : S7 := Equiv.swap 1 3 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 5 6
private def p33 : S7 := Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 5 6
private def p38 : S7 := Equiv.swap 1 3 * Equiv.swap 2 3 * Equiv.swap 3 5 * Equiv.swap 4 5 * Equiv.swap 5 6
private def p48 : S7 := Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 2 3 * Equiv.swap 3 5 * Equiv.swap 4 5 * Equiv.swap 5 6
private def p56 : S7 := Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6
private def p71 : S7 := Equiv.swap 0 1 * Equiv.swap 1 3 * Equiv.swap 3 4 * Equiv.swap 4 5 * Equiv.swap 5 6
private def p86 : S7 := Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 2 4 * Equiv.swap 3 5 * Equiv.swap 5 6

private theorem second_mixed (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    mixed D.representation c a (D.representation p14 s) +
      mixed D.representation c b (D.representation p24 s) =
        D.representation secondCubic s := by
  have hP := syntheme_fixes D s hs
  have he (p q : S7) (h : q⁻¹*p ∈ synthemeOvergroup) :
      D.representation p s = D.representation q s :=
    orbit_eq_of_coset D.representation s synthemeOvergroup hP p q h
  have h0 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 0 1 * Equiv.swap 1 2) p0 p4 p1 (by decide) (by decide) (by decide)
  have h25 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 2 3 * Equiv.swap 3 4) p0 p7 p2 (by decide) (by decide) (by decide)
  have h48 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 0 4 * Equiv.swap 4 6) p1 p71 p48 (by decide) (by decide) (by decide)
  have h91 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 1 3 * Equiv.swap 3 6) p2 p56 p86 (by decide) (by decide) (by decide)
  have h163 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 1 4 * Equiv.swap 4 6) p4 p56 p38 (by decide) (by decide) (by decide)
  have h280 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 0 1 * Equiv.swap 1 2) p8 p21 p14 (by decide) (by decide) (by decide)
  have h290 := orbit_norm D s synthemeOvergroup hP
    (Equiv.swap 0 3 * Equiv.swap 3 5) p8 p71 p86 (by decide) (by decide) (by decide)
  have hsum : D.representation p7 s +
      (D.representation p21 s + D.representation p14 s +
        D.representation p48 s + D.representation p38 s) = 0 := by
    calc
      _ = (D.representation p0 s + D.representation p4 s + D.representation p1 s) +
        (D.representation p0 s + D.representation p7 s + D.representation p2 s) +
        (D.representation p1 s + D.representation p71 s + D.representation p48 s) +
        (D.representation p2 s + D.representation p56 s + D.representation p86 s) +
        (D.representation p4 s + D.representation p56 s + D.representation p38 s) +
        (D.representation p8 s + D.representation p21 s + D.representation p14 s) +
        (D.representation p8 s + D.representation p71 s + D.representation p86 s) := by
          abel_nf
          simp [← Int.cast_smul_eq_zsmul (ZMod 2)]
      _ = 0 := by rw [h0, h25, h48, h91, h163, h280, h290]; simp
  have hm : mixed D.representation c a (D.representation p14 s) +
      mixed D.representation c b (D.representation p24 s) =
      D.representation p21 s + D.representation p14 s +
        D.representation p48 s + D.representation p38 s := by
    simp only [mixed, map_sub, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]
    rw [he (a*c*p14) p33 (by decide), he (a*p14) p24 (by decide),
      he (c*p14) p21 (by decide), he (b*c*p24) p48 (by decide),
      he (b*p24) p38 (by decide), he (c*p24) p33 (by decide)]
    simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
    abel_nf
    simp [← Int.cast_smul_eq_zsmul (ZMod 2)]
  rw [hm]
  simpa only [p7, secondCubic, ZModModule.neg_eq_self] using
    eq_neg_of_add_eq_zero_right hsum

/-- The second moved plane lies in the commutator of the distinguished swap displacement. -/
theorem second_moved_le (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    movedLine D.representation s duadOvergroup ≤
      subspaceCommutator D.representation (displacement D.representation c) B8 := by
  rw [second_moved_eq D s hs]
  apply Submodule.span_le.mpr
  intro x hx
  rcases (show x = s ∨ x = D.representation secondCubic s from hx) with hx | hx
  · rw [hx]
    exact seed_mixed D s hs c (Or.inr rfl) ▸
      mixed_mem D.representation c b b_mem (D.representation (u*v) s)
  · rw [hx]
    exact second_mixed D s hs ▸ Submodule.add_mem _
      (mixed_mem D.representation c a a_mem (D.representation p14 s))
      (mixed_mem D.representation c b b_mem (D.representation p24 s))

end Representation.AlternatingSevenConjugatePair.SourceLineGeometry
