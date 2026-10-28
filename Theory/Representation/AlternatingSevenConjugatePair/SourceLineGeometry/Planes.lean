module

public import Theory.Representation.AlternatingSevenConjugatePair.SourceLineGeometry.Basic

/-!
# The two residual moved planes

The cubic residual is cyclic. The duad residual has three cosets modulo its
Sylow intersection. In either case the orbit of the marked vector consists of
`s`, `r s`, and `s + r s`. The cubic norm puts both generators in the actual
commutator subspace, and fixed-point-freeness proves their independence.

Source: Aschbacher–Smith, Lemma 14.4.11, printed p.1011/PDF p.1028.
-/

@[expose] public section
namespace Representation.AlternatingSevenConjugatePair.SourceLineGeometry
open BinaryOffender Subgroup
open Theory.SpecificGroups.SymmetricSeven.LocalResidualRecognition
open Theory.SpecificGroups.SymmetricSeven.LocalResidualModels

local instance decidableThreeCyclePlanes (t : S7) : Decidable t.IsThreeCycle :=
  inferInstanceAs (Decidable (t.cycleType = {3}))
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The plane used below has two explicit orbit generators. -/
def cubicPlane (ρ : Representation (ZMod 2) S7 V) (s : V) (r : S7) :
    Submodule (ZMod 2) V := Submodule.span (ZMod 2) {s, ρ r s}

private theorem cubic_square (D : Pair V) (s : V) (r : S7) (hr : r.IsThreeCycle) :
    D.representation (r * r) s = s + D.representation r s := by
  have h := eq_neg_of_add_eq_zero_right (threeCycle_norm D r hr s)
  simpa only [ZModModule.neg_eq_self] using h

private theorem cubicPlane_le_commutator (D : Pair V) (s : V) (r : S7)
    (hr : r.IsThreeCycle) (R : Subgroup S7) (hR : r ∈ R) :
    cubicPlane D.representation s r ≤ subspaceCommutator D.representation (line s) R := by
  let M := subspaceCommutator D.representation (line s) R
  have hd (g : S7) (hg : g ∈ R) : D.representation g s - s ∈ M :=
    Submodule.subset_span ⟨g, hg, s, Submodule.subset_span (Set.mem_singleton s), rfl⟩
  have he : (D.representation r s - s) + (D.representation (r*r) s - s) = s := by
    rw [cubic_square D s r hr]
    simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
    calc
      _ = (D.representation r s + D.representation r s) + (s+s) + s := by abel
      _ = s := by rw [ZModModule.add_self, ZModModule.add_self, zero_add, zero_add]
  have hsM : s ∈ M := he ▸ M.add_mem (hd r hR) (hd (r*r) (R.mul_mem hR hR))
  have hrM : D.representation r s ∈ M := by
    simpa only [sub_add_cancel] using M.add_mem (hd r hR) hsM
  apply Submodule.span_le.mpr
  intro v hv
  rcases (show v = s ∨ v = D.representation r s from hv) with rfl | rfl
  · exact hsM
  · exact hrM

omit [FiniteDimensional (ZMod 2) V] in
private theorem commutator_le_cubicPlane (ρ : Representation (ZMod 2) S7 V)
    (s : V) (r : S7) (R : Subgroup S7)
    (hR : ∀ g ∈ R, ρ g s ∈ cubicPlane ρ s r) :
    subspaceCommutator ρ (line s) R ≤ cubicPlane ρ s r := by
  apply Submodule.span_le.mpr
  rintro v ⟨g, hg, w, hw, rfl⟩
  obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, ← smul_sub]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hR g hg)
    (Submodule.subset_span (Or.inl rfl)))

private theorem cubic_power_mem (D : Pair V) (s : V) (r : S7)
    (hr : r.IsThreeCycle) (n : ℕ) :
    D.representation (r^n) s ∈ cubicPlane D.representation s r := by
  rw [← pow_mod_orderOf r n, hr.orderOf]
  have hn : n % 3 < 3 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 3
  · simp only [pow_zero, map_one, Module.End.one_apply]
    exact Submodule.subset_span (Or.inl rfl)
  · rw [pow_one]
    exact Submodule.subset_span (Or.inr rfl)
  · simpa only [pow_two, cubic_square D s r hr] using
      (cubicPlane D.representation s r).add_mem
        (Submodule.subset_span (Or.inl rfl)) (Submodule.subset_span (Or.inr rfl))

/-- The embedded cubic residual is the literal cycle on `{0,1,6}`. -/
theorem first_residual : residual cubicOvergroup = zpowers firstCubic := by
  rw [residual, residual_cubicOvergroup, cubicResidual7, MonoidHom.map_zpowers]
  congr 1
  decide

private theorem secondCubic_mem : secondCubic ∈ residual duadOvergroup := by
  rw [residual, residual_duadOvergroup]
  let x : A := ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by decide⟩
  exact ⟨duadHom x, ⟨x, rfl⟩, by decide⟩

private theorem duad_cosets : ∀ x : A, ∃ n : Fin 3,
    (secondCubic ^ n.val)⁻¹ * liftSix (duadHom x) ∈ standardTwo := by decide +kernel

/-- The first moved space, with the actual embedded residual and action. -/
theorem first_moved_eq (D : Pair V) (s : V) :
    movedLine D.representation s cubicOvergroup = cubicPlane D.representation s firstCubic := by
  apply le_antisymm
  · apply commutator_le_cubicPlane
    intro g hg
    rw [first_residual] at hg
    obtain ⟨n, _, hn⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hg)
    rw [← hn]
    exact cubic_power_mem D s firstCubic (by decide) n
  · exact cubicPlane_le_commutator D s firstCubic (by decide) _
      (by rw [first_residual]; exact mem_zpowers _)

/-- The second moved space uses the three actual residual cosets modulo the Sylow group. -/
theorem second_moved_eq (D : Pair V) (s : V)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    movedLine D.representation s duadOvergroup = cubicPlane D.representation s secondCubic := by
  apply le_antisymm
  · apply commutator_le_cubicPlane
    intro g hg
    change g ∈ residual duadOvergroup at hg
    rw [residual, residual_duadOvergroup] at hg
    obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hg
    obtain ⟨n, hn⟩ := duad_cosets x
    rw [orbit_eq_of_coset D.representation s standardTwo hs _ _ hn]
    exact cubic_power_mem D s secondCubic (by decide) n.val
  · exact cubicPlane_le_commutator D s secondCubic (by decide) _ secondCubic_mem

private theorem cubicPlane_finrank (D : Pair V) (s : V) (hne : s ≠ 0)
    (r : S7) (hr : r.IsThreeCycle) :
    Module.finrank (ZMod 2) (cubicPlane D.representation s r) = 2 := by
  have hzero : D.representation r s ≠ 0 := by
    intro h
    have hh := congrArg (D.representation r⁻¹) h
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] at hh
    exact hne hh
  have hfix : D.representation r s ≠ s := fun h =>
    hne (threeCycle_fixedPointFree D r hr s h)
  have hsum : s + D.representation r s ≠ 0 := by
    intro h
    have hh := eq_neg_of_add_eq_zero_right h
    exact hfix (by simpa only [ZModModule.neg_eq_self] using hh)
  have hi : LinearIndependent (ZMod 2) ![s, D.representation r s] := by
    rw [LinearIndependent.pair_iff]
    intro x y h
    have hf : ∀ k : ZMod 2, k = 0 ∨ k = 1 := by decide
    rcases hf x with rfl | rfl <;> rcases hf y with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at h ⊢
    · trivial
    · exact (hzero h).elim
    · exact (hne h).elim
    · exact (hsum h).elim
  have hspan : Set.range ![s, D.representation r s] = {s, D.representation r s} := by
    ext v
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [cubicPlane]
  have hh := finrank_span_eq_card hi
  change Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range ![s, D.representation r s])) = 2 at hh
  rwa [hspan] at hh

/-- The first source moved plane has dimension two. -/
theorem first_moved_finrank (D : Pair V) (s : V) (hne : s ≠ 0) :
    Module.finrank (ZMod 2) (movedLine D.representation s cubicOvergroup) = 2 := by
  rw [first_moved_eq]
  exact cubicPlane_finrank D s hne firstCubic (by decide)

/-- The second source moved plane has dimension two. -/
theorem second_moved_finrank (D : Pair V) (s : V) (hne : s ≠ 0)
    (hs : ∀ t ∈ standardTwo, D.representation t s = s) :
    Module.finrank (ZMod 2) (movedLine D.representation s duadOvergroup) = 2 := by
  rw [second_moved_eq D s hs]
  exact cubicPlane_finrank D s hne secondCubic (by decide)

end Representation.AlternatingSevenConjugatePair.SourceLineGeometry
