module

public import Glauberman.Definitions
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Solvable groups exclude Qd at primes at least five

For a prime `p ≥ 5`, a finite solvable group has no section isomorphic to
the natural quadratic group `Qd(p) = C_p² ⋊ SL₂(p)`. A hypothetical section
would make its `SL₂(p)` quotient solvable. The scalar `2` in `ZMod p` has
nonzero square different from one, so Mathlib's transvection commutator
theorem makes `SL₂(p)` perfect. Its nontrivial projective quotient then
contradicts solvability.

Together with Glauberman's proved Lemma 6.3, this gives the solvable case
of the p-stability input in Kurzweil–Stellmacher, *The Theory of Finite
Groups*, 9.4.5(1). It is used for the ZJ normalizer supplement corresponding
to 9.4.6 and the characteristic-subgroup step of signalizer completion in
11.2.8. The argument uses the actual `Qd` semidirect product from
`Glauberman.Definitions`.
-/

namespace Glauberman

/-- A finite solvable group cannot involve `Qd(p)` when the prime is at least five. -/
public theorem qd_not_involved_of_solvable
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) :
    ¬ Involved (Qd p) G := by
  intro hInv
  obtain ⟨K, N, hN, ⟨e⟩⟩ := hInv
  let : N.Normal := hN
  let : Group.IsSolvable G := hsolv
  let : Group.IsSolvable (Qd p) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsSolvable (qdSL p) :=
    Group.isSolvable_of_surjective (SemidirectProduct.rightHom_surjective (φ := qdAction p))
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 2 < p)
      ((ZMod.natCast_eq_zero_iff 2 p).mp h)
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega : 3 < p)
      ((ZMod.natCast_eq_zero_iff 3 p).mp h)
  have hsq : (2 : ZMod p) ^ 2 ≠ 1 := by
    intro h
    apply hthree
    have hh := sub_eq_zero.mpr h
    norm_num at hh ⊢
    exact hh
  let : Group.IsPerfect (qdSL p) := ⟨Matrix.SL2.commutator_eq_top htwo hsq⟩
  exact Group.IsPerfect.not_isSolvable
    (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod p)) inferInstance

end Glauberman
