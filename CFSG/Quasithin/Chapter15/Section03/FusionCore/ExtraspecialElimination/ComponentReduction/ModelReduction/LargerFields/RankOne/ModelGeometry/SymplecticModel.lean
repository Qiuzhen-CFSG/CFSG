module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry.NormalizerData
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerDerived
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableOvergroupGeometry
public import Theory.SpecificGroups.SymplecticFour.Sylow.SolvableRootOrbit
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.CubicSubgroup

/-!
# Cubic normalizer geometry in the full symplectic model

The matrix Borel contains an elementary abelian subgroup of order nine in
even field degree. Its nonidentity elements have order three, so it lies in
the literal order-three-generated subgroup theta. An actual multiplicative
equivalence transports this witness to any supplied Sylow normalizer.

The root calculation makes the standard point orbit of every solvable
unipotent overgroup orthogonal. Its span gives an invariant isotropic subspace,
so the parabolic placement theorem and Sylow conjugacy prove normalization
for every supplied Sylow subgroup. Together with the commutator and odd-degree
order calculations, this establishes all four normalizer properties without
any additional geometric premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
15.3.49 after (k), printed p.1144.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter15.Section03
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
variable {F : Type*} [Field F] [Finite F]

/-- An actual elementary abelian cubic subgroup lies in theta of every supplied
Sylow normalizer. The witness is the conjugate of the literal diagonal torus. -/
theorem symplectic_theta_normalizer_rank {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 1 ≤ n) (he : Even n)
    (S : Sylow 2 (Matrix.symplecticGroup (Fin 2) F)) :
    2 ≤ primeRank 3 (theta (normalizer (S : Set (Sp F)))) := by
  obtain ⟨E, hE, hcard⟩ := exists_cubic_borel_subgroup hF he
  let _ := hE
  let : CommGroup E := IsMulCommutative.instCommGroup
  let N := normalizer (S : Set (Sp F))
  let a : borel (F := F) ≃* N := (sylowNormalizerEquiv hF hn S).symm
  let f : E →* Sp F := N.subtype.comp (a.toMonoidHom.comp E.subtype)
  have hf : Function.Injective f := N.subtype_injective.comp (a.injective.comp E.subtype_injective)
  have hp : ∀ x : E, x ^ 3 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 E)
  have hmem (x : E) : f x ∈ theta N := by
    by_cases hx : f x = 1
    · rw [hx]
      exact (theta N).one_mem
    · have hNx : f x ∈ N := (a (E.subtype x)).property
      have hpx : (f x) ^ 3 = 1 := by rw [← map_pow, hp x, map_one]
      exact Subgroup.subset_closure ⟨hNx, orderOf_eq_prime hpx hx⟩
  let j : E →* theta N := f.codRestrict (theta N) hmem
  have hj : Function.Injective j := by
    intro x y h
    exact hf (congrArg (fun z : theta N => (z : Sp F)) h)
  exact primeRank_ge_of_elementary_embedding hp hcard j hj

/-- The symplectic normalizer data, conditional only on the remaining
long-root orbit calculation. The orbit premise is not asserted here. -/
theorem symplectic_normalizerData_of_orthogonal_root_orbits [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n)
    (hroot : ∀ (H : Subgroup (Sp F)), Group.IsSolvable H → unipotent ≤ H →
      ∀ g ∈ H, form F (e 0) (g • e 0) = 0) :
    NormalizerData (Matrix.symplecticGroup (Fin 2) F) n 2 where
  solvable_overgroups := solvable_overgroups_of_orthogonal_root_orbits hF hn hroot
  commutator_le := commutator_sylow_normalizer_le hF hn.le
  odd := fun ho S => three_not_dvd_card_normalizer hF hn.le ho S
  rank := fun he S => symplectic_theta_normalizer_rank hF hn.le he S

/-- The full symplectic matrix group over a nonbinary field of characteristic
two has all four required Sylow normalizer properties. -/
theorem symplectic_normalizerData [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n) (hn : 1 < n) :
    NormalizerData (Matrix.symplecticGroup (Fin 2) F) n 2 := by
  have hlarge : 2 < Nat.card F := by
    rw [hF]
    exact (show (2 : ℕ) ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  exact symplectic_normalizerData_of_orthogonal_root_orbits hF hn
    (solvable_unipotent_point_orbit_orthogonal hlarge)

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.LargerFields.RankOne.ModelGeometry
