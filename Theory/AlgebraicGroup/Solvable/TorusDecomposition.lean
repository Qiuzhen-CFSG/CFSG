module

public import Theory.AlgebraicGroup.Solvable.MaximalTorusConjugacy

/-!
# Solvable torus-unipotent decomposition

This module proves the decomposition form of Borel, *Linear Algebraic Groups*,
Chapter III, Theorem 10.6(4), for a specified maximal torus of a connected
solvable algebraic group.  The complementary subgroup is the connected
unipotent radical, so the result supplies its unipotence together with
pointwise factorization and trivial intersection.

The proof starts from the independently constructed maximal torus complement
and conjugates the specified maximal torus to it using the solvable conjugacy
theorem.  To transfer factorization back, conjugate an arbitrary point into the
known product, factor there, and conjugate both factors back.  Normality of the
unipotent radical keeps the second factor in the same subgroup; the independent
torus--unipotent intersection theorem gives trivial intersection.  Thus this
module does not use the later maximal-torus image or Borel decomposition
theorems.
-/

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- A specified maximal torus in a connected solvable algebraic group
complements the connected unipotent radical. -/
public theorem exists_unipotentRadical_complement_of_maximalTorus_solvable_connected
    {G : Variety k} [AlgebraicGroup G]
    (hsolvable : Group.IsSolvable (Variety.Point G))
    (hconnected : Variety.IsConnected G)
    (T : ClosedSubgroup G) (hT : IsMaximalTorus T) :
    ∃ U : ClosedSubgroup G,
      IsUnipotentRadicalSubgroup U ∧
      Variety.IsConnected U.carrierVariety ∧
      IsUnipotentAlgebraicGroup U.carrierVariety ∧
      IsTorusComplement T U := by
  obtain ⟨U, hUrad, hUconnected, M, hMcomplement, _hMmaximal⟩ :=
    exists_maximalTorus_complement_of_solvable_connected
      hsolvable hconnected
  have hUunipotent : IsUnipotentAlgebraicGroup U.carrierVariety :=
    hUrad.isUnipotent_of_solvable_connected hsolvable hconnected
  have hUnormal : U.toSubgroup.Normal :=
    hUrad.normal_of_solvable_connected hsolvable hconnected
  obtain ⟨g, _hgU, hg⟩ :=
    maximalTorus_conjugate_to_torusComplement_by_unipotentRadical
      hsolvable hconnected U M T hUrad hMcomplement hT
  have hfactor : ∀ x : Variety.Point G, ∃ t u,
      t ∈ T.toSubgroup ∧ u ∈ U.toSubgroup ∧ x = t * u := by
    intro x
    obtain ⟨m, v, hm, hv, hmv⟩ := hMcomplement.2.1 (g * x * g⁻¹)
    let t := g⁻¹ * m * g
    let u := g⁻¹ * v * g
    have hmConjugate : m ∈ (T.conjugate g).toSubgroup := by
      rw [hg]
      exact hm
    have ht : t ∈ T.toSubgroup :=
      (T.mem_conjugate_iff g m).mp hmConjugate
    have hu : u ∈ U.toSubgroup := by
      simpa [u] using hUnormal.conj_mem v hv g⁻¹
    refine ⟨t, u, ht, hu, ?_⟩
    dsimp [t, u]
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (m * v) * g := by rw [hmv]
      _ = (g⁻¹ * m * g) * (g⁻¹ * v * g) := by group
  have hTU : T.toSubgroup ⊓ U.toSubgroup = ⊥ :=
    subtorus_inf_unipotent_eq_bot T U hT.1 hUunipotent
  exact ⟨U, hUrad, hUconnected, hUunipotent, hT.1, hfactor, hTU⟩

end Theory.AlgebraicGroup
