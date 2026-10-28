module

public import Theory.AlgebraicGroup.Bor1.WeightSpacePermutation
public import Theory.AlgebraicGroup.Representations.Solvable
public import Theory.AlgebraicGroup.Representations.Algebraic.Irreducible

/-!
This module proves the Clifford--Lie--Kolchin scalar-action lemma.  A common
eigenvector for the connected solvable subgroup is obtained from the public
Lie--Kolchin API.  Bor1's normal-weight permutation theorem then shows that
the corresponding nonzero common weight space has a finite ambient orbit:
the independent-family theorem makes the set of nonzero weights finite.
Connectedness of the ambient group and closedness of subspace stabilizers
force this orbit to be a singleton.  The weight space is therefore ambient
invariant, and irreducibility makes it all of the representation, yielding a
single scalar for every subgroup element.  The restriction representation is
formed by the public pullback API; no classification input is used.
-/

namespace Theory.AlgebraicGroup

open Bor1

set_option linter.style.haveILetI false

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Every connected solvable normal closed subgroup acts by scalars in a
finite-dimensional irreducible rational representation of a connected
algebraic group. -/
public theorem RationalRepresentation.acts_by_scalars_of_isIrreducible
    {G : Variety k} [AlgebraicGroup G]
    {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V] [Nontrivial V]
    (ρ : RationalRepresentation G V)
    (hirr : IsIrreducibleRepresentation ρ)
    (hG : Variety.IsConnected G)
    (N : ClosedSubgroup G)
    (hNnormal : N.toSubgroup.Normal)
    (hNsolvable : Group.IsSolvable (Variety.Point N.carrierVariety))
    (hNconnected : Variety.IsConnected N.carrierVariety) :
    ∃ χ : N.toSubgroup → k, ∀ n : N.toSubgroup,
      (ρ.action n : Module.End k V) = χ n • LinearMap.id := by
  letI : N.toSubgroup.Normal := hNnormal
  obtain ⟨τ, hpull, hτrational⟩ :=
    rationalRepresentation_pullback_exists N.inclusion ρ hirr.1
  obtain ⟨χ₀, v, hv, hveig⟩ :=
    τ.exists_common_eigenvector_of_isSolvable_isConnected_public
      hτrational hNsolvable hNconnected
  let χ : N.toSubgroup → k := fun n => χ₀ (N.pointEquiv.symm n)
  have hveig' : ∀ n : N.toSubgroup,
      (ρ.action n : Module.End k V) v = χ n • v := by
    intro n
    have h := hveig (N.pointEquiv.symm n)
    rw [hpull] at h
    exact h
  let σ := Bor1.rationalRepresentationUnderlying ρ
  have hχ : Bor1.Representation.commonEigenspace σ N.toSubgroup χ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, ?_, hv⟩
    dsimp [Bor1.Representation.commonEigenspace]
    rw [Submodule.mem_iInf]
    intro n
    apply Module.End.mem_eigenspace_iff.mpr
    exact hveig' n
  let χi : Bor1.Representation.commonWeightIndex σ N.toSubgroup := ⟨χ, hχ⟩
  let W : Submodule k V := Bor1.Representation.commonWeightSpace σ N.toSubgroup χi
  have hWne : W ≠ ⊥ := by
    exact χi.property
  have hfiniteIdx : Finite (Bor1.Representation.commonWeightIndex σ N.toSubgroup) := by
    have heig := Bor1.Representation.commonWeightSpace_iSupIndep σ N.toSubgroup
    letI : Fintype {χi : Bor1.Representation.commonWeightIndex σ N.toSubgroup //
        Bor1.Representation.commonWeightSpace σ N.toSubgroup χi ≠ ⊥} :=
      heig.fintypeNeBotOfFiniteDimensional
    apply Finite.of_injective (fun χi =>
      (⟨χi, χi.property⟩ : {χi : Bor1.Representation.commonWeightIndex σ N.toSubgroup //
        Bor1.Representation.commonWeightSpace σ N.toSubgroup χi ≠ ⊥}))
    intro a b hab
    simpa using congrArg Subtype.val hab
  letI : Finite (Bor1.Representation.commonWeightIndex σ N.toSubgroup) := hfiniteIdx
  have hfinite : (Set.range fun g : Variety.Point G =>
      Submodule.map (σ g : Module.End k V) W).Finite := by
    apply (Set.finite_range (Bor1.Representation.commonWeightSpace σ N.toSubgroup)).subset
    rintro U ⟨g, rfl⟩
    refine ⟨Bor1.Representation.normalCommonWeightPermutation
      σ N.toSubgroup g χi, ?_⟩
    exact (Bor1.Representation.commonWeightSpace_map
      σ N.toSubgroup g χi).symm
  have hWinv : ∀ g : Variety.Point G,
      Submodule.map (σ g : Module.End k V) W = W :=
    Bor1.Representation.subspace_invariant_of_connected_of_finite_orbit
      σ W hG (RationalRepresentation.subspaceStabilizer_isZariskiClosed_Bor1
        ρ hirr.1 W) hfinite
  have hWinv' : IsInvariantSubmodule ρ W := by
    intro g x hx
    have hm : (ρ.action g : Module.End k V) x ∈
        Submodule.map (ρ.action g : Module.End k V) W := ⟨x, hx, rfl⟩
    change (σ g : Module.End k V) x ∈
      Submodule.map (σ g : Module.End k V) W at hm
    rw [hWinv g] at hm
    exact hm
  have hWtop : W = ⊤ := by
    rcases hirr.2 W hWinv' with hbot | htop
    · exact False.elim (hWne hbot)
    · exact htop
  refine ⟨χ, ?_⟩
  intro n
  apply LinearMap.ext
  intro x
  have hxW : x ∈ W := by rw [hWtop]; trivial
  have hx : x ∈ Bor1.Representation.commonEigenspace σ N.toSubgroup χ := by
    exact hxW
  dsimp [Bor1.Representation.commonEigenspace] at hx
  rw [Submodule.mem_iInf] at hx
  have he := Module.End.mem_eigenspace_iff.mp (hx n)
  change (ρ.action n : Module.End k V) x = χ n • x
  exact he

end Theory.AlgebraicGroup
