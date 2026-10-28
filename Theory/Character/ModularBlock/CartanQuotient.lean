module

public import Theory.Character.ModularBlock.CartanOddQuotient
public import Theory.Character.ModularBlock.CartanCentralQuotient
public import Theory.Character.ModularBlock.CartanEquiv

/-!
# Principal-block Cartan quotient comparisons

The genuine principal-block quotient theorems preserve the contracted modular
place. Odd normal subgroups preserve Brauer degrees and Cartan entries; central
two-subgroups preserve Brauer degrees and multiply Cartan entries by their
order. Group-isomorphism transport lets computations on a named quotient model
feed either theorem without choosing a new modular prime.

The ordinary-character correspondence, simple-module inflation and descent,
and the ordinary kernel comparison are proved in the imported modules. This
assembly is used for the local computations in Fong, *Some Sylow subgroups of
order 32*, J. Algebra 6 (1967), p. 71; see also Feit, *The Representation
Theory of Finite Groups*, III.2.13 and IV.4.12.
-/

public section
noncomputable section

namespace ModularBlock.Cartan

open PrincipalBlockConstruction CompatibleLocalBlock

universe u v
variable {G : Type u} {K : Type v} [Group G] [Finite G] [Group K] [Finite K]

/-- Apply decomposition data computed on a model of an odd normal quotient at
the modular place transported from the original group. -/
theorem exists_oddNormalQuotient_of_equiv
    (d : PrincipalCongruenceBlockData G) (N : Subgroup G) [N.Normal]
    (hN : Odd (Nat.card N)) (e : (G ⧸ N) ≃* K) {n : ℕ}
    (aK : PrincipalDecompositionData
      ((compatibleQuotientPrincipalCongruenceBlockData d N).transport e) n) :
    ∃ aG : PrincipalDecompositionData d n,
      aG.family.degree = aK.family.degree ∧
      ∀ j k, aG.cartan j k = aK.cartan j k := by
  let aQ := aK.transportBack e
  refine ⟨aQ.ofOddQuotient d N hN, ?_, ?_⟩
  · funext j
    simp [aQ]
  · intro j k
    simp [aQ]

/-- Apply decomposition data computed on a model of a central two-quotient at
the transported modular place, scaling its Cartan matrix by the kernel order. -/
theorem exists_centralTwoQuotient_of_equiv
    (d : PrincipalCongruenceBlockData G) (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    (e : (G ⧸ Z) ≃* K) {n : ℕ}
    (aK : PrincipalDecompositionData
      ((compatibleQuotientPrincipalCongruenceBlockData d Z).transport e) n) :
    ∃ aG : PrincipalDecompositionData d n,
      aG.family.degree = aK.family.degree ∧
      ∀ j k, aG.cartan j k = Nat.card Z * aK.cartan j k := by
  let aQ := aK.transportBack e
  obtain ⟨aG, _, hdegree, hcartan⟩ := exists_centralTwoQuotient d Z hcentral hZ aQ
  refine ⟨aG, ?_, ?_⟩
  · funext j
    exact (congrFun hdegree j).trans (aK.transportBack_degree e j)
  · intro j k
    simpa [aQ] using hcartan j k

end ModularBlock.Cartan
