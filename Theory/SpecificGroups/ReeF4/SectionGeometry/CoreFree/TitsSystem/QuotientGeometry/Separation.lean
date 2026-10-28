module

public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.UniformWords
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.TitsSystem.QuotientGeometry.Monomial

/-!
# The two relative Weyl lifts have distinct Borel cosets

The linear orbit word sends the first simple root to its negative. The
Suzuki orbit word preserves the second coordinate of that root, because
both of its simple reflecting roots have zero there. Thus their genuine
Weyl permutations differ. If the quotient of the two matrix lifts lay in
the Borel, the proved Borel–normalizer intersection would put it in the
torus, whose root permutation is the identity, a contradiction.

This calculation is unconditional, over every Ree coefficient field.
Source: the two orbit reflections of GLS3 2.3.2–4,
`refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
namespace ReeF4.SectionGeometry.BNPair.QuotientGeometry
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction Subgroup
open Parabolics Parabolics.Binary.FixedGeometry
open Parabolics.Binary.FixedGeometry.BruhatCoverage.FixedWeyl
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
open NormalizerGeometry

private abbrev sr := typeF4SimpleRootIndex

/-- The actual two orbit words induce different permutations of the F₄ roots. -/
theorem side_permutations_ne :
    typeF4RootPairing.weylGroupToPerm (rootWord (sideWord .linear)) ≠
      typeF4RootPairing.weylGroupToPerm (rootWord (sideWord .suzuki)) := by
  intro he
  have h := congrArg (fun e : Equiv.Perm F4Chevalley.Root =>
    (typeF4RootPairing.root (e (sr 0))) 1) he
  change (typeF4RootPairing.root
    (typeF4RootPairing.reflectionPerm (sr 0) (typeF4RootPairing.reflectionPerm (sr 3) (sr 0)))) 1 =
      (typeF4RootPairing.root
        (typeF4RootPairing.reflectionPerm (sr 1) (typeF4RootPairing.reflectionPerm (sr 2)
          (typeF4RootPairing.reflectionPerm (sr 1) (typeF4RootPairing.reflectionPerm (sr 2) (sr 0)))))) 1 at h
  have h03 : typeF4RootPairing.reflectionPerm (sr 3) (sr 0) = sr 0 := by
    apply typeF4RootPairing.reflectionPerm_eq_of_pairing_eq_zero
    rw [← typeF4RootPairing.algebraMap_pairingIn ℤ]
    have hp : typeF4RootPairing.pairingIn ℤ (sr 0) (sr 3) = typeF4CartanMatrix 0 3 :=
      typeF4RootPairing_base_cartan_apply 0 3
    rw [hp]
    norm_num [typeF4CartanMatrix, Fin.ext_iff]
  rw [h03, typeF4RootPairing.root_reflectionPerm,
    typeF4RootPairing.reflection_apply_self] at h
  simp only [typeF4RootPairing.root_reflectionPerm, typeF4RootPairing.reflection_apply] at h
  norm_num [Pi.sub_apply, Pi.smul_apply, typeF4RootPairing_root,
    sr, typeF4SimpleRootIndex_val, typeF4SimpleRoot] at h

end ReeF4.SectionGeometry.BNPair.QuotientGeometry

namespace ReeF4.SectionGeometry.BNPair
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open Parabolics Parabolics.Binary.FixedGeometry QuotientGeometry
open LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover.NormalizerGeometry
/-- The two actual fixed lifts represent different Borel cosets. -/
theorem weylLift_linear_inv_mul_suzuki_not_mem_borel (m : ℕ) :
    (weylLift m .linear)⁻¹ * weylLift m .suzuki ∉ borel m := by
  intro hB
  have hN : (weylLift m .linear)⁻¹ * weylLift m .suzuki ∈ normalizerWords m :=
    (normalizerWords m).mul_mem
      ((normalizerWords m).inv_mem (weylLift_mem_normalizerWords m .linear))
      (weylLift_mem_normalizerWords m .suzuki)
  have ht : (weylLift m .linear)⁻¹ * weylLift m .suzuki ∈ fixedTorus m := by
    rw [← borel_inf_normalizerWords]
    exact ⟨hB, hN⟩
  change toSplitGroup m ((weylLift m .linear)⁻¹ * weylLift m .suzuki) ∈ splitTorus m at ht
  rw [map_mul, map_inv, toSplitGroup_weylLift, toSplitGroup_weylLift] at ht
  obtain ⟨c, hc⟩ := torus_rootMonomial ht
  have hm := rootMonomial_mul (monomial_inv (simpleWord_rootMonomial m (sideWord .linear)))
    (simpleWord_rootMonomial m (sideWord .suzuki))
  have hp := monomial_perm_unique hm hc
  exact side_permutations_ne (inv_mul_eq_one.mp hp)

end ReeF4.SectionGeometry.BNPair
