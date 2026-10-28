module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification.Basic

/-!
# The concrete pair used in the Suzuki-component placement argument

Let A be the fixed middle-node B₂ Levi, and let w = rₐ rᵦ rₐ, using the
actual fixed Weyl words on the outer and middle node orbits. Define B = Aʷ
and N = N_G(A ⊔ B). The root-word calculation below proves w² = 1, so w
interchanges A and B and belongs to N. Commutation, distinctness and the
structure of N are not consequences of these definitions.

Two geometric obligations are separated: placing a supplied maximal subgroup
inside a conjugate of N, and calculating the components of this one concrete
normalizer. Maximality will upgrade the placement to equality. Neither
obligation is asserted here as an unconditional theorem.

Source: Malle, *The maximal subgroups of ²F₄(q²)*, J. Algebra 139 (1991),
52–69, DOI 10.1016/0021-8693(91)90283-E, §2.2 and Proposition 2.3.
The Weyl words use GLS3, §2.3, in `refs/KGroup/GLS3/chapter2.tex`.
-/

@[expose] public section

open Subgroup
open ReeF4
open ReeF4.Parabolics.Binary.FixedGeometry
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem

namespace ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification

private theorem simpleWeyl_inv (m : ℕ) (i : Fin 4) :
    (Parabolics.weylWord m (typeF4SimpleRootIndex i) 1)⁻¹ =
      Parabolics.weylWord m (typeF4SimpleRootIndex i) 1 := by
  have hr (r : F4Chevalley.Root) (t : CoefficientField m) :
      (rootGeneratorInGroup m r t)⁻¹ = rootGeneratorInGroup m r t := by
    apply Subtype.ext
    simp [F4Chevalley.rootCurve_inv, CharTwo.neg_eq]
  simp only [Parabolics.weylWord, mul_inv_rev, hr, mul_assoc]

private theorem canonicalWeyl_inv (m : ℕ) (s : LargeLocalSeeds.Side) :
    (weylLift m s)⁻¹ = weylLift m s := by
  apply Subtype.ext
  have h := sideWord_fixed m s
  rw [reeTwist_simpleWord] at h
  change (simpleWord m (sideWord s))⁻¹ = simpleWord m (sideWord s)
  cases s with
  | suzuki =>
    change simpleWord m [2, 1, 2, 1] = simpleWord m [1, 2, 1, 2] at h
    simpa only [sideWord, simpleWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev, simpleWeyl_inv, mul_assoc] using h
  | linear =>
    change simpleWord m [3, 0] = simpleWord m [0, 3] at h
    simpa only [sideWord, simpleWord, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev, simpleWeyl_inv] using h

/-- The fixed Weyl word rₐ rᵦ rₐ from the generic Suzuki pair construction. -/
noncomputable def suzukiFactorSwap (m : ℕ) : Model m :=
  weylLift m .linear * weylLift m .suzuki * weylLift m .linear

@[simp] theorem suzukiFactorSwap_inv (m : ℕ) :
    (suzukiFactorSwap m)⁻¹ = suzukiFactorSwap m := by
  simp only [suzukiFactorSwap, mul_inv_rev, canonicalWeyl_inv, mul_assoc]

@[simp] theorem suzukiFactorSwap_mul_self (m : ℕ) :
    suzukiFactorSwap m * suzukiFactorSwap m = 1 := by
  simpa only [suzukiFactorSwap_inv] using inv_mul_cancel (suzukiFactorSwap m)

/-- The image of the full fixed B₂ Levi under the specified Weyl word. -/
noncomputable def companionSuzukiLevi (m : ℕ) : Subgroup (Model m) :=
  (standardSuzukiLevi m).map (MulAut.conj (suzukiFactorSwap m)).toMonoidHom

/-- The join of the canonical Levi and its specified companion. -/
noncomputable def suzukiLeviPair (m : ℕ) : Subgroup (Model m) :=
  standardSuzukiLevi m ⊔ companionSuzukiLevi m

/-- The actual ambient normalizer of the concrete join. -/
noncomputable def suzukiLeviPairNormalizer (m : ℕ) : Subgroup (Model m) :=
  normalizer (suzukiLeviPair m : Set (Model m))

/-- The word takes the companion back to the full canonical Levi. -/
theorem companionSuzukiLevi_map_swap (m : ℕ) :
    (companionSuzukiLevi m).map (MulAut.conj (suzukiFactorSwap m)).toMonoidHom =
      standardSuzukiLevi m := by
  rw [companionSuzukiLevi, map_map]
  have he : (MulAut.conj (suzukiFactorSwap m)).toMonoidHom.comp
      (MulAut.conj (suzukiFactorSwap m)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change suzukiFactorSwap m *
      (suzukiFactorSwap m * x * (suzukiFactorSwap m)⁻¹) * (suzukiFactorSwap m)⁻¹ = x
    rw [suzukiFactorSwap_inv]
    calc
      _ = (suzukiFactorSwap m * suzukiFactorSwap m) * x *
          (suzukiFactorSwap m * suzukiFactorSwap m) := by group
      _ = x := by simp only [suzukiFactorSwap_mul_self, one_mul, mul_one]
  rw [he, map_id]

/-- The specified word preserves the join of the two subgroups. -/
theorem suzukiLeviPair_map_swap (m : ℕ) :
    (suzukiLeviPair m).map (MulAut.conj (suzukiFactorSwap m)).toMonoidHom =
      suzukiLeviPair m := by
  rw [suzukiLeviPair, Subgroup.map_sup, companionSuzukiLevi_map_swap]
  exact sup_comm _ _

/-- The interchange belongs to the ambient normalizer by the preceding identity. -/
theorem suzukiFactorSwap_mem_normalizer (m : ℕ) :
    suzukiFactorSwap m ∈ suzukiLeviPairNormalizer m :=
  mem_normalizer_iff_map_conj_eq.mpr (suzukiLeviPair_map_swap m)

/-- The global geometric placement obligation, prior to maximality. This must
be proved from the fixed-point construction; it is not an assumed catalogue. -/
def SuzukiPairPlacement : Prop :=
  ∀ m, 1 ≤ m → ∀ M : Subgroup (Model m), IsCoatom M →
    ¬ Group.IsSolvable M → solvableRadical M = ⊥ → ∀ L K : Subgroup M,
      L.IsCComponent → K.IsCComponent → L ≠ K → ⁅L, K⁆ = ⊥ →
        ∃ g : Model m,
          M.map (MulAut.conj g).toMonoidHom ≤ suzukiLeviPairNormalizer m

/-- The independent calculation for the one concrete normalizer. Both
properness and the full-parameter component equalities remain proof obligations. -/
def SuzukiPairNormalizerGeometry : Prop :=
  ∀ m, 1 ≤ m → suzukiLeviPairNormalizer m ≠ ⊤ ∧
    ∀ L : Subgroup (suzukiLeviPairNormalizer m), L.IsCComponent →
      L.map (suzukiLeviPairNormalizer m).subtype = standardSuzukiLevi m ∨
        L.map (suzukiLeviPairNormalizer m).subtype = companionSuzukiLevi m

end ReeF4.MaximalSubgroups.CommutingComponents.CarrierIdentification
