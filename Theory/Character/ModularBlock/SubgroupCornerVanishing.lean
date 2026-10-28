module

public import Theory.Character.ModularBlock.PrimitiveCorner
public import Theory.Character.ModularBlock.SubgroupBrauerHom

/-!
# Vanishing of factors fixed by principal-corner Brauer images

Let Q be any two-subgroup of a finite group. A central augmentation-zero
element in the reduced principal-block corner has nilpotent Q-Brauer image.
Consequently, any factor on which that image acts as the identity is zero.
The corner nilpotence theorem supplies a vanishing power; subgroup Brauer
restriction is a ring homomorphism on centers, so it preserves that power.
Iterating the identity action on the factor then proves its vanishing.

This is the subgroup form of principal-corner vanishing used in the
maximal-support proof of Brauer's third main theorem. Ported from
`public/lean-eval/glauberman_zStar`, `Submission/ZStar/BrauerThirdMain.lean`
(revision `c3503435`), with the current augmentation API.
-/

public section

noncomputable section

namespace ModularBlock.BrauerThirdMain

open PrincipalBlockConstruction

universe v

/-- The principal-corner nilpotence argument works for every subgroup
Brauer restriction, not only the involution restriction. -/
theorem eq_zero_of_subgroupRestriction_mul_eq_self_of_corner_augmentation_zero
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer (Q : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q a * f = f) :
    f = 0 := by
  let K := BrauerBlockReduction.principalResidueField d
  have hnilA : IsNilpotent a :=
    PrimitiveCorner.reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
      d a haCenter hfactor haug
  let aZ : Subring.center (MonoidAlgebra K G) := ⟨a, haCenter⟩
  have hnilZ : IsNilpotent aZ := by
    rcases hnilA with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  let br := SubgroupBrauerMap.subgroupCentralizerRestrictionCenterHom
    2 K Q hQ
  have hnilBr : IsNilpotent (br aZ) := hnilZ.map br
  let x : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)) := br aZ
  have hxmul : x * f = f := by
    simpa [x, br, aZ, K] using hrestrict
  have hxpow : ∀ n : ℕ, x ^ n * f = f := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, mul_assoc, hxmul, ih]
  rcases hnilBr with ⟨n, hn⟩
  have hxn : x ^ n = 0 := by
    exact congrArg
      (fun y : Subring.center
        (MonoidAlgebra K (Subgroup.centralizer (Q : Set G))) =>
          (y : MonoidAlgebra K (Subgroup.centralizer (Q : Set G)))) hn
  calc
    f = x ^ n * f := (hxpow n).symm
    _ = 0 := by rw [hxn, zero_mul]

end ModularBlock.BrauerThirdMain

