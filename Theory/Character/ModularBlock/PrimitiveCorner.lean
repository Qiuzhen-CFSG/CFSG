module
public import Theory.Character.ModularBlock.FinitePrimitiveCorner
public import Theory.Character.ModularBlock.PrincipalPrimitivity
public import Mathlib.Data.Finsupp.Fintype

/-!
# Primitive principal corners eliminate transfer witnesses

An augmentation-zero central element in the reduced principal-block corner
is nilpotent. Consequently, if its Brauer restriction acts as the identity
on a local factor, that factor vanishes. Applied to the difference between
the ambient Brauer image and the compatible local principal selector, this
gives principal Brauer equality from a relative-transfer witness.

The principal residue field is finite because the defining cyclotomic
prime contains two and is nonzero. The proved principal-block primitivity
theorem and augmentation-one identity specialize the generic finite-corner
nilpotence result. Brauer restriction on the center is a ring homomorphism,
so it preserves nilpotence. Iterating its identity action on the local
factor then kills that factor with a vanishing power.

Ported from the principal-block specialization in
`Submission/ZStar/PrimitiveCorner.lean` at revision `c3503435` of
`public/lean-eval/glauberman_zStar`. All required primitivity and reduction
results are proved production imports. Constructing the transfer witness is
the separate downstream relative-transfer argument.
-/

namespace ModularBlock.PrimitiveCorner

universe u v

attribute [local instance] Fintype.ofFinite

private theorem principalResidueField_finite
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G) :
    Finite (BrauerBlockReduction.principalResidueField d) := by
  have hprime_ne_bot : d.primeIdeal ≠ ⊥ := by
    intro hbot
    have htwo := BlockPreliminaries.two_mem_of_liesOver
      d.primeIdeal d.primeIdeal_liesOverTwo
    rw [hbot, Ideal.mem_bot] at htwo
    exact two_ne_zero htwo
  exact CyclotomicDVR.cyclotomicOrder_quotient_finite
    (Nat.card_pos (α := G)).ne' d.eta_spec d.primeIdeal hprime_ne_bot

/-- Every augmentation-zero central element in the reduced principal-block
corner is nilpotent. -/
public theorem reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0) :
    IsNilpotent a := by
  let : Finite (BrauerBlockReduction.principalResidueField d) :=
    principalResidueField_finite d
  let : Field (BrauerBlockReduction.principalResidueField d) :=
    Ideal.Quotient.field d.primeIdeal
  let : Fintype (BrauerBlockReduction.principalResidueField d) :=
    Fintype.ofFinite (BrauerBlockReduction.principalResidueField d)
  let : Fintype G := Fintype.ofFinite G
  let : DecidableEq G := Classical.decEq G
  let : Finite
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) := by
    exact Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  exact isNilpotent_of_centrallyPrimitive_of_map_eq_zero
    (groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) G).toRingHom
    (BrauerBlockReduction.reducedPrincipalBlockElement d) a
    (BlockPrimitivity.reducedPrincipalBlockElement_isCentrallyPrimitive d)
    haCenter hfactor
    (BrauerBlockReduction.reducedPrincipalBlockElement_augmentation_eq_one d)
    haug

/-- An augmentation-zero witness in the ambient principal corner cannot have
Brauer restriction acting as the identity on a nonzero local factor.

This is the exact ring-theoretic endpoint needed by a relative-transfer
argument.  Once a central transfer witness `a` satisfies
`Br_z(a) * f = f`, primitive-corner nilpotence makes `Br_z(a)` nilpotent,
and hence forces `f = 0`. -/
public theorem eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (f : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)))
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z a * f = f) :
    f = 0 := by
  have hnilA : IsNilpotent a :=
    reducedPrincipalBlockElement_corner_augmentation_zero_isNilpotent
      d a haCenter hfactor haug
  let aZ : Subring.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G) :=
    ⟨a, haCenter⟩
  have hnilZ : IsNilpotent aZ := by
    rcases hnilA with ⟨n, hn⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    exact hn
  let br := BrauerMap.centralizerRestrictionCenterHom
    (BrauerBlockReduction.principalResidueField d) z hz
  have hnilBr : IsNilpotent (br aZ) := hnilZ.map br
  let x : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) := br aZ
  have hxmul : x * f = f := by
    simpa [x, br, aZ] using hrestrict
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
        (MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
          (Subgroup.centralizer ({z} : Set G))) =>
          (y : MonoidAlgebra (BrauerBlockReduction.principalResidueField d)
            (Subgroup.centralizer ({z} : Set G)))) hn
  calc
    f = x ^ n * f := (hxpow n).symm
    _ = 0 := by rw [hxn, zero_mul]

/-- Principal Brauer equality follows from a single augmentation-zero
relative-transfer witness for the extra local factor. -/
public theorem involutionPrincipalBrauerEquality_of_transferWitness
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (z : G) (hz : z * z = 1)
    (a : MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G)
    (haCenter : a ∈ Set.center
      (MonoidAlgebra (BrauerBlockReduction.principalResidueField d) G))
    (hfactor : a * BrauerBlockReduction.reducedPrincipalBlockElement d = a)
    (haug : groupAlgebraAugmentation
      (BrauerBlockReduction.principalResidueField d) G a = 0)
    (hrestrict :
      BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z a *
          (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.centralizer ({z} : Set G))) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G))) :
    CompatibleBrauerBlock.InvolutionPrincipalBrauerEquality d z := by
  have hzero :
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
          CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) = 0 :=
    eq_zero_of_brauerRestriction_mul_eq_self_of_corner_augmentation_zero
      d z hz a
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)))
      haCenter hfactor haug hrestrict
  change
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer ({z} : Set G)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z
  exact (sub_eq_zero.mp hzero).symm

end ModularBlock.PrimitiveCorner

