module

public import Theory.Character.ModularBlock.NagaoComplement
public import Theory.Character.ModularBlock.CompatibleBrauerBlock
public import Theory.Character.ModularBlock.ResidueKernel

/-!
# The principal Nagao complement

The complementary idempotent between the ambient localized principal
selector and the compatible principal selector in an involution centralizer
is fixed by conjugation. Under the local factor identity, its reduced
centralizer restriction equals the ambient Brauer image minus the local
principal selector. Hence its coefficients at the conjugation fixed points
lie in the localization's maximal ideal exactly when those two selectors
are equal. This is the precise input needed by the projective Nagao range
criterion; the factor identity alone does not imply coefficient vanishing.

The proof combines the generic complement-restriction formula, compatibility
of local selector reduction, and the elementary residue-kernel lemma.
The principal complement is exposed because subsequent range constructions
use its exact group-algebra element. Ported from
`public/lean-eval/glauberman_zStar`, `Submission/ZStar/NagaoComplement.lean`
(revision `c3503435`), preserving its principal-block hypotheses.
-/

@[expose] public section

noncomputable section

namespace Glauberman.ZStar.NagaoComplement

open ModularBlock ModularBlock.NagaoComplement

universe u v

attribute [local instance] Fintype.ofFinite

open PrincipalBlockConstruction

private instance principalPrime_isPrime
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) : d.primeIdeal.IsPrime :=
  d.primeIdeal_maximal.isPrime

/-- The concrete complement between the ambient localized principal-block
selector and the compatible local principal selector. -/
noncomputable def principalComplement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    MonoidAlgebra (Localization.AtPrime d.primeIdeal) G :=
  complement z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))

theorem principalComplement_isIdempotent
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    IsIdempotentElem (principalComplement d z) := by
  exact complement_isIdempotent z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))
    (BlockOrthogonality.localizedPrincipalBlockElement_isIdempotent d)
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_isIdempotent
      d (Subgroup.centralizer ({z} : Set G)))

theorem conjugation_principalComplement
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G) :
    BrauerKernelRelativeTrace.conjugation
        (Localization.AtPrime d.primeIdeal) z (principalComplement d z) =
      principalComplement d z := by
  exact conjugation_complement z
    (BlockOrthogonality.localizedPrincipalBlockElement d)
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G)))
    (BlockOrthogonality.localizedPrincipalBlockElement_mem_center d)

/-- Assuming only the valid local factor identity, reduction of the concrete
Nagao complement restricts to `eBrauer - eLocal`.  This records exactly the
additional-local-factor obstruction. -/
theorem centralizerRestriction_reduce_principalComplement_eq_sub
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    BrauerMap.centralizerRestriction
        (BrauerBlockReduction.principalResidueField d) z
        (MonoidAlgebra.mapRingHom G
          (BrauerBlockReduction.localizationToResidue d)
          (principalComplement d z)) =
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
  let e := BlockOrthogonality.localizedPrincipalBlockElement d
  let b :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization d
      (Subgroup.centralizer ({z} : Set G))
  have hE :
      BrauerMap.centralizerRestriction
          (BrauerBlockReduction.principalResidueField d) z
          (MonoidAlgebra.mapRingHom G
            (BrauerBlockReduction.localizationToResidue d) e) =
        BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z := by
    rfl
  have hb :
      MonoidAlgebra.mapRingHom
          (Subgroup.centralizer ({z} : Set G))
          (BrauerBlockReduction.localizationToResidue d) b =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
    exact CompatibleBrauerBlock.localPrincipalBlockElementInAmbientLocalization_reduce
      d (Subgroup.centralizer ({z} : Set G))
  have h := centralizerRestriction_mapRingHom_complement_eq_sub
    (BrauerBlockReduction.localizationToResidue d) z e b
    (by simpa [hE] using
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement_mem_center d z)
    (by simpa [hb, hE] using hfactor)
  simpa [principalComplement, e, b, hE, hb] using h

/-- Coefficientwise form of the preceding obstruction identity.  A group
element fixed under conjugation by `z` is canonically an element of
`C_G(z)`. -/
theorem localizationToResidue_principalComplement_coeff
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z x : G)
    (hfixed : z⁻¹ * x * z = x)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    let xC : Subgroup.centralizer ({z} : Set G) :=
      ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr (by
        calc
          x * z = z * (z⁻¹ * x * z) := by group
          _ = z * x := by rw [hfixed])⟩
    BrauerBlockReduction.localizationToResidue d ((principalComplement d z).coeff x) =
      (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))).coeff xC := by
  let xC : Subgroup.centralizer ({z} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc
        x * z = z * (z⁻¹ * x * z) := by group
        _ = z * x := by rw [hfixed])⟩
  have h := congrArg (fun q : MonoidAlgebra
      (BrauerBlockReduction.principalResidueField d)
      (Subgroup.centralizer ({z} : Set G)) => q.coeff xC)
    (centralizerRestriction_reduce_principalComplement_eq_sub d z hfactor)
  simpa [xC, BrauerMap.centralizerRestriction_apply,
    MonoidAlgebra.coeff_mapRingHom] using h

/-- For the local-principal complement, the fixed-coefficient hypothesis
needed by `ExactRelativeTrace` is equivalent to the *full* equality between
the ambient Brauer image and the compatible local principal selector.  Thus
the weaker factor identity cannot by itself feed the exact-trace theorem. -/
theorem fixed_coeff_mem_maximalIdeal_principalComplement_iff
    {G : Type v} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (z : G)
    (hfactor :
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G)) *
          BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G))) :
    (∀ x : G, z⁻¹ * x * z = x →
        (principalComplement d z).coeff x ∈
          IsLocalRing.maximalIdeal (Localization.AtPrime d.primeIdeal)) ↔
      BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer ({z} : Set G)) := by
  constructor
  · intro hcoeff
    ext xC
    let x : G := xC
    have hxcomm : (xC : G) * z = z * (xC : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp xC.property
    have hfixed : z⁻¹ * x * z = x := by
      dsimp [x]
      calc
        z⁻¹ * (xC : G) * z = z⁻¹ * ((xC : G) * z) := mul_assoc _ _ _
        _ = z⁻¹ * (z * (xC : G)) := by rw [hxcomm]
        _ = (xC : G) := by simp
    have hmem := hcoeff x hfixed
    have hzero :
        BrauerBlockReduction.localizationToResidue d
            ((principalComplement d z).coeff x) = 0 := by
      rw [BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit]
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hmem)
    have hvalue := localizationToResidue_principalComplement_coeff
      d z x hfixed hfactor
    have hvalue' :
        BrauerBlockReduction.localizationToResidue d
            ((principalComplement d z).coeff x) =
          (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
            CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
              (Subgroup.centralizer ({z} : Set G))).coeff xC := by
      simpa [x] using hvalue
    have hsub :
        (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z).coeff xC -
          (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
            (Subgroup.centralizer ({z} : Set G))).coeff xC = 0 := by
      calc
        _ = (BrauerBlockReduction.involutionBrauerPrincipalBlockElement d z -
              CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
                (Subgroup.centralizer ({z} : Set G))).coeff xC :=
            rfl
        _ = BrauerBlockReduction.localizationToResidue d
              ((principalComplement d z).coeff x) := hvalue'.symm
        _ = 0 := hzero
    exact sub_eq_zero.mp hsub
  · intro heq x hfixed
    rw [IsLocalRing.mem_maximalIdeal]
    change ¬ IsUnit ((principalComplement d z).coeff x)
    rw [← BlockPrimitivity.localizationToResidue_eq_zero_iff_not_isUnit]
    rw [localizationToResidue_principalComplement_coeff d z x hfixed hfactor,
      heq, sub_self]
    rfl


end Glauberman.ZStar.NagaoComplement

