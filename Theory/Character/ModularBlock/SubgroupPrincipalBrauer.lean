module
public import Theory.Character.ModularBlock.SubgroupPrincipalBrauerData
public import Theory.Character.ModularBlock.PrincipalPrimitivity

/-!
# The local principal factor of a subgroup Brauer image

For a finite group and a 2-subgroup, the direct subgroup Brauer image of the
principal selector contains the compatible principal selector of the
centralizer as a factor. Both have augmentation one, so their product is a
nonzero central idempotent factor of the primitive local selector and equals
that selector. Subtracting the local selector therefore gives an orthogonal
central idempotent complement. The direct image equals the local selector
exactly when this complement vanishes.

Ported from the factor identity and its consequences in
`c3503435:glauberman_zStar/Submission/ZStar/SubgroupPrincipalBrauer.lean`.
The imported data module supplies the direct restriction, augmentation, and
complement definitions; principal primitivity supplies the essential
minimality argument. No additional hypotheses are imposed on the final
equality-versus-zero characterization.
-/

public section
noncomputable section
namespace ModularBlock.SubgroupPrincipalBrauer
open PrincipalBlockConstruction
universe u
attribute [local instance] Fintype.ofFinite

private theorem mul_ne_zero_of_augmentation_eq_one
    {R H : Type*} [CommRing R] [Nontrivial R] [Group H]
    {a b : MonoidAlgebra R H}
    (ha : groupAlgebraAugmentation R H a = 1)
    (hb : groupAlgebraAugmentation R H b = 1) : a * b ≠ 0 := by
  intro hzero
  have h := congrArg (groupAlgebraAugmentation R H) hzero
  rw [map_mul, ha, hb, one_mul, map_zero] at h
  exact one_ne_zero h

/-- The compatible principal block of `C_G(Q)` is a factor of the direct
`Q`-Brauer image of the ambient principal block.

Both idempotents have augmentation one, so their product is nonzero.  The
product is a central-idempotent factor of the centrally primitive local
principal selector and therefore equals that selector. -/
theorem localPrincipalBlockElement_mul_subgroupRestriction_eq_self
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) *
        DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
        (Subgroup.centralizer (Q : Set G)) := by
  let K := BrauerBlockReduction.principalResidueField d
  let C := Subgroup.centralizer (Q : Set G)
  let eLocal : MonoidAlgebra K C :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d C
  let eGQ : MonoidAlgebra K C :=
    DefectSupport.subgroupCentralizerRestriction K Q
      (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hLocalPrimitive : IsCentrallyPrimitive eLocal := by
    simpa [eLocal, K, C] using
      BlockPrimitivity.localPrincipalBlockElementInAmbientResidue_isCentrallyPrimitive d C
  have hGQCenter : eGQ ∈ Set.center (MonoidAlgebra K C) := by
    simpa [eGQ, K, C] using
      reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q
  have hGQIdem : IsIdempotentElem eGQ := by
    simpa [eGQ, K, C] using
      reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ
  have hProductNe : eLocal * eGQ ≠ 0 := by
    apply mul_ne_zero_of_augmentation_eq_one
    · simpa [eLocal, K, C] using
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_augmentation_eq_one
          d C
    · simpa [eGQ, K, C] using
        reducedPrincipalBlockElement_subgroupRestriction_augmentation_eq_one
          d Q hQ
  have hCommute : Commute eLocal eGQ :=
    (Semigroup.mem_center_iff.mp hLocalPrimitive.1 eGQ).symm
  have hProductCenter : eLocal * eGQ ∈ Set.center (MonoidAlgebra K C) :=
    Set.mul_mem_center hLocalPrimitive.1 hGQCenter
  have hProductIdem : IsIdempotentElem (eLocal * eGQ) :=
    IsIdempotentElem.mul_of_commute hCommute
      hLocalPrimitive.2.1 hGQIdem
  have hProductFactor : (eLocal * eGQ) * eLocal = eLocal * eGQ := by
    calc
      (eLocal * eGQ) * eLocal = eLocal * (eGQ * eLocal) :=
        mul_assoc _ _ _
      _ = eLocal * (eLocal * eGQ) := by rw [hCommute.eq.symm]
      _ = (eLocal * eLocal) * eGQ := (mul_assoc _ _ _).symm
      _ = eLocal * eGQ := by rw [hLocalPrimitive.2.1.eq]
  change eLocal * eGQ = eLocal
  exact hLocalPrimitive.2.2.2 (eLocal * eGQ)
    hProductCenter hProductIdem hProductFactor hProductNe

theorem extraBrauerFactor_isIdempotent
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    IsIdempotentElem (extraBrauerFactor d Q) := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  have hcomm : eGQ * eLocal = eLocal := by
    have hc := Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) eLocal
    exact hc.symm.trans hfactor
  change IsIdempotentElem (eGQ - eLocal)
  exact IsIdempotentElem.sub
    (CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer (Q : Set G)))
    (reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ)
    hfactor hcomm

theorem extraBrauerFactor_mul_local_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    extraBrauerFactor d Q *
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) = 0 := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  have hcomm : eGQ * eLocal = eLocal := by
    have hc := Semigroup.mem_center_iff.mp
      (reducedPrincipalBlockElement_subgroupRestriction_mem_center d Q) eLocal
    exact hc.symm.trans hfactor
  change (eGQ - eLocal) * eLocal = 0
  rw [sub_mul, hcomm,
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue_isIdempotent
      d (Subgroup.centralizer (Q : Set G)), sub_self]

theorem extraBrauerFactor_mul_subgroupRestriction_eq_self
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G)
    (hQ : IsPGroup 2 Q) :
    extraBrauerFactor d Q *
        DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
      extraBrauerFactor d Q := by
  let eLocal :=
    CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
      (Subgroup.centralizer (Q : Set G))
  let eGQ := DefectSupport.subgroupCentralizerRestriction
    (BrauerBlockReduction.principalResidueField d) Q
    (BrauerBlockReduction.reducedPrincipalBlockElement d)
  have hfactor : eLocal * eGQ = eLocal := by
    simpa [eLocal, eGQ] using
      localPrincipalBlockElement_mul_subgroupRestriction_eq_self d Q hQ
  change (eGQ - eLocal) * eGQ = eGQ - eLocal
  rw [sub_mul,
    reducedPrincipalBlockElement_subgroupRestriction_isIdempotent d Q hQ,
    hfactor]

/-- The direct subgroup Brauer image equals its compatible principal factor
exactly when its complementary factor vanishes. -/
theorem subgroupRestriction_eq_local_iff_extra_eq_zero
    {G : Type u} [Group G] [Finite G]
    (d : PrincipalCongruenceBlockData G) (Q : Subgroup G) :
    DefectSupport.subgroupCentralizerRestriction
          (BrauerBlockReduction.principalResidueField d) Q
          (BrauerBlockReduction.reducedPrincipalBlockElement d) =
        CompatibleBrauerBlock.localPrincipalBlockElementInAmbientResidue d
          (Subgroup.centralizer (Q : Set G)) ↔
      extraBrauerFactor d Q = 0 := by
  rw [extraBrauerFactor, sub_eq_zero]

end ModularBlock.SubgroupPrincipalBrauer
