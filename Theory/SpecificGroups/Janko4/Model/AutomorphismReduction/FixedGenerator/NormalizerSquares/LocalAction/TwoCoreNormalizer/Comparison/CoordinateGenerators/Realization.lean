module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.RawAction
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.NormalClosure
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.ActionCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.Realization.CoreIdentification

/-!
# Transporting the max2 word coordinates to the actual two-core quotient

An equality of the image of the seed normal closure N with Q = O₂(C)
induces an explicit multiplicative equivalence N ≃ Q. It intertwines the
actual conjugation actions. The proved intrinsic-center calculation then
identifies the image of <t> with Z(Q), giving N/<t> ≃ Q/Z(Q). Composing the
inverse of this equivalence with the published binary coordinates realizes
both required left-column actions on the actual two-core quotient.

The raw action is irreducible, so O₂(H) acts trivially on N/<t>. Extraspecial
commutator duality, the exponent-two condition on C_H(N), full local generation,
and the order-two center of Q then identify N with Q. The final theorem combines
these results to realize the coordinates under exactly those three explicit
local hypotheses. Their discharge belongs to the source-theorem assembly;
no additional centralizer-control hypothesis is needed for this realization.

Source motivation: GLS3, Table 5.3i, printed p.270,
`refs/KGroup/GLS3/Chapter5(sec3-).tex`. All word coordinates and matrix
conventions come from the cited max2 certificates in `Realization.NormalClosure`.
-/

@[expose] public section

open scoped Matrix
set_option maxRecDepth 4000

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
open TwoCoreCentralizerData
namespace Realization

/-- The actual normal closure is isomorphic to its image, identified with Q. -/
noncomputable def normalClosureEquiv
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) :
    localNormalClosure ≃* involutionTwoCore :=
  (localNormalClosure.equivMapOfInjective localSubgroup.subtype Subtype.val_injective).trans
    (MulEquiv.subgroupCongr hN)

/-- This equivalence preserves the element in the literal centralizer. -/
theorem normalClosureEquiv_coe
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore)
    (n : localNormalClosure) :
    (normalClosureEquiv hN n : involutionCentralizer) = (n : localSubgroup) := rfl

/-- Compatibility with the two actual left-conjugation actions. -/
theorem normalClosureEquiv_action
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore)
    (g : localSubgroup) (n : localNormalClosure) :
    normalClosureEquiv hN (localNormalClosureAction g n) =
      involutionTwoCoreAction (g : involutionCentralizer) (normalClosureEquiv hN n) := by
  apply Subtype.ext
  rfl

/-- The quotient subgroup maps onto the full intrinsic center of Q. -/
theorem normalClosureEquiv_map_centralPowers
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) :
    OuterImageComparison.centralPowers.map (normalClosureEquiv hN).toMonoidHom =
      Subgroup.center involutionTwoCore := by
  rw [← normalClosure_center]
  let e := normalClosureEquiv hN
  change (Subgroup.center localNormalClosure).map e.toMonoidHom = _
  ext q
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro m
    obtain ⟨z, rfl⟩ := e.surjective m
    exact (map_mul e z n).symm.trans
      ((congrArg e (Subgroup.mem_center_iff.mp hn z)).trans (map_mul e n z))
  · intro hq
    refine ⟨e.symm q, ?_, e.apply_symm_apply q⟩
    change e.symm q ∈ Subgroup.center localNormalClosure
    rw [Subgroup.mem_center_iff]
    intro n
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using
      Subgroup.mem_center_iff.mp hq (e n)

/-- Identification of the literal quotients N/<t> and Q/Z(Q). -/
noncomputable def centralQuotientEquiv
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) :
    OuterImageComparison.CentralQuotient ≃* TwoCoreComparison.CentralQuotient :=
  QuotientGroup.congr OuterImageComparison.centralPowers
    (Subgroup.center involutionTwoCore) (normalClosureEquiv hN)
    (normalClosureEquiv_map_centralPowers hN)

/-- The quotient identification agrees on every representative. -/
theorem centralQuotientEquiv_projection
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore)
    (n : localNormalClosure) :
    centralQuotientEquiv hN (OuterImageComparison.projection n) =
      QuotientGroup.mk' (Subgroup.center involutionTwoCore) (normalClosureEquiv hN n) :=
  QuotientGroup.congr_mk' _ _ _ _ n

/-- Binary coordinates on the actual two-core quotient. -/
noncomputable def realizedCoordinates
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) :
    TwoCoreComparison.Coordinates :=
  (centralQuotientEquiv hN).symm.trans OuterImageComparison.coordinates

/-- Coordinates agree with the word coordinates on corresponding representatives. -/
theorem vector_realizedCoordinates
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore)
    (n : localNormalClosure) :
    vector (realizedCoordinates hN) (normalClosureEquiv hN n) =
      (OuterImageComparison.coordinates (OuterImageComparison.projection n)).toAdd := by
  change (OuterImageComparison.coordinates ((centralQuotientEquiv hN).symm
    (QuotientGroup.mk' (Subgroup.center involutionTwoCore) (normalClosureEquiv hN n)))).toAdd = _
  rw [← centralQuotientEquiv_projection, MulEquiv.symm_apply_apply]

/-- Both required raw actions transported to the actual two-core quotient. -/
noncomputable def rawCoordinatesOfNormalClosureEq
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) : RawCoordinates where
  coordinates := realizedCoordinates hN
  actionX := by
    intro q
    obtain ⟨n, rfl⟩ := (normalClosureEquiv hN).surjective q
    change rawMatrixX *ᵥ vector (realizedCoordinates hN) (normalClosureEquiv hN n) =
      vector (realizedCoordinates hN)
        (involutionTwoCoreAction (subgroupX : involutionCentralizer) (normalClosureEquiv hN n))
    rw [← normalClosureEquiv_action, vector_realizedCoordinates, vector_realizedCoordinates]
    exact normalClosure_actionX n
  actionY := by
    intro q
    obtain ⟨n, rfl⟩ := (normalClosureEquiv hN).surjective q
    change rawMatrixY *ᵥ vector (realizedCoordinates hN) (normalClosureEquiv hN n) =
      vector (realizedCoordinates hN)
        (involutionTwoCoreAction (subgroupY : involutionCentralizer) (normalClosureEquiv hN n))
    rw [← normalClosureEquiv_action, vector_realizedCoordinates, vector_realizedCoordinates]
    exact normalClosure_actionY n

end Realization

/-- Transport the word coordinates through an identification with the actual two-core. -/
theorem nonempty_rawCoordinates_of_normalClosure_eq
    (hN : localNormalClosure.map localSubgroup.subtype = involutionTwoCore) :
    Nonempty RawCoordinates := ⟨Realization.rawCoordinatesOfNormalClosureEq hN⟩

/-- Realize the raw left-column actions on the actual two-core central quotient. -/
theorem nonempty_rawCoordinates
    (hcenter : Nat.card (Subgroup.center involutionTwoCore) = 2)
    (hgen : localSubgroup = ⊤)
    (hpow : ∀ z ∈ Subgroup.centralizer (localNormalClosure : Set localSubgroup), z ^ 2 = 1) :
    Nonempty RawCoordinates :=
  nonempty_rawCoordinates_of_normalClosure_eq
    (Realization.normalClosureImage_eq_twoCore_of_quotient_kernel
      Realization.localTwoCore_le_quotientAction_ker hcenter hgen hpow)

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
