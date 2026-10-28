module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointHom
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Generation.FixedOpposition.AmbientNormalizer.SimpleReflections.CorootRealization.Geometry.PointExistence.Relations

/-!
# Constructing simple-root SL₂ point maps from intrinsic relations

The two-cell matrix construction sends the standard upper and lower curves
to a jointly chosen pair of actual root parametrizations. The map lands in
`oppositePairGeneratedSubgroup` throughout; no concrete identification of the
ambient D4 group and no regularity theorem is used.

The conditional assembly isolates two geometric obligations: choosing curves
whose three-factor word swaps them, and proving multiplicativity and square
scaling of their diagonal words. This module does not assert that either
obligation follows from `Geometry`; unconditional point-map existence still
requires both proofs.

Sources: GLS3, Theorem 1.9.5(d), Remarks 1.9.6 and the formulas in §1.12,
`refs/KGroup/GLS3/Chapter1.tex`; Steinberg §6,
`refs/KGroup/GLS3/Chapter2St2.tex`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {S : Geometry K} {i : Fin 4}

/-- Construct the actual SL₂ point homomorphism from the intrinsic curve identities. -/
public noncomputable def SimpleRootSL2Parameters.pointHom_of_relations
    (P : SimpleRootSL2Parameters S i) (hP : P.Relations) : SimpleRootSL2PointHom S i where
  plus := P.plus
  minus := P.minus
  map := (P.presentation_of_relations hP).toHom.comp (slPointMulEquiv 2).toMonoidHom
  upper := by
    intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change _ = (P.presentation_of_relations hP).toHom
      (slPointMulEquiv 2 (standardSL2UpperMorphism.onPoints (kPlusPoint t)))
    rw [slPointMulEquiv_apply]
    change _ = (P.presentation_of_relations hP).toHom (BinaryRankOne.upper t)
    rw [BinaryRankOne.Relations.toHom_upper, P.upper_eq]
  lower := by
    intro s
    obtain ⟨t, rfl⟩ : ∃ t, kPlusPoint t = s := ⟨_, kPlusPoint_coordinate s⟩
    change _ = (P.presentation_of_relations hP).toHom
      (slPointMulEquiv 2 (standardSL2LowerMorphism.onPoints (kPlusPoint t)))
    rw [slPointMulEquiv_apply]
    change _ = (P.presentation_of_relations hP).toHom (BinaryRankOne.lower t)
    rw [BinaryRankOne.Relations.toHom_lower, hP.2, P.lower_eq]

/-- Final assembly from the two separate geometric results. Both premises must
be discharged before claiming unconditional simple-root point-map existence. -/
public theorem nonempty_simpleRootSL2PointHom_of_swap_and_diagonal
    (hswap : ∃ P : SimpleRootSL2Parameters S i, P.WeylSwaps)
    (hdiag : ∀ P : SimpleRootSL2Parameters S i, P.WeylSwaps → P.DiagonalRelations) :
    Nonempty (SimpleRootSL2PointHom S i) := by
  obtain ⟨P, hP⟩ := hswap
  exact ⟨P.pointHom_of_relations ⟨hdiag P hP, hP⟩⟩

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ClassBound.FixedOpposition.AmbientNormalizer.CorootRealization
