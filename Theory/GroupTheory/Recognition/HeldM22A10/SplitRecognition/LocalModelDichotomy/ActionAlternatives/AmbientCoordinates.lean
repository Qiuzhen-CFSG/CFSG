module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.ActionAlternatives.Coordinates
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.LocalModelDichotomy.BinaryReduction

/-!
# Janko coordinates inside the original ambient group

The binary basis is mapped through the actual elementary kernel, and the
four-letter permutations are mapped through the supplied complement. Both
maps are injective; the basis image is exactly the ambient image of the
kernel. The coordinate identities become literal right-conjugation formulas
in G, using `BinaryReduction.binaryAction_apply_kernel`.

These maps connect the matrix cases to the ambient exclusions in Janko,
*A characterization of the Mathieu simple groups, I*, J. Algebra 9 (1968),
Section 1, pp.2–3, DOI 10.1016/0021-8693(68)90002-1. A coordinate witness is
an explicit input. No exhaustion or exclusion is asserted here.
-/

namespace Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (K : Subgroup D.centralizer) (hK : D.kernel.IsComplement' K)

/-- The actual complement embedding with the fixed four-letter labels. -/
@[expose] public noncomputable def jankoAmbientComplement : SymmetricFour →* G :=
  D.centralizer.subtype.comp (K.subtype.comp (D.complementEquiv K hK).symm.toMonoidHom)

/-- The complement coordinates preserve distinct group elements. -/
public theorem jankoAmbientComplement_injective :
    Function.Injective (jankoAmbientComplement D K hK) :=
  D.centralizer.subtype_injective.comp
    (K.subtype_injective.comp (D.complementEquiv K hK).symm.injective)

variable [Finite G]

namespace JankoCoordinates
variable {k : JankoCase} (R : JankoCoordinates (D.binaryAction K hK) k)

/-- Source vectors embedded through the original elementary kernel. -/
@[expose] public noncomputable def ambientBasis : BinaryFour →* G :=
  D.centralizer.subtype.comp (D.kernel.subtype.comp
    (D.kernelBinaryEquiv.symm.toMonoidHom.comp R.basis.toMonoidHom))

/-- The source vectors are distinct in the original ambient group. -/
public theorem ambientBasis_injective : Function.Injective (R.ambientBasis D K hK) :=
  D.centralizer.subtype_injective.comp (D.kernel.subtype_injective.comp
    (D.kernelBinaryEquiv.symm.injective.comp R.basis.injective))

/-- The image is the actual kernel, with its two subgroup inclusions. -/
public theorem ambientBasis_range :
    (R.ambientBasis D K hK).range = D.kernel.map D.centralizer.subtype := by
  apply le_antisymm
  · rintro x ⟨v, rfl⟩
    exact ⟨D.kernelBinaryEquiv.symm (R.basis v),
      (D.kernelBinaryEquiv.symm (R.basis v)).property, rfl⟩
  · rintro x ⟨f, hf, rfl⟩
    refine ⟨R.basis.symm (D.kernelBinaryEquiv ⟨f, hf⟩), ?_⟩
    change ((D.kernelBinaryEquiv.symm
      (R.basis (R.basis.symm (D.kernelBinaryEquiv ⟨f, hf⟩))) : D.centralizer) : G) = _
    rw [MulEquiv.apply_symm_apply, MulEquiv.symm_apply_apply]
    rfl

/-- A coordinate action identity gives the literal source right conjugation. -/
public theorem ambient_conjugation_of_action (s : SymmetricFour) (v w : BinaryFour)
    (h : D.binaryAction K hK s⁻¹ (R.basis v) = R.basis w) :
    (jankoAmbientComplement D K hK s)⁻¹ * R.ambientBasis D K hK v *
        jankoAmbientComplement D K hK s = R.ambientBasis D K hK w := by
  have hf : D.complementAction K ((D.complementEquiv K hK).symm s⁻¹)
      (D.kernelBinaryEquiv.symm (R.basis v)) = D.kernelBinaryEquiv.symm (R.basis w) := by
    apply D.kernelBinaryEquiv.injective
    rw [← D.binaryAction_apply_kernel K hK, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact h
  have hg := congrArg (fun x : D.kernel => ((x : D.centralizer) : G)) hf
  change (((D.complementEquiv K hK).symm s⁻¹ : D.centralizer) : G) *
      R.ambientBasis D K hK v *
      (((D.complementEquiv K hK).symm s⁻¹ : D.centralizer) : G)⁻¹ = _ at hg
  change (((D.complementEquiv K hK).symm s : D.centralizer) : G)⁻¹ *
      R.ambientBasis D K hK v * (((D.complementEquiv K hK).symm s : D.centralizer) : G) =
    ((D.kernelBinaryEquiv.symm (R.basis w) : D.centralizer) : G)
  simpa only [map_inv, Subgroup.coe_inv, inv_inv] using hg

/-- The source matrix of `a` acts by right conjugation in G. -/
public theorem ambient_conjugation_a (v : BinaryFour) :
    (jankoAmbientComplement D K hK jankoA)⁻¹ * R.ambientBasis D K hK v *
        jankoAmbientComplement D K hK jankoA =
      R.ambientBasis D K hK (jankoSourceA k v) := by
  apply R.ambient_conjugation_of_action
  have hinv : jankoA⁻¹ = jankoA := by decide +kernel
  rw [hinv]
  exact R.action_a v

/-- The source matrix of `b` acts by right conjugation in G. -/
public theorem ambient_conjugation_b (v : BinaryFour) :
    (jankoAmbientComplement D K hK jankoB)⁻¹ * R.ambientBasis D K hK v *
        jankoAmbientComplement D K hK jankoB =
      R.ambientBasis D K hK (jankoSourceB k v) := by
  apply R.ambient_conjugation_of_action
  have hinv : jankoB⁻¹ = jankoB := by decide +kernel
  rw [hinv]
  exact R.action_b v

/-- The source matrix of `c` acts by right conjugation in G. -/
public theorem ambient_conjugation_c (v : BinaryFour) :
    (jankoAmbientComplement D K hK jankoC)⁻¹ * R.ambientBasis D K hK v *
        jankoAmbientComplement D K hK jankoC =
      R.ambientBasis D K hK (jankoSourceC v) :=
  R.ambient_conjugation_of_action D K hK jankoC v _ (R.action_c v)

/-- The source matrix of `d` acts by right conjugation in G. -/
public theorem ambient_conjugation_d (v : BinaryFour) :
    (jankoAmbientComplement D K hK jankoD)⁻¹ * R.ambientBasis D K hK v *
        jankoAmbientComplement D K hK jankoD =
      R.ambientBasis D K hK (jankoSourceD k v) := by
  apply R.ambient_conjugation_of_action
  have hinv : jankoD⁻¹ = jankoD := by decide +kernel
  rw [hinv]
  exact R.action_d v

end JankoCoordinates
end Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
