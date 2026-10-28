module

public import Theory.Representation.Mathieu.M24Degree44Displacement.FiveSpace.Placement.Contracts
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.CodePair
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels.FortyFour

/-!
# Four binary Mathieu models with native Golay exterior sections

The eleven-dimensional code and cocode are absolutely irreducible and
inequivalent. Their existing coordinate models are obtained by scalar
extension followed by a linear equivalence; absolute irreducibility survives
both operations, including when the scalar field is binary.

The other two models are the native code exterior contraction kernel and its
dual, in forty-four coordinates. The existing density and trace proofs give
absolute irreducibility and inequivalence, and their literal section maps
place them in the code and cocode exterior squares. Dimension separates the
two pairs. Reindexing their union by `Fin 4` supplies `BinarySectionModels`,
discharging the concrete small-model premise of
`golayExteriorPlacement_of_binary_models` and
`fiveFixedSpaceBound_of_binary_section_models`.

Sources: G. D. James, The modular characters of the Mathieu groups,
J. Algebra 27 (1973), 57–111; Guralnick–Malle, Classification of 2F-modules I,
Proposition 5.1, M₂₄ paragraph, manuscript p.17. The native constructions and
checked matrix comparisons are reused from `AbsoluteSpectrum.SmallModels`.
-/

public section
noncomputable section
namespace Representation.MathieuM24Degree44.FiveSpace.Placement
open Sporadic.Mathieu
open Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.SmallModels

private theorem absolute_of_equiv {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    {ρ : Representation F M24 V} {σ : Representation F M24 W}
    (e : ρ.Equiv σ) (h : ρ.IsAbsolutelyIrreducible) : σ.IsAbsolutelyIrreducible := by
  exact ⟨(RepEquiv.ofRepresentationEquiv
    (BinaryFieldDescent.extendEquiv (K := AlgebraicClosure F) e)).irreducible_euqiv.mp
      h.irreducible_of_closure⟩

private theorem elevenModels_absolute (F : Type*) [Field F] [CharP F 2] (i : Fin 2) :
    (![code F, cocode F] i).IsAbsolutelyIrreducible := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  fin_cases i
  · exact absolute_of_equiv (codeEquiv F)
      ((IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars
        MathieuCode.codeRepresentation F).mpr MathieuCode.code_isAbsolutelyIrreducible)
  · exact absolute_of_equiv (cocodeEquiv F)
      ((IsAbsolutelyIrreducible.isAbsolutelyIrreducible_iff_extendScalars
        MathieuCode.cocodeRepresentation F).mpr MathieuCode.cocode_isAbsolutelyIrreducible)

private theorem binaryElevenModelsExist :
    ∃ ρ : Fin 2 → Representation (ZMod 2) M24 (Fin 11 → ZMod 2),
      (∀ i, (ρ i).IsAbsolutelyIrreducible) ∧
      Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
  refine ⟨![code (ZMod 2), cocode (ZMod 2)], ?_, ?_⟩
  · exact elevenModels_absolute (ZMod 2)
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact code_cocode_coordinates_inequivalent (ZMod 2)
    · exact ⟨fun e => (code_cocode_coordinates_inequivalent (ZMod 2)).false e.symm⟩
    · exact (hij rfl).elim

/-- Four actual pairwise inequivalent absolutely irreducible binary M₂₄
modules, of degrees eleven or forty-four. Every degree-forty-four member is a
surjective equivariant image of a native Golay exterior invariant subspace. -/
theorem binarySectionModels : BinarySectionModels := by
  obtain ⟨α, hαabs, hα⟩ := binaryElevenModelsExist
  let d : Fin 2 ⊕ Fin 2 → ℕ := fun i => match i with
    | .inl _ => 11
    | .inr _ => 44
  let ρ : ∀ i : Fin 2 ⊕ Fin 2, Representation (ZMod 2) M24 (Fin (d i) → ZMod 2) :=
    fun i => match i with
    | .inl j => α j
    | .inr j => binaryFortyFourModels j
  have habs : ∀ i, (ρ i).IsAbsolutelyIrreducible := by
    rintro (i | i)
    · exact hαabs i
    · exact binaryFortyFourModels_absolute FortyFour.kernel_isAbsolutelyIrreducible i
  have hneq : Pairwise fun i j => IsEmpty ((ρ i).Equiv (ρ j)) := by
    intro i j hij
    constructor
    intro e
    have hdim := e.toLinearEquiv.finrank_eq
    rcases i with i | i <;> rcases j with j | j
    · exact (hα (fun h => hij (congrArg Sum.inl h))).false e
    · simp only [d, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      omega
    · simp only [d, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hdim
      omega
    · exact (binaryFortyFourModels_inequivalent FortyFour.kernel_dual_inequivalent
        (fun h => hij (congrArg Sum.inr h))).false e
  let f : Fin 4 ≃ Fin 2 ⊕ Fin 2 := (finSumFinEquiv (m := 2) (n := 2)).symm
  refine ⟨fun i => d (f i), fun i => ρ (f i), fun i => habs (f i), ?_, ?_, ?_⟩
  · intro i j hij
    exact hneq (fun h => hij (f.injective h))
  · intro i
    change d (f i) = 11 ∨ d (f i) = 44
    rcases f i with j | j
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro i hi
    change IsSectionOf (ρ (f i)) codeExterior ∨ IsSectionOf (ρ (f i)) cocodeExterior
    change d (f i) = 44 at hi
    rcases hfi : f i with j | j
    · simp only [hfi, d] at hi
      omega
    · exact binaryFortyFourModels_sections j

end Representation.MathieuM24Degree44.FiveSpace.Placement
