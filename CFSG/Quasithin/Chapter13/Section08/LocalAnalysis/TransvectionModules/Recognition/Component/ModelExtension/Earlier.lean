module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.SourceSetup
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.RecognitionStep.Models
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.ModelExtension.ChiefQuotient
public import Theory.AtlasPort.OtherSporadic.Codes.HexacodeConjugation
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model

/-!
# Exact earlier implications for the component-extension assembly

The consumed clauses of 13.7.6(1),(3) are stated universally over H, K,
the degree, the intrinsic component marking and the actual section action.
The six-letter clause retains the chief factors on U_H, as printed; the
covered local conclusion is an equivalence to the concrete hexacode group.
The point/plane markings not consumed by 13.8.5 are not claimed here.
The centralizer identity is F.9.2(3), in the notation of 13.5.8 and p.946.

These definitions specify earlier-theorem inputs, not proofs of those
results. The assembly constructs every application premise from the
standing setup and the recognized section. In particular it must still
construct both alternating full modules and their full H* actions.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
F.9.2(3), p.317; 13.7.6(1),(3), pp.938–940; 13.8.5, p.947.
-/

@[expose] public section
open Subgroup Representation
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open RecognitionStep
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full natural action of the actual projective matrix group L₄(2).
The matrix-coset comparison is proved in `BinaryLinear.OuterCyclic.Model`. -/
noncomputable def projectiveRepresentation (n : ℕ) (hn : 0 < n) :
    Representation (ZMod 2) (Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2))
      (Fin n → ZMod 2) :=
  (linearRepresentation n).comp
    (BinaryLinear.OuterCyclic.projectiveEquivLinear hn).toMonoidHom

/-- The degree-four specialization. -/
noncomputable abbrev projectiveFourRepresentation :=
  projectiveRepresentation 4 (by decide)

/-- The exact previously recognized alternatives, on the literal section
and with its intrinsic K/O₂(K) marking. No full-module conclusion is assumed. -/
def RecognizedSection (H K V₃ V₁ : Subgroup G) (hKH : K ≤ H)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  (∃ n : ℕ, 3 ≤ n ∧
    ∃ eK : (K ⧸ pCore 2 K) ≃* BinaryLinear.GL (Fin n → ZMod 2),
      HasSectionModel H V₃ V₁ ρ K hKH (linearRepresentation n) eK) ∨
  (∃ n : ℕ, 5 ≤ n ∧
    ∃ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) eK)

/-- Earlier source results, all universally quantified before selecting the
component or its model. No instance of 13.8.5 is an input. -/
structure EarlierInputs (T : Sylow 2 G) (L V V₁ V₂ V₃ M G₁ : Subgroup G) : Prop where
  centralizer : ∀ (_d : LocalSetup T L V V₁ V₂ V₃ M G₁) (H : Subgroup G),
    H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M →
    commutatorPreimage H (Source.UH H V₃) V₁ = Source.QH H
  linear : ∀ (_d : LocalSetup T L V V₁ V₂ V₃ M G₁) (H : Subgroup G),
    H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M →
    ∀ [_hn : (V₁.subgroupOf (Source.UH H V₃)).Normal]
      [_ha : IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
      (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (K : Subgroup G) (hKH : K ≤ H), (K.subgroupOf H).IsCComponent →
      ∀ (n : ℕ) (hn : 3 ≤ n),
      ∀ eK : (K ⧸ pCore 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) (ZMod 2),
      HasSectionModel H V₃ V₁ ρ K hKH (projectiveRepresentation n (by omega)) eK →
      n = 4 ∧ HasActionModel ρ projectiveFourRepresentation ∧
        Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
  alternating : ∀ (_d : LocalSetup T L V V₁ V₂ V₃ M G₁)
    (H : Subgroup G) (hH : H ∈ Source.Hz (sourceOne L T V₁) (T : Subgroup G) G₁ M),
    ∀ [_hu : IsElementaryAbelian 2 (Source.UH H V₃)]
      [_hn : (V₁.subgroupOf (Source.UH H V₃)).Normal]
      [_ha : IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
      (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))),
      IsConjugation H V₃ V₁ ρ →
      ∀ (K : Subgroup G) (hKH : K ≤ H), (K.subgroupOf H).IsCComponent →
      ∀ (n : ℕ), 5 ≤ n → ∀ eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin n),
      HasSectionModel H V₃ V₁ ρ K hKH
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) eK →
      Source.UH H V₃ = ⁅Source.UH H V₃, K⁆ ∧ sourceOne L T V₁ ≤ K ∧
      (H : Set G) = (K : Set G) * (T : Set G) ∧
      ((n = 6 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
        CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
          (ChiefQuotient.loneRepresentation H V₃ (sourceOne L T V₁)
            (le_sup_left.trans hH.1.2))) ∨
       (n = 7 ∧ Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)))

/-- All of 13.8.5(2),(3), with each module intertwined by the same actor
isomorphism as its group model. The augmentation alternative is genuinely
five-dimensional; the chief series is on U_H/V₁, not on U_H. -/
def FullAlternatives (H L L₁ V₃ V₁ : Subgroup G) (hL₁ : L₁ ≤ H)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁))) : Prop :=
  (((HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin 6))) ∨
      (HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin 6)) ∧
       Module.finrank (ZMod 2) (Additive (Source.Utilde H V₃ V₁)) = 5)) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧
    CriticalGeometry.Reorientation.TwoNoncentralChiefFactors
      (ChiefQuotient.loneQuotientRepresentation H V₃ V₁ L₁ hL₁ ρ)) ∨
  ((HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin 7)) ∨
    HasActionModel ρ projectiveFourRepresentation) ∧
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms))

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
end
