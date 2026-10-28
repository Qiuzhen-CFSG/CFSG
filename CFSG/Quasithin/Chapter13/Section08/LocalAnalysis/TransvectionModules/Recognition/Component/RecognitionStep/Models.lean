module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Component.Sections
public import Theory.Representation.BinaryPermutationAlternatingActions
public import Theory.SpecificGroups.BinaryLinear.Parabolics

/-!
# Concrete models at the G.6.4 application boundary

The three actor alternatives retain group and module equivalences, including
the even-degree permutation core, which is different from the natural module.
The section predicate uses the literal displacement space modulo its fixed
vectors and retains the specified group equivalence on representatives.

These are conclusion predicates for the recognition and intrinsic model
calculations. They assert neither classification nor component existence.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, G.6.4(2),
printed pp.345–346, and the first paragraph of 13.8.5, printed p.947.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

/-- The actual natural action of the binary linear group. -/
def linearRepresentation (n : ℕ) :
    Representation (ZMod 2) (BinaryLinear.GL (Fin n → ZMod 2)) (Fin n → ZMod 2) where
  toFun g := g.toLinearMap
  map_one' := rfl
  map_mul' _ _ := rfl

variable {A E : Type*} [Group A] [AddCommGroup E] [Module (ZMod 2) E]

/-- An identification of the entire actor and its representation. -/
def HasActionModel (ρ : Representation (ZMod 2) A E)
    {B F : Type*} [Group B] [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F) : Prop :=
  ∃ (eA : A ≃* B) (eE : E ≃ₗ[ZMod 2] F),
    ∀ a v, eE (ρ a v) = σ (eA a) (eE v)

/-- The single-factor alternatives of G.6.4, before excluding the solvable
linear group of dimension two. The permutation-core cases are retained. -/
def ActorModel (ρ : Representation (ZMod 2) A E) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ HasActionModel ρ (linearRepresentation n)) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧
    HasActionModel ρ (BinaryPermutation.naturalRepresentation (Fin n))) ∨
  (∃ n, (n = 6 ∨ n = 8) ∧
    HasActionModel ρ (BinaryPermutation.coreRepresentation (Fin n)))

/-- A model of [E,C]/C_[E,C](C), with an explicitly specified actor map. -/
def HasCentralSectionModel (ρ : Representation (ZMod 2) A E) (C : Subgroup A)
    {B F : Type*} [Group B] [AddCommGroup F] [Module (ZMod 2) F]
    (σ : Representation (ZMod 2) B F) (eC : C ≃* B) : Prop :=
  let I := subspaceCommutator ρ ⊤ C
  ∃ (hs : ∀ (c : C) (v : I), ρ c v ∈ I)
    (e : (I ⧸ (fixedSpace ρ C).comap I.subtype) ≃ₗ[ZMod 2] F),
    ∀ (c : C) (v : I),
      e (Submodule.Quotient.mk ⟨ρ c v, hs c v⟩) =
        σ (eC c) (e (Submodule.Quotient.mk v))

/-- The two natural-section alternatives required for 13.7.6, with the
source parameter bounds and actual model identifications. -/
def NaturalSection (ρ : Representation (ZMod 2) A E) (C : Subgroup A) : Prop :=
  (∃ n, 3 ≤ n ∧ n ≤ 5 ∧
    ∃ eC : C ≃* BinaryLinear.GL (Fin n → ZMod 2),
      HasCentralSectionModel ρ C (linearRepresentation n) eC) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧
    ∃ eC : C ≃* alternatingGroup (Fin n),
      HasCentralSectionModel ρ C
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) eC)

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep

end
