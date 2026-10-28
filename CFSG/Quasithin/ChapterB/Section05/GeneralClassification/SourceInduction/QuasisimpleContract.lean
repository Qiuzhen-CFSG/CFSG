module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Statement

/-!
# Earlier B.5.1 input with the source projective-line convention

This lower interface retains all six B.5.1 conclusions on the actual action.
It uses the vector-plane convention in B.4.2(8), as specified by K.1.3, and
leaves the older one-dimensional convention unchanged. The definitions agree
with the corrected Chapter 15 consumer contracts without importing that chapter.

The universal implication below is an allowed earlier-source parameter for
the B.5.6 induction. It is not proved here. Its source assembly owner is
`qt-b05-quasisimple`; the general-classification owner must instantiate it.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.4.2, p.86,
B.5.1, pp.99–103, and K.1.3, p.453.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine
open QuasisimpleSource
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- B.4.2(8)'s scalar structure is on the actual module. A projective F₄-line is a vector
plane; the specified binary coordinates make that plane literal, and the actor preserves F₄-scaling. -/
structure TripleSixAction (L : Subgroup D) where
  centerEquiv : center L ≃* Multiplicative (ZMod 3)
  quotientEquiv : (L ⧸ center L) ≃* alternatingGroup (Fin 6)
  dimension : Module.finrank (ZMod 2) V = 6
  coordinates : V ≃ₗ[ZMod 2] (Fin 3 → BinaryField.four.Carrier)
  scalar_linear : ∀ (g : L) (c : BinaryField.four.Carrier) (v : V),
    coordinates (ρ g (coordinates.symm (c • coordinates v))) = c • coordinates (ρ g v)
  offenders : ∀ A, IsBestOffender ρ A → ∃ P :
      Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier),
    Module.finrank BinaryField.four.Carrier P = 2 ∧
    A = subspaceKernel ρ ((P.restrictScalars (ZMod 2)).comap coordinates.toLinearMap) ⊤

/-- All eleven possibilities in B.4.2. The two small derived endpoints and
the two orthogonal endpoints are displayed separately, retaining the source
cases without identifying a full group with its commutator subgroup. -/
inductive IrreducibleActionCase (L H : Subgroup D) : Prop
  | linearTwo (F : BinaryField) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2))
      (offenders : ∀ A, IsBestOffender ρ A → ∃ S : Sylow 2 L,
        A = (S : Subgroup L).map L.subtype)
      (ratio : quadraticRatio ρ = 1)
  | linearThree (F : BinaryField) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
      (ratio : quadraticRatio ρ = 1 / 2)
  | symplectic (F : BinaryField) (large : 1 < F.degree) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F))
      (ratio : quadraticRatio ρ = 2 / 3)
  | symplecticTwo
      (e : MarkedActionEquiv ρ H L (symplecticNatural (k := ZMod 2) 2)
        (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
      (ratio : quadraticRatio ρ = 2 / 3)
  | g2 (F : BinaryField) (large : 1 < F.degree) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (binaryG2 F))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3 * F.degree)
      (ratio : quadraticRatio ρ = 1)
  | g2Two (e : MarkedActionEquiv ρ H L (g2Natural (ZMod 2))
        (commutator (Atlas.G2.Model (ZMod 2))))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3)
      (ratio : quadraticRatio ρ = 1)
  | symmetric (n : ℕ) (degree : n = 5 ∨ n = 7)
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin n))
        (alternatingGroup (Fin n)))
      (offenders : ∀ A, IsBestOffender ρ A →
        ChapterB.Offenders.CaseAFamily n
          ((A.subgroupOf H).map e.action.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
  | alternatingSix (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 6))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 2 ∧
        ∃ g : alternatingGroup (Fin 6),
          ((A.subgroupOf L).map
            ((alternatingGroup (Fin 6)).subtype.comp e.groupEquiv.toMonoidHom)) =
          (ChapterB.Offenders.evenPart 6).map (MulAut.conj (g : Equiv.Perm (Fin 6))).toMonoidHom)
      (ratio : quadraticRatio ρ = 1)
  | alternatingSeven (generated : H = L) (whole : L = ⊤)
      (e : L ≃* alternatingGroup (Fin 7)) (dimension : Module.finrank (ZMod 2) V = 4)
      (offenders : ∀ A, IsBestOffender ρ A →
        ∃ g : alternatingGroup (Fin 7),
          ((A.subgroupOf L).map ((alternatingGroup (Fin 7)).subtype.comp e.toMonoidHom)) =
          (Subgroup.closure {ChapterB.Offenders.kleinFirst 7 (by decide),
            ChapterB.Offenders.kleinSecond 7 (by decide)}).map
              (MulAut.conj (g : Equiv.Perm (Fin 7))).toMonoidHom)
      (ratio : quadraticRatio ρ = 1)
  | tripleSix (generated : H = L) (action : TripleSixAction ρ L)
      (ratio : quadraticRatio ρ = 1)
  | binaryLinear (d : ℕ) (degree : d = 4 ∨ d = 5) (generated : H = L)
      (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two d))
      (ratio : quadraticRatio ρ = 1 / (d - 1 : ℕ))
  | orthogonalSix (generated : H = L) (whole : L = ⊤)
      (e : ActionEquiv (ρ.comp L.subtype) (alternatingNatural 8))
      (offenders : ∀ A, IsBestOffender ρ A → rank A = 3)
      (ratio : quadraticRatio ρ = 1)
  | symmetricEight (whole : H = ⊤)
      (e : MarkedActionEquiv ρ H L (BinaryPermutation.naturalRepresentation (Fin 8))
        (alternatingGroup (Fin 8)))
      (ratio : quadraticRatio ρ = 3 / 4)
  | exteriorFive (generated : H = L) (whole : L = ⊤)
      (e : L ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
      (dimension : Module.finrank (ZMod 2) V = 10)
      (offenders : ∀ A, IsBestOffender ρ A →
        IsEndNodeRadical ((A.subgroupOf L).map e.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)

/-- The full four-way alternative in B.5.1(1), after its Fitting equality.
The referenced B.4.2 data is on the actual quotient action. -/
inductive QuasisimpleActionCase (L : Subgroup D) (s : MovedSection ρ L) : Prop
  | irreducible (irrPlus : IsIrrPlus ρ L s.space.toSubmodule)
      (faithful : Function.Injective s.action)
      (irreducible : IsIrreducible (s.action.comp L.subtype))
      (source : IrreducibleActionCase s.action L (offenderSubgroup s.action))
      (extension : L = ⊤ ∨ (∀ T : Sylow 2 D, L ⊔ (T : Subgroup D) = ⊤) ∧
        OuterNaturalAction s.action)
  | doubleThree (F : BinaryField) (whole : L = ⊤)
      (e : ActionEquiv (s.space.toRepresentation.comp L.subtype)
        (repeated (linearNatural F 3) 2))
      (offenders : ∀ A, IsBestOffender s.space.toRepresentation A ↔
        IsFullAxisGroup F 3 ((A.subgroupOf L).map e.groupEquiv.toMonoidHom))
      (ratio : quadraticRatio ρ = 1)
  | naturalDual (d : ℕ) (degree : d = 4 ∨ d = 5) (whole : L = ⊤)
      (natural : IsNaturalPlusDual (s.space.toRepresentation.comp L.subtype) d)
  | repeatedNatural (d r : ℕ) (degree : d = 4 ∨ d = 5) (positive : 0 < r)
      (bound : r ≤ d - 1) (whole : L = ⊤)
      (natural : IsRepeatedLinearNatural
        (s.space.toRepresentation.comp L.subtype) BinaryField.two d r)

/-- The full B.5.1 conclusion. Clause (5) is a supplement assertion; the
word hyperplane in B.5.6(5) is encoded separately there, not added here. -/
structure QuasisimpleSourceConclusion (L : Subgroup D) where
  sectionData : MovedSection ρ L
  fitting_eq : L = generalizedFitting D
  clause_one : QuasisimpleActionCase ρ L sectionData
  nonsplitting_iff :
    (¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L)) ↔
      sectionData.space.toSubmodule ⊓ fixedSpace ρ L ≠ ⊥ ∨
      sectionData.space.toSubmodule ⊔ fixedSpace ρ L ≠ ⊤
  clause_two : ¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) →
    IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      NonsplitNatural (sectionData.action.comp L.subtype)
  clause_three : IsHomogeneousAction (sectionData.action.comp L.subtype) ∨
    ∃ d, (d = 4 ∨ d = 5) ∧
      IsNaturalPlusDual (sectionData.space.toRepresentation.comp L.subtype) d
  clause_four : ¬ IsCompl sectionData.space.toSubmodule ρ.invariants →
    IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      (¬ IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) ∨
        (IsCompl sectionData.space.toSubmodule (fixedSpace ρ L) ∧
          (IsSymmetricNatural sectionData.space.toRepresentation 6 ∨
            IsSymmetricNatural sectionData.space.toRepresentation 8) ∧
          Nat.card ((fixedSpace ρ L) ⧸
            ρ.invariants.comap (fixedSpace ρ L).subtype) = 2))
  clause_five : sectionData.space.toSubmodule ⊔ ρ.invariants = ⊤ ∨
    (IsIrrPlus ρ L sectionData.space.toSubmodule ∧
      SupplementNatural (sectionData.action.comp L.subtype) ∧
      (Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) →
        sectionData.space.toSubmodule ⊓ fixedSpace ρ L = ⊥))
  clause_six : ∀ d, (d = 4 ∨ d = 5) → L = ⊤ →
    IsNaturalPlusDual (sectionData.space.toRepresentation.comp L.subtype) d →
      ∀ T : Sylow 2 D, Nonempty (SylowFixedCentralizer ρ L d T)

/-- The complete universal earlier B.5.1 implication, with its original
hypotheses. Its use never supplies B.5.6 or any counterexample reduction. -/
def QuasisimpleClassificationInput (K : GroupClass.{u}) : Prop :=
  ∀ (D : Type u) [Group D] [Finite D]
    (V : Type v) [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D),
    QuasisimpleSourceHypothesis ρ K L → Nonempty (QuasisimpleSourceConclusion ρ L)

end CFSG.Quasithin.ChapterB.SourceInduction.ProjectiveLine
