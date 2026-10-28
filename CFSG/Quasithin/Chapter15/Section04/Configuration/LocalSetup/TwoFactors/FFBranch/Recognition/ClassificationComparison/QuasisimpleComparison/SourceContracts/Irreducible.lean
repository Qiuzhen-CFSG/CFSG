module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.SourceActions.Irreducible
/-!
# The projective-line convention in B.4.2(8)

K.1.3 identifies the offender as the radical fixing a two-dimensional F₄
subspace in a three-dimensional F₄ module. Thus the F₄-line in B.4.2(8)
is a projective line, not a one-dimensional vector subspace. This namespace
provides the corrected full irreducible contract. The earlier conditional
contract remains available unchanged; no implication from its one-dimensional
offender assertion to this assertion is claimed.

All other cases and their action, rank and offender clauses are retained.
The model extraction deliberately does not use either offender convention.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.2,
printed p.86, and K.1.3, printed p.453.
-/
@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
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

/-- Extract the actual actor from the full action list. This is transport
of conclusions, not the B.4.2 classification theorem. -/
theorem IrreducibleActionCase.model {L H : Subgroup D}
    (h : IrreducibleActionCase ρ L H) : QuasisimpleModel L := by
  cases h with
  | linearTwo F _ e _ _ => exact .linearTwo F e.groupEquiv
  | linearThree F _ e _ => exact .linearThree F e.groupEquiv
  | symplectic F _ _ e _ => exact .symplecticFour F e.groupEquiv
  | symplecticTwo e _ =>
    exact .alternatingSix (e.subgroupEquiv.trans binarySymplecticDerivedEquiv)
  | g2 F _ _ e _ _ => exact .g2 F e.groupEquiv
  | g2Two e _ _ => exact .g2DerivedTwo e.subgroupEquiv
  | symmetric n hn e _ _ =>
    rcases hn with rfl | rfl
    · exact .linearTwo BinaryField.four (e.subgroupEquiv.trans alternatingFiveLinearEquiv)
    · exact .alternatingSeven e.subgroupEquiv
  | alternatingSix _ e _ _ => exact .alternatingSix e.groupEquiv
  | alternatingSeven _ _ e _ _ _ => exact .alternatingSeven e
  | tripleSix _ h _ => exact .tripleSix h.centerEquiv h.quotientEquiv
  | binaryLinear d hd _ e _ =>
    rcases hd with rfl | rfl
    · exact .linearFourTwo e.groupEquiv
    · exact .linearFiveTwo e.groupEquiv
  | orthogonalSix _ _ e _ _ =>
    exact .linearFourTwo (e.groupEquiv.trans alternatingEightLinearEquiv)
  | symmetricEight _ e _ =>
    exact .linearFourTwo (e.subgroupEquiv.trans alternatingEightLinearEquiv)
  | exteriorFive _ _ e _ _ _ => exact .linearFiveTwo e

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives.ProjectiveLine
