module

public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Geometry
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The B.4.2 action list used by the native B.5.1 implication

Every row describes the actual representation and offender-generated subgroup.
The full binary symplectic and G₂ groups are distinguished from their derived
subgroups. The SL₃ row allows every positive binary field degree, as in B.4.2;
B.5.6's extra odd-degree restriction is not a hypothesis of B.5.1.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.2, p.86.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource
universe u v

/-- Restrict the natural symplectic action to the binary prime field. -/
def binarySymplectic (F : BinaryField) :=
  restrictScalars (k := ZMod 2) (symplecticNatural (k := F.Carrier) 2)

/-- Restrict the natural octonion quotient action to the binary prime field. -/
def binaryG2 (F : BinaryField) :=
  restrictScalars (k := ZMod 2) (g2Natural F.Carrier)

/-- The four-element field in the triple-cover row. -/
noncomputable def BinaryField.four : BinaryField where
  Carrier := GaloisField 2 2
  degree := 2
  degree_pos := by decide
  card_eq := GaloisField.card 2 2 (by decide)

variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- B.4.2(8)'s scalar structure is on the actual module. The specified binary
coordinates make the F₄-lines literal, and the actor preserves F₄-scaling. -/
structure TripleSixAction (L : Subgroup D) where
  centerEquiv : center L ≃* Multiplicative (ZMod 3)
  quotientEquiv : (L ⧸ center L) ≃* alternatingGroup (Fin 6)
  dimension : Module.finrank (ZMod 2) V = 6
  coordinates : V ≃ₗ[ZMod 2] (Fin 3 → BinaryField.four.Carrier)
  scalar_linear : ∀ (g : L) (c : BinaryField.four.Carrier) (v : V),
    coordinates (ρ g (coordinates.symm (c • coordinates v))) = c • coordinates (ρ g v)
  offenders : ∀ A, IsBestOffender ρ A → ∃ P :
      Submodule BinaryField.four.Carrier (Fin 3 → BinaryField.four.Carrier),
    Module.finrank BinaryField.four.Carrier P = 1 ∧
    A = subspaceKernel ρ ((P.restrictScalars (ZMod 2)).comap coordinates.toLinearMap) ⊤

/-- The literal unipotent radical of an end-node parabolic of SL₅(2). -/
def IsEndNodeRadical (A : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))) : Prop :=
  ∃ P : Submodule (ZMod 2) (Fin 5 → ZMod 2),
    (Module.finrank (ZMod 2) P = 1 ∨ Module.finrank (ZMod 2) P = 4) ∧
    A = (pCore 2 (subspaceStabilizer (linearNatural BinaryField.two 5) P)).map
      (subspaceStabilizer (linearNatural BinaryField.two 5) P).subtype

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

end CFSG.Quasithin.ChapterB.QuasisimpleSource
