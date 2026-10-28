module

public import CFSG.Quasithin.ChapterG.Section09.Setup
public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts
public import Theory.SpecificGroups.GL2.Semilinear
public import Theory.Representation.QuasithinRankTwoInvolutionExclusions.OddCentralizer.ExtraspecialModel.BinaryAction
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The five concrete outputs of G.9.4

The orthogonal alternatives use subgroups of the full isometry group of the
split binary four-space, with their natural actions. In particular its
three-core is not confused with the elementary orthogonal subgroup. The
semilinear alternative retains the matrix and coefficient-automorphism action.
The degree-six alternative uses the previously constructed, marked
extraspecial-three extension and its faithful binary action.

These are output predicates, not assumptions on the input action. The second
case identifies the actual normal closure of the given actor. Source:
Aschbacher--Smith, G.9.4, printed pp.354--355, PDF pp.365--366.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition

universe u v

variable {G : Type u} [Group G] {V : Type v}
  [AddCommGroup V] [Module (ZMod 2) V]

/-- The full orthogonal group, on the prescribed hyperbolic coordinates. -/
abbrev OrthogonalFour := Theory.AlgebraicGroup.quadraticIsometrySubgroup
  (ClassicalOrthogonal.formD 2 (ZMod 2))

/-- The actual binary natural action of a subgroup of the orthogonal group. -/
def OrthogonalRealization (ρ : Representation (ZMod 2) G V)
    (H : Subgroup OrthogonalFour) : Prop :=
  ∃ e : G ≃* H, ∃ f : V ≃ₗ[ZMod 2] ClassicalOrthogonal.VectorD 2 (ZMod 2),
    ∀ g v, f (ρ g v) = (e g).val.val (f v)

/-- The semilinear group acts by a matrix after applying its coefficient automorphism. -/
def SemilinearRealization (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ e : G ≃* Matrix.GeneralLinearGroup.GammaL2 (GaloisField 2 2),
    ∃ f : V ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      ∀ g v, f (ρ g v) =
        ((e g).left : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
          (fun i => (e g).right (f v i))

/-- The marked extension and the representation both come from the concrete model. -/
def ExtraspecialRealization (ρ : Representation (ZMod 2) G V) : Prop :=
  ∃ H : Subgroup Representation.RankTwo.ExtraspecialModel.Model,
    Representation.RankTwo.ExtraspecialModel.fourExtension ≤ H ∧
      Quasiequivalent ρ
        (Representation.RankTwo.ExtraspecialModel.BinaryAction.representation.comp H.subtype)

/-- G.9.4(1). The plane recognition theorem also identifies the full linear action. -/
def CaseOne [FiniteDimensional (ZMod 2) V]
    (_ρ : Representation (ZMod 2) G V) (m : ℕ) : Prop :=
  m = 1 ∧ Module.finrank (ZMod 2) V = 2 ∧ Nonempty (G ≃* Equiv.Perm (Fin 3))

/-- G.9.4(2), with `K = ⟨Aᴳ⟩` interpreted literally. -/
def CaseTwo [FiniteDimensional (ZMod 2) V]
    (_ρ : Representation (ZMod 2) G V) (A : Subgroup G) (m : ℕ) : Prop :=
  m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
    Nonempty (Subgroup.normalClosure (A : Set G) ≃* DihedralGroup 5)

/-- G.9.4(3), including the lower containment of the full orthogonal three-core. -/
def CaseThree [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (m : ℕ) : Prop :=
  m = 1 ∧ Module.finrank (ZMod 2) V = 4 ∧
    (SemilinearRealization ρ ∨ ∃ H : Subgroup OrthogonalFour,
      pCore 3 OrthogonalFour ≤ H ∧ OrthogonalRealization ρ H)

/-- G.9.4(4), with the index taken in the full orthogonal group. -/
def CaseFour [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (m : ℕ) : Prop :=
  m = 2 ∧ Module.finrank (ZMod 2) V = 4 ∧
    ∃ H : Subgroup OrthogonalFour, H.index ≤ 2 ∧ OrthogonalRealization ρ H

/-- G.9.4(5), including its marked lower subgroup and actual binary module. -/
def CaseFive [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (m : ℕ) : Prop :=
  m = 2 ∧ Module.finrank (ZMod 2) V = 6 ∧ ExtraspecialRealization ρ

/-- All five source alternatives; no classification is built into the hypotheses. -/
def Conclusion [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) (m : ℕ) : Prop :=
  CaseOne ρ m ∨ CaseTwo ρ A m ∨ CaseThree ρ m ∨ CaseFour ρ m ∨ CaseFive ρ m

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
