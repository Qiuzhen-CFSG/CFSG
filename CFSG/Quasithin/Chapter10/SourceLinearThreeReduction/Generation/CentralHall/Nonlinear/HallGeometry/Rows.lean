module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Inputs

/-!
# Independent row calculations for the central Hall geometry

The natural and Suzuki calculations must show that the original quotient
action is trivial. The shared H-star argument then contradicts faithfulness
and nontriviality. The orthogonal calculation must produce one common
product marking and pointwise diagonal realizations fixing both specified
singular vectors. Multiplicativity of the parameters is proved separately,
rather than being an additional geometric assumption.

All three predicates are outstanding source obligations. Their simultaneous
assembly is owned by HallGeometry.Source, and they require no module
classification input: each row supplies its actual coordinates.
Source: Aschbacher--Smith, 10.1.2(5) and 10.2.3, pp.742 and 745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G]

local instance fixedBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance hermitianBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- The natural section forces triviality of the literal quotient action. -/
def NaturalActionTrivialAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ModuleGeometry D → ∀ (r : ℕ), 1 < r →
      ∀ e : (L ⧸ pCore 2 L) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r),
        NaturalSection D r e → action D B c.hall_le = 1

/-- The whole Suzuki module forces triviality of the literal quotient action. -/
def SuzukiActionTrivialAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ModuleGeometry D → ∀ (m : ℕ), 0 < m →
      ∀ e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m,
        BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
          ((SuzukiNatural.natural m).comp
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) →
        action D B c.hall_le = 1

/-- A single marking realizes all original Hall actors by diagonal matrices
fixing the two singular vectors. Neither characters nor innerness are assumed. -/
def OrthogonalDiagonalAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ModuleGeometry D → ∀ (n : ℕ) (_ : NeZero n), 1 < n →
      ∀ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n),
        BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
          ((SL2.BinarySmall.hermitian n).comp
            (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))) →
        ∃ (e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
          (q : (localOrbit T L ⧸ pCore 2 (localOrbit T L)) ≃*
            (Matrix.SpecialLinearGroup (Fin 2) (Field n) ×
              Matrix.SpecialLinearGroup (Fin 2) (Field n))),
          (∀ l : L, q (QuotientGroup.mk' (pCore 2 (localOrbit T L))
            ⟨l,le_componentOrbit L T l.property⟩) =
              (e' (QuotientGroup.mk' (pCore 2 L) l),1)) ∧
          ∀ b : B, ∃ a : (Field n)ˣ × (Field n)ˣ,
            (∀ x, q (action D B c.hall_le b x) =
              (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2) * q x *
                (CartanFixed.diagonal n a.1, CartanFixed.diagonal n a.2)⁻¹) ∧
            FiniteModel.action n (CartanFixed.diagonal n a.1)
              (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1 ∧
            FiniteModel.action n (CartanFixed.diagonal n a.2)
              (CartanFixed.rootVector n 1) = CartanFixed.rootVector n 1

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
