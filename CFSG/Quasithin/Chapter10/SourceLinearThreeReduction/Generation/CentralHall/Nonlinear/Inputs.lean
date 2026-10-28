module

public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Cartan
public import Theory.Representation.BinaryConjugationSection
public import Theory.Representation.SL2.BinarySmallModels
public import Theory.Representation.Suzuki.NaturalMatrix

/-!
# The two source inputs for the nonlinear central Hall calculation

After excluding A₅ and SL₃(2), the required part of 10.1.1 consists of
the natural SL₂ section, the whole orthogonal SL₂ module, or the whole
natural Suzuki module. Each row below retains an actual quotient
isomorphism and equivariant coordinates on the original moved subgroup.
The common geometry includes crossed centralization; pair generation
alone does not supply it.

The independent Hall calculation may assume this geometry and the row's
coordinates. It must exclude the natural and Suzuki rows, and construct
the inner Cartan coordinates in the orthogonal row, including elimination
of the field-automorphism factor. These are unproved source obligations,
not source theorems. Their assembly owner is `Nonlinear.Source`.
Source: Aschbacher--Smith, 10.1.1--2 and 10.2.3, pp.741--742,745.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
open Chapter3.Section02 Representation
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

local instance fixedBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance hermitianBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

/-- The genuine common module geometry in the surviving rows of 10.1.1. -/
structure ModuleGeometry : Prop where
  full_eq_local : D.fullModule = D.moduleSubgroup
  crossed : ∀ t ∈ (T : Subgroup G), t ∉ normalizer (L : Set G) →
    (⁅D.fullModule,L⁆).map (MulAut.conj t).toMonoidHom ≤ centralizer (L : Set G)

/-- The natural section, using the natural model's specified binary scalars. -/
abbrev NaturalSection (r : ℕ)
    (e : (L ⧸ pCore 2 L) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r)) :=
  letI : Algebra (ZMod 2) (GaloisField 2 r) := ZMod.algebra _ 2
  BinaryConjugationSection L ⁅D.fullModule,L⁆
    (⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G))
    (SL2.BinarySmall.natural.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))

/-- Source rows (1), (4), (7), with the literal component quotient and action. -/
inductive ModuleRow (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop
  | natural (r : ℕ) (large : 1 < r)
      (e : (L ⧸ pCore 2 L) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
      (coordinates : Nonempty (NaturalSection D r e)) : ModuleRow D
  | orthogonal (n : ℕ) [NeZero n] (large : 1 < n)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
      (coordinates : Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((SL2.BinarySmall.hermitian n).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) : ModuleRow D
  | suzuki (m : ℕ) (positive : 0 < m)
      (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
      (coordinates : Nonempty (BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((SuzukiNatural.natural m).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))) : ModuleRow D

/-- The first outstanding source input: obtain the actual remaining module rows. -/
def ModuleAnalysisAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (_c : Context D H B),
    ¬ Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ModuleGeometry D ∧ ModuleRow D

/-- The Hall calculation on each actual source row. No injectivity or
norm-one conclusion is assumed by the orthogonal coordinate contract. -/
structure HallGeometry {H : Subgroup G} (B : Subgroup H) (c : Context D H B) : Prop where
  natural_excluded (r : ℕ) (large : 1 < r)
      (e : (L ⧸ pCore 2 L) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 r))
      (coordinates : NaturalSection D r e) : False
  orthogonal (n : ℕ) [NeZero n] (large : 1 < n)
      (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
      (coordinates : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((SL2.BinarySmall.hermitian n).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) :
    ∃ e' : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n),
      Nonempty (CartanCoordinates D B c.hall_le n e')
  suzuki_excluded (m : ℕ) (positive : 0 < m)
      (e : (L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)
      (coordinates : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
        ((SuzukiNatural.natural m).comp
          (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) : False

/-- The independent source calculation, conditional on genuine common geometry.
The producer must prove every row; it does not await the module classification. -/
def HallGeometryAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (H : Subgroup G) (B : Subgroup H) (c : Context D H B),
    ModuleGeometry D → HallGeometry D B c

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear
