module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.Layers
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.MSContract
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Mathlib.GroupTheory.Frattini

/-!
# All five C.1.34 alternatives

The five alternatives keep every layer as an intrinsic quotient with its
actual conjugation action. One common quotient identification coordinates
the natural layers and their contragredient duals. In particular case (4)
retains all three higher layers and its central elementary summand, while
case (5) retains the index-seven point stabilizer and radical equality.
The universal classification below is an earlier-result parameter, not a
proof of C.1.34 and not a reduced classification for this application.

Source: Aschbacher–Smith, C.1.34(1)–(5), printed pp.136–137.
-/

@[expose] public section

open Subgroup Representation Stellmacher CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
universe u

/-- Coordinatewise copies of a specified representation. -/
def moduleCopies {F T V : Type*} [Field F] [Group T] [AddCommGroup V] [Module F V]
    (ρ : Representation F T V) (a : ℕ) : Representation F T (Fin a → V) where
  toFun g :=
    { toFun v i := ρ g (v i)
      map_add' v w := by ext; simp
      map_smul' c v := by ext; simp }
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp

abbrev NaturalCopies (F : Type) [Field F] (a : ℕ) :=
  moduleCopies (specialLinearNatural (k := F) 3) a

abbrev DualCopies (F : Type) [Field F] (a : ℕ) :=
  moduleCopies (specialLinearNatural (k := F) 3).dual a

variable {D : Type u} [Group D]

/-- Φ(Q), mapped from its intrinsic carrier to D. -/
def sourceFrattini (L : Subgroup D) : Subgroup D :=
  (frattini (sourceQ L)).map (sourceQ L).subtype

/-- C_Q(Φ(Q)), in the original ambient group. -/
def sourceFrattiniCentralizer (L : Subgroup D) : Subgroup D :=
  sourceQ L ⊓ centralizer (sourceFrattini L : Set D)

/-- The natural summand in case (4) is the actual commutator [Z(Q),L]. -/
def sourceNatural (L : Subgroup D) : Subgroup D := ⁅sourceCenter L, L⁆

/-- The exact inequality in source cases (2)–(4). -/
def RadicalInequality (R : Subgroup D) (S : Sylow 2 D) : Prop :=
  R ≠ (pCore 2 (centralizer (omegaOneCenterAmbient (S : Subgroup D) : Set D))).map
    (centralizer (omegaOneCenterAmbient (S : Subgroup D) : Set D)).subtype

/-- The index-seven point-stabilizing subgroup in case (5), retaining its
actual action on Q/C_Q(L), the containment of S, and its radical. -/
def IndexSevenPointRadical (L R : Subgroup D) (S : Sylow 2 D) : Prop :=
  ∃ G₁ : Subgroup D, G₁.index = 7 ∧ (S : Subgroup D) ≤ G₁ ∧
    (pCore 2 G₁).map G₁.subtype = R ∧
    ∃ q : sourceQ L, (q : D) ∉ sourceFixed L ∧
      ∀ g : D, g ∈ G₁ ↔ g * (q : D) * g⁻¹ * (q : D)⁻¹ ∈ sourceFixed L

/-- All source alternatives, with a common actual quotient isomorphism
for the natural modules and their duals. -/
inductive Alternatives (F : Type) [Field F] (n : ℕ) (L R : Subgroup D)
    (S : Sylow 2 D) (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) : Prop
  | one (block : IsSL3EvenBlock L n)
      (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies F 1)))
  | two (natural : Nonempty (LayerModel L (sourceQ L) ⊥ e (NaturalCopies F 2)))
      (radical : RadicalInequality R S)
  | three (natural : Nonempty (LayerModel L (sourceCenter L) ⊥ e (NaturalCopies F 1)))
      (dual : Nonempty (LayerModel L (sourceQ L) (sourceCenter L) e (DualCopies F 2)))
      (radical : RadicalInequality R S)
  | four (elementary : IsElementaryAbelian 2 (sourceFixed L))
      (order : Nat.card (sourceFixed L) = 2 ^ (2 * n))
      (central : sourceFixed L ≤ center D)
      (fixed_le_center : sourceFixed L ≤ sourceCenter L)
      (natural_le_center : sourceNatural L ≤ sourceCenter L)
      (direct_sum : (sourceNatural L |>.subgroupOf (sourceCenter L)).IsComplement'
        (sourceFixed L |>.subgroupOf (sourceCenter L)))
      (natural : Nonempty (LayerModel L (sourceNatural L) ⊥ e (NaturalCopies F 1)))
      (frattini_dual : Nonempty (LayerModel L (sourceFrattini L) (sourceCenter L) e (DualCopies F 1)))
      (centralizer_dual : Nonempty (LayerModel L (sourceFrattiniCentralizer L) (sourceFrattini L) e (DualCopies F 2)))
      (upper_natural : Nonempty (LayerModel L (sourceQ L) (sourceFrattiniCentralizer L) e (NaturalCopies F 2)))
      (radical : RadicalInequality R S)
  | five (binary_quotient : Nonempty ((L ⧸ pCore 2 L) ≃* Natural.Actor))
      (fixed_order : Nat.card (sourceFixed L) = 2)
      (natural : Nonempty (LayerModel L (sourceQ L) (sourceFixed L) e (NaturalCopies F 1)))
      (central_omega : omegaOneCenterAmbient (S : Subgroup D) ≤ center D)
      (radical : IndexSevenPointRadical L R S)

/-- The complete universal implication C.1.34, at every field and every
MS-pair. The isomorphism is existential in the output: an arbitrary fixed
identification may interchange the natural and dual modules. -/
def UniversalClassification : Prop :=
  ∀ (κ : GroupClass.{u}) (D : Type u) [Group D] [Finite D]
    (L R : Subgroup D), MSPair κ D L R →
    ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 0 < n → Nat.card F = 2 ^ n →
      Nonempty ((L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F) →
      ∀ S : Sylow 2 D, R ≤ (S : Subgroup D) →
        ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) F,
          Alternatives F n L R S e

/-- The binary coordinate action agrees with the previously proved obstruction. -/
theorem naturalCopies_binary (a : ℕ) : NaturalCopies (ZMod 2) a = Natural.copies a := by
  ext g v i
  rfl

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases
