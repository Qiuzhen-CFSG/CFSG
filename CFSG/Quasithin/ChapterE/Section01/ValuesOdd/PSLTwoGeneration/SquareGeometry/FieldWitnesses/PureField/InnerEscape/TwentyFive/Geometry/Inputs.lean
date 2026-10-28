module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Frames
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.FamilyUnions

/-!
# Independent characteristic-five model calculations

The fusion contract concerns individual actors and their actual ambient
conjugates inside the common Sylow. The generation contract concerns five
joins of literal centralizers and normalizers. Their shared coordinates are
constructed in `Frames`; `Geometry` proves the invariant-family assembly.
Neither contract contains the final escape conclusion or an E-generation
hypothesis. Both still need proofs in the actual order-25 field model.

Source: Aschbacher--Smith E.1.14(6), printed p.214, referring to
Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F}

namespace Frame
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

/-- Some actual ambient conjugate in the chosen Sylow has a usable image. -/
@[expose] def Usable (i : Bool) (A : Subgroup (innerModel F σ)) : Prop :=
  ∃ B ∈ conjugatesIn (c.T : Subgroup (innerModel F σ)) A, c.IsPositioned hF hσ i B

variable [Finite (innerModel F σ)]

/-- The individual actors to which the finite model calculation applies. -/
@[expose] def Eligible (A : Subgroup (innerModel F σ)) : Prop :=
  IsElementaryAbelian 2 A ∧ A ≤ (c.T : Subgroup (innerModel F σ)) ∧
    A ≠ ⊥ ∧ (Group.rank A = 2 ∨ Group.rank A = 3)

/-- Fusion and coordinate facts for individual actors. In particular the
second clause identifies their full ambient conjugacy span inside `T`. -/
structure Fusion : Prop where
  coverage : ∀ A, c.Eligible A → c.Usable hF hσ false A ∨ c.Usable hF hσ true A
  spans : ∀ i A, c.Eligible A → ¬ c.Usable hF hσ i A →
    orbitSpan (c.T : Subgroup (innerModel F σ)) A = c.small hF hσ i ∨
      orbitSpan (c.T : Subgroup (innerModel F σ)) A = c.large hF hσ i

/-- Five concrete subgroup-generation identities, independent of actor
families. The normalizer belongs to the opposite centralizer's span. -/
structure Generation : Prop where
  pair : c.centralizerAt false ⊔ c.centralizerAt true = ⊤
  small : ∀ i, c.centralizerAt (!i) ⊔
    normalizer (c.small hF hσ i : Set (innerModel F σ)) = ⊤
  large : ∀ i, c.centralizerAt (!i) ⊔
    normalizer (c.large hF hσ i : Set (innerModel F σ)) = ⊤

end Frame
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
