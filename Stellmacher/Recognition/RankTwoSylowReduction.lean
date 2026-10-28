module

public import Stellmacher.MainDefs
public import Theory.GroupTheory.PGroup.NoNormalFourClassification
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Data.ZMod.Basic

/-!
# The proved no-normal-four part of the rank-two Sylow reduction

The low elementary-rank argument splits at the first normal elementary
four-group in the Sylow subgroup.  The no-normal-four side is a completely
independent two-group calculation: a finite two-group containing an elementary
four-group and no normal elementary four-group is dihedral or semidihedral.

This file records that consequence with the actual `Sylow` carrier and the
project's public predicates. The complementary normal-four branch must retain
the dihedral alternative as well as the `C₄ ≀ C₂` and order-64 Lyons
configurations. It requires the transfer and MacWilliams inputs from the source
and is intentionally not folded into this lemma as an assumption disguised as
a recognition theorem. The checked rank-bound consequences and the adapter to
Lyons's full intrinsic hypotheses are in `NormalFourSylowReduction`.

Source for the proved calculation: GLS2, Chapter C, Lemma 10.11; the Lean
implementation is `Theory.GroupTheory.PGroup.NoNormalFourClassification`.
-/

namespace Stellmacher.Recognition

universe u

open Subgroup

/-- The concrete `C₄ ≀ C₂` model used by the missing normal-four branch. -/
public abbrev C4WreathC2 :=
  RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))

/-- A compact intrinsic description of the order-64 (Lyons) Sylow structure.

All subgroups in this predicate are subgroups of the Sylow carrier itself;
thus no coercion-dependent ambient equality is hidden in the statement.  The
square-generated subgroup is the subgroup closure of the set of squares (the
squaring map need not be a homomorphism in a nonabelian group).
-/
public def IsLyonsSylow (S : Type u) [Group S] [Finite S] : Prop :=
  ∃ Z : Subgroup S,
    Nat.card S = 64 ∧
    Z = Subgroup.center S ∧
    Z = commutator S ∧
    Z = frattini S ∧
    Z = Subgroup.closure (Set.range (fun x : S => x ^ 2)) ∧
    IsElementaryAbelian 2 Z ∧ Nat.card Z = 4

/-- Public specification of the intrinsic Lyons predicate. -/
public theorem isLyonsSylow_iff (S : Type u) [Group S] [Finite S] :
    IsLyonsSylow S ↔ ∃ Z : Subgroup S,
      Nat.card S = 64 ∧ Z = Subgroup.center S ∧ Z = commutator S ∧
      Z = frattini S ∧ Z = Subgroup.closure (Set.range (fun x : S => x ^ 2)) ∧
      IsElementaryAbelian 2 Z ∧ Nat.card Z = 4 := Iff.rfl

/-- The intrinsic Lyons Sylow structure has order sixty-four. -/
public theorem IsLyonsSylow.card {S : Type u} [Group S] [Finite S]
    (hS : IsLyonsSylow S) : Nat.card S = 64 := by
  obtain ⟨Z, hcard, _⟩ := hS
  exact hcard

/-- The four alternatives used by the low-rank Sylow interface. -/
public def RankTwoSylowAlternative (S : Type u) [Group S] [Finite S] : Prop :=
  IsDihedralGroup S ∨
  IsSemidihedralGroup S ∨
  Nonempty (S ≃* C4WreathC2) ∨
  IsLyonsSylow S

/-- Public specification of the four-way Sylow alternative. -/
public theorem rankTwoSylowAlternative_iff (S : Type u) [Group S] [Finite S] :
    RankTwoSylowAlternative S ↔
      IsDihedralGroup S ∨ IsSemidihedralGroup S ∨
        Nonempty (S ≃* C4WreathC2) ∨ IsLyonsSylow S := Iff.rfl

/-- No-normal-four classification, expressed as the first two alternatives of
the rank-two interface. -/
public theorem dihedral_or_semidihedral_of_no_normal_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hS : IsPGroup 2 S)
    (hno : ¬ ∃ U : Subgroup S,
      U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    IsDihedralGroup S ∨ IsSemidihedralGroup S := by
  obtain ⟨m, hm⟩ | ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩ :=
    IsPGroup.exists_dihedral_or_semidihedral_of_no_normal_four hS hno E hE
  · exact Or.inl ⟨m, hm⟩
  · exact Or.inr ⟨n, hn, hcard, a, b, ha, hb, hab, hgen⟩

/-- The no-normal-four branch as a `RankTwoSylowAlternative`. -/
public theorem rank_two_sylow_alternative_of_no_normal_four
    {G : Type u} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hS : IsPGroup 2 S)
    (hno : ¬ ∃ U : Subgroup S,
      U.Normal ∧ IsElementaryAbelian 2 U ∧ Nat.card U = 4)
    (E : Subgroup S) [IsElementaryAbelian 2 E] (hE : Nat.card E = 4) :
    RankTwoSylowAlternative S := by
  rcases dihedral_or_semidihedral_of_no_normal_four S hS hno E hE with hd | hs
  · exact Or.inl hd
  · exact Or.inr (Or.inl hs)

end Stellmacher.Recognition
