module
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover
public import Theory.GroupTheory.PRadical

/-!
# Symplectic four-space radical normalizers

A nontrivial binary radical subgroup U has its normalizer as the two-local
subgroup N(U). The concrete fixed-space radical in the natural symplectic
four-space is nonzero isotropic and is preserved by N(U); the native
symplectic flag geometry therefore places N(U), after a literal symplectic
conjugacy, in the point or plane stabilizer. A point--plane Borel is retained
as a subgroup of either parabolic, so no maximal-parabolic assumption is made.

Source: Aschbacher (1981), A pushing up theorem for finite groups, 8.2(7),
and Aschbacher--Smith C.2.7(3), printed pp.145--146. The fixed-space
construction is `TwoLocalCover.fixedRadical`.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The normalizer of a nontrivial 2-radical is covered by a native symplectic
point or plane parabolic, up to the actual conjugation action. -/
theorem radical_normalizer_parabolic_cover
    (U : Subgroup (Sp F)) (hU : U.IsPRadical 2) :
    ∃ g : Sp F,
      (normalizer (U : Set (Sp F))).map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      (normalizer (U : Set (Sp F))).map (MulAut.conj g).toMonoidHom ≤ planeParabolic := by
  apply twoLocal_parabolic_cover_of_charTwo
  exact ⟨U, hU.1, hU.isPGroup, rfl⟩

/-- The source-level point--plane flag alternative is included explicitly:
the Borel is contained in each native parabolic. -/
theorem radical_normalizer_borel_subgroup_cover
    (U : Subgroup (Sp F)) (hU : U.IsPRadical 2) :
    ∃ g : Sp F,
      (normalizer (U : Set (Sp F))).map (MulAut.conj g).toMonoidHom ≤ pointParabolic ∨
      (normalizer (U : Set (Sp F))).map (MulAut.conj g).toMonoidHom ≤ planeParabolic :=
  radical_normalizer_parabolic_cover U hU

end Theory.SpecificGroups.SymplecticFour
