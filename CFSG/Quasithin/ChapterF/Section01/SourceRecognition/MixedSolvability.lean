module
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import Theory.SpecificGroups.DihedralSolvable
public import BenderSuzuki.MatrixGroups.SuzukiZero

/-!
# Endpoint solvability of the original dihedral/Suzuki--A5 pair

The original D10 or Sz(2) local quotient is solvable, whereas A5 is not.
The source parabolic has solvable quotient by its local factor, so the
actual first parabolic is solvable and the second is nonsolvable. This
uses precisely the quotient markings produced in Chapter15.2.4, without
an ambient Sylow assumption or finiteness of the generated completion.

The missing (5,5) rank-two recognition need only rule out this mixed
solvability. This module supplies the consumer side of that implication;
it does not assert the exclusion or classification.

Source: Aschbacher--Smith 15.2.4, printed pp.1106--1107, and F.1.12,
printed pp.262--264.
-/

public section
namespace CFSG.Quasithin.ChapterF.Source
open Subgroup
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
theorem HypothesisF11.a5_parabolic_not_solvable (h : HypothesisF11 L S) (i : Fin 2)
    (e : (L i ⧸ pCore 2 (L i)) ≃* alternatingGroup (Fin 5)) :
    ¬ Group.IsSolvable (parabolic L S i) := by
  intro hs
  let := (h.parabolic_solvable_iff_local_quotient i).mp hs
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

theorem HypothesisF11.dihedral_suzuki_a5_mixed_solvability
    (h : HypothesisF11 L S)
    (h0 : Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃* DihedralGroup 5) ∨
      Nonempty ((L 0 ⧸ pCore 2 (L 0)) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))
    (h1 : Nonempty ((L 1 ⧸ pCore 2 (L 1)) ≃* alternatingGroup (Fin 5))) :
    Group.IsSolvable (parabolic L S 0) ∧ ¬ Group.IsSolvable (parabolic L S 1) := by
  refine ⟨(h.parabolic_solvable_iff_local_quotient 0).mpr ?_,
    h.a5_parabolic_not_solvable 1 h1.some⟩
  rcases h0 with he | he
  · let := GLS3.Chapter5.dihedralGroup_isSolvable 5
    exact Group.isSolvable_of_surjective
      (f := he.some.symm.toMonoidHom) he.some.symm.surjective
  · let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
    exact Group.isSolvable_of_surjective
      (f := he.some.symm.toMonoidHom) he.some.symm.surjective
end CFSG.Quasithin.ChapterF.Source
