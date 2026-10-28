module

public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Data
public import Theory.SpecificGroups.Held.RankOneLocalPair.Maximal.ConcreteMaximality.Cover.Conjugator

/-!
# Soundness of max5 cover computations

The checker evaluates the literal transported representative, inverse positive
max5 word and inverse short representative. Equality at the four proved base
points gives the exact centralizer equation in CoverChecks. No subgroup label
or external permutation computation is used in this implication.
Source: ../source/README.md, ATLAS HeG1-max5W1.
-/

@[expose] public section
namespace Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
open Held Held.TwoLocalCandidates
open Held.LocalPairs.PairCoverage.SylowOvergroups
open Held.LocalPairs.PairCoverage.SylowOvergroups.RepresentativeVerification

/-- The exact three words specified by the existing production data. -/
def actualRow (j : Fin 4831) : Row :=
  (decodeWord (representativeText j), rightWord j, shortWord (coverIndex j))

private def rightPerm (w : List Bool) : Equiv.Perm (Fin 2058) :=
  (w.map fun b => if b then Cores.Tables2.p1 else Cores.Tables2.p0).prod

private theorem rightPerm_eq (j : Fin 4831) :
    rightPerm (rightWord j) = representation (rightFactor j) := by
  have h0 : Cores.Tables2.p0 = representation max5First := Cores.Tables2.p0_eq
  have h1 : Cores.Tables2.p1 = representation max5Second := Cores.Tables2.p1_eq
  simp only [rightPerm, rightFactor, map_list_prod, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b <;> simp only [Bool.false_eq_true, if_false, if_true, h0, h1]

private theorem rightInverse_eq (w : List Bool) (t : Fin 2058) :
    w.foldl (fun t b => if b then Cores.Tables2.backward1 t else
      Cores.Tables2.backward0 t) t = (rightPerm w)⁻¹ t := by
  unfold rightPerm
  induction w generalizing t with
  | nil => rfl
  | cons b w ih =>
    rw [List.foldl_cons, List.map_cons, List.prod_cons, mul_inv_rev, Equiv.Perm.mul_apply]
    rw [← ih]
    cases b <;> rfl

private theorem conjugatorPermutation_eq : conjugatorPermutation = fastConjugator := rfl

set_option maxRecDepth 4096 in
private theorem rawLeft_eq (j : Fin 4831) (t : Fin 2058) :
    rawLeft (actualRow j).1 (actualRow j).2.1 (actualRow j).2.2 t =
      representation (leftFactor j) t := by
  have ht : representation (transport (representative j)) =
      fastConjugator⁻¹ * representation (representative j) * fastConjugator := by
    rw [transport, MulAut.conj_apply, inv_inv, map_mul, map_mul, map_inv,
      fastConjugator_eq]
  have hs : representation (shortRepresentative (coverIndex j)) =
      wordEval fastA fastB (shortWord (coverIndex j)) := by
    rw [shortRepresentative, map_wordEval, fastA_eq, fastB_eq]
    rfl
  rw [leftFactor, map_mul, map_mul, map_inv, map_inv, ht, hs]
  simp only [Equiv.Perm.mul_apply]
  unfold rawLeft actualRow
  rw [conjugatorInverseTable_eq, conjugatorTable_eq, rightInverse_eq,
    rightPerm_eq, inverseWordAction_eq, conjugatorPermutation_eq]
  change (fastConjugator⁻¹ : Equiv.Perm _) (representativeAction j _) = _
  rw [representativeAction_eq]

private theorem representation_mul_apply (x y : He) (p : Fin 2058) :
    representation (x*y) p = representation x (representation y p) := by
  rw [map_mul, Equiv.Perm.mul_apply]

set_option maxRecDepth 4096 in
/-- A checked row proves the literal max5 centralizer-membership equation. -/
theorem rowCheck_sound (j : Fin 4831) (h : rowCheck (actualRow j) = true) :
    leftFactor j * max5First ^ 4 = max5First ^ 4 * leftFactor j := by
  apply Held.eq_of_four_point_images
  intro i
  have hi := List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt)
  have he : (⟨i.val % 2058, Nat.mod_lt _ (by decide)⟩ : Fin 2058) =
      ⟨i.val, by omega⟩ := Fin.ext (Nat.mod_eq_of_lt (by omega))
  have hi' := beq_iff_eq.mp hi
  rw [he] at hi'
  change rawLeft (actualRow j).1 (actualRow j).2.1 (actualRow j).2.2
    (Cores.Tables2.p2 _) = Cores.Tables2.p2
    (rawLeft (actualRow j).1 (actualRow j).2.1 (actualRow j).2.2 _) at hi'
  rw [rawLeft_eq, rawLeft_eq, CentralInvolutionBounds.p2_eq_representation] at hi'
  exact (representation_mul_apply _ _ _).trans (hi'.trans (representation_mul_apply _ _ _).symm)

end Held.RankOneLocalPair.ConcreteMaximality.CoverCertificate
