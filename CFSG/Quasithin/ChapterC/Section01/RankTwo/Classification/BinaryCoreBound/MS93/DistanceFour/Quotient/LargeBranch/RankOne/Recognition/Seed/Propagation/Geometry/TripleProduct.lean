module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Bruhat

/-!
# Three-parabolic factorization in the actual binary flag geometry

For either orientation of an incident flag, every matrix in SL₃(2) is a
product from the first, second and first full parabolics. The existing binary
Bruhat decomposition reduces this to twelve short permutation identities.
Conjugating the flag preserves the factorization and the specified quotient.

This supplies an alternative to the problematic two-core generation formula
in MS93 (1993), printed p.911, using the genuine flag geometry of p.905.
It asserts neither generation by two-cores nor any seed containment.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed

open Subgroup
open Matrix.PSL3Two (lineParabolicSL pointParabolicSL)
private def P (i : Bool) : Subgroup SL := if i then lineParabolicSL else pointParabolicSL
private def leftWord : Bool → Fin 6 → Fin 6
  | false => ![0,1,0,1,0,1]
  | true => ![0,0,2,0,2,2]
private def middleWord : Bool → Fin 6 → Fin 6
  | false => ![0,0,2,2,2,2]
  | true => ![0,1,0,1,1,1]
private def rightWord : Bool → Fin 6 → Fin 6
  | false => ![0,0,0,0,1,1]
  | true => ![0,0,0,2,0,2]
private theorem words : ∀ (i : Bool) (j : Fin 6),
    Matrix.PSL3Two.Bruhat.perm (leftWord i j) ∈ P i ∧
    Matrix.PSL3Two.Bruhat.perm (middleWord i j) ∈ P (!i) ∧
    Matrix.PSL3Two.Bruhat.perm (rightWord i j) ∈ P i ∧
    Matrix.PSL3Two.Bruhat.perm j = Matrix.PSL3Two.Bruhat.perm (leftWord i j) *
      Matrix.PSL3Two.Bruhat.perm (middleWord i j) * Matrix.PSL3Two.Bruhat.perm (rightWord i j) := by
  intro i
  cases i <;> simp only [P, Bool.false_eq_true, Bool.not_false, Bool.not_true, if_false, if_true] <;> decide +kernel

private theorem standard_triple (i : Bool) (g : SL) :
    ∃ a ∈ P i, ∃ b ∈ P (!i), ∃ c ∈ P i, g = a * b * c := by
  obtain ⟨u, w, v, rfl⟩ := Matrix.PSL3Two.Bruhat.decomposition g
  obtain ⟨ha, hb, hc, he⟩ := words i w
  have hupper (k : Fin 8) : Matrix.PSL3Two.Bruhat.upper k ∈ P i := by
    cases i
    · exact (Matrix.PSL3Two.Bruhat.upper_mem k).1
    · exact (Matrix.PSL3Two.Bruhat.upper_mem k).2
  refine ⟨Matrix.PSL3Two.Bruhat.upper u * Matrix.PSL3Two.Bruhat.perm (leftWord i w), (P i).mul_mem (hupper _) ha,
    Matrix.PSL3Two.Bruhat.perm (middleWord i w), hb,
    Matrix.PSL3Two.Bruhat.perm (rightWord i w) * Matrix.PSL3Two.Bruhat.upper v, (P i).mul_mem hc (hupper _), ?_⟩
  rw [he]
  simp only [mul_assoc]

/-- Full parabolic factorization at a specified flag, for either orientation. -/
theorem modelParabolic_triple_product (flag : SL) (i : Bool) (g : SL) :
    ∃ a ∈ modelParabolic flag i, ∃ b ∈ modelParabolic flag (!i),
      ∃ c ∈ modelParabolic flag i, g = a * b * c := by
  obtain ⟨a, ha, b, hb, c, hc, he⟩ := standard_triple i ((MulAut.conj flag).symm g)
  refine ⟨MulAut.conj flag a, mem_map_of_mem _ ha,
    MulAut.conj flag b, mem_map_of_mem _ hb,
    MulAut.conj flag c, mem_map_of_mem _ hc, ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg (MulAut.conj flag) he

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Seed
