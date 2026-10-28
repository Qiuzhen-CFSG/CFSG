module

public import Theory.AtlasPort.LinearGroups.G2.ExceptionalLocalQuotients.Numbering
public import Theory.GroupTheory.PResidual.Defs

/-!
# The marked derived binary overlap lies in every completion's two-residual

The two cubics vanish in every two-group quotient. In the existing checked
word tables, common row 2 then evaluates to a squared on the first side
and a cubed on the second. Compatibility forces a = 1; the common generator
and cubics generate the local rows, so the whole overlap vanishes. This
retains both literal inclusion maps and gives the residual-placement input
for the full binary G₂ branch of Aschbacher–Smith F.6.18(11).
-/

public section
open Subgroup
open Atlas.G2.LieAutomorphismExtensions
open Atlas.G2.LieAutomorphismExtensions.BinaryAmalgamBound
namespace Atlas.G2.BinaryParabolicPair

private theorem groupWord_one_right {G : Type*} [Group G] (a : G) (w : List Bool) :
    groupWord a 1 w = a ^ w.count false := by
  induction w with
  | nil => simp [groupWord]
  | cons b w ih => cases b <;> simp [groupWord,ih,pow_succ']

private theorem cubic_image_one {G : Type*} [Group G] (hG : IsPGroup 2 G)
    {A : Type*} [Group A] (f : A →* G) (a : A) (hc : a^3=1) : f a = 1 := by
  obtain ⟨n,hn⟩ := hG (f a)
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 3 2).pow_right n)
  · apply orderOf_dvd_of_pow_eq_one
    rw [← map_pow,hc,map_one]
  · exact orderOf_dvd_of_pow_eq_one hn

private theorem left_cube : binaryConcreteRealization.left.equiv 2 ^ 3 = 1 := by
  calc
    _ = binaryConcreteRealization.left.equiv (leftTable.mul 2 (leftTable.mul 2 2)) := by
      rw [binaryConcreteRealization.left.mul_eq,binaryConcreteRealization.left.mul_eq]
      simp only [pow_succ,pow_zero,one_mul,mul_assoc]
    _ = binaryConcreteRealization.left.equiv 0 := by congr 1
    _ = 1 := binaryConcreteRealization.left.one_eq

private theorem right_cube : binaryConcreteRealization.right.equiv 2 ^ 3 = 1 := by
  calc
    _ = binaryConcreteRealization.right.equiv (rightTable.mul 2 (rightTable.mul 2 2)) := by
      rw [binaryConcreteRealization.right.mul_eq,binaryConcreteRealization.right.mul_eq]
      simp only [pow_succ,pow_zero,one_mul,mul_assoc]
    _ = binaryConcreteRealization.right.equiv 0 := by congr 1
    _ = 1 := binaryConcreteRealization.right.one_eq

private theorem image_row {A G : Type*} [Group A] [Group G]
    {T : WordTable} (E : T.Realization A) (hT : T.Valid) (f : A →* G)
    (hb : f (E.equiv 2) = 1) (i : Fin 96) :
    f (E.equiv i) = f (E.equiv 1) ^ (T.word i).count false := by
  have he := congrArg f (E.word_eq hT i)
  simpa only [map_groupWord,hb,groupWord_one_right] using he.symm

theorem binary_amalgam_two_group_middle_trivial
    {G : Type*} [Group G] (hG : IsPGroup 2 G)
    (l : BinaryLeft →* G) (r : BinaryRight →* G)
    (hc : ∀ x : binaryOverlap, l (binaryAmalgam.left x) = r (binaryAmalgam.right x))
    (x : binaryOverlap) : l (binaryAmalgam.left x) = 1 := by
  let a := l (binaryConcreteRealization.left.equiv 1)
  have hb : l (binaryConcreteRealization.left.equiv 2) = 1 :=
    cubic_image_one hG l _ left_cube
  have hd : r (binaryConcreteRealization.right.equiv 2) = 1 :=
    cubic_image_one hG r _ right_cube
  have ha : r (binaryConcreteRealization.right.equiv 1) = a := by
    change _ = l (binaryConcreteRealization.left.equiv 1)
    have hlc := binaryConcreteRealization.left_overlap 1
    have hrc := binaryConcreteRealization.right_overlap 1
    rw [left_valid.common] at hlc
    rw [right_valid.common] at hrc
    exact (congrArg r hrc).trans ((hc _).symm.trans (congrArg l hlc).symm)
  have hl := image_row binaryConcreteRealization.left left_valid l hb
  have hr (i : Fin 96) : r (binaryConcreteRealization.right.equiv i) =
      a ^ (rightTable.word i).count false :=
    (image_row binaryConcreteRealization.right right_valid r hd i).trans
      (congrArg (fun g => g ^ (rightTable.word i).count false) ha)
  have he := (congrArg l (binaryConcreteRealization.left_overlap 2)).trans
    ((hc _).trans (congrArg r (binaryConcreteRealization.right_overlap 2)).symm)
  have he := (hl _).symm.trans (he.trans (hr _))
  change a ^ 2 = a ^ 3 at he
  have ha1 : a = 1 := by
    have hh : a ^ 2 * 1 = a ^ 2 * a := by simpa only [mul_one,pow_succ] using he
    exact (mul_left_cancel hh).symm
  let i := binaryConcreteRealization.middle.symm x
  have hh := (congrArg l (binaryConcreteRealization.left_overlap i)).symm.trans (hl _ )
  change l (binaryAmalgam.left (binaryConcreteRealization.middle i)) = a ^ _ at hh
  have hx : l (binaryAmalgam.left (binaryConcreteRealization.middle i)) = 1 := by
    simpa only [ha1,one_pow] using hh
  exact (congrArg (fun b => l (binaryAmalgam.left b))
    (binaryConcreteRealization.middle.apply_symm_apply x)).symm.trans hx

theorem binary_amalgam_middle_le_twoResidual
    {G : Type*} [Group G]
    (l : BinaryLeft →* G) (r : BinaryRight →* G)
    (hc : ∀ x : binaryOverlap, l (binaryAmalgam.left x) = r (binaryAmalgam.right x))
    (x : binaryOverlap) : l (binaryAmalgam.left x) ∈ pResidual 2 G := by
  apply Subgroup.mem_sInf.mpr
  rintro N ⟨hN,hP⟩
  let := hN
  apply (QuotientGroup.eq_one_iff _).mp
  exact binary_amalgam_two_group_middle_trivial hP ((QuotientGroup.mk' N).comp l)
    ((QuotientGroup.mk' N).comp r) (fun x => congrArg (QuotientGroup.mk' N) (hc x)) x
end Atlas.G2.BinaryParabolicPair
