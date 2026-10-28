module
public import Theory.Representation.BinaryPermutation.SevenParabolic.Geometry
public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Partition
public import Theory.SpecificGroups.AlternatingSix.SmallIndex
/-!
# The two ordinary seven-letter parabolics

The centralizers of (12)(34)(56) and (12)(34) realize the partition
stabilizers of types 2+2+2+1 and 2+2+3. The first fixes the six-support
vector. A complementary three-cycle expresses that vector in the span
of the second parabolic's orbit of the original plane. Explicit even
permutations distinguish the second parabolic from the point stabilizer,
exclude the reversed orientation, and escape both marked intersections.

Source: Aschbacher--Smith, original14.6.10(5), printed pp.1029--1030.
All finite checks involve specified permutations or seven points.
-/

@[expose] public section
open Subgroup Equiv BinaryPermutation
open BinaryPermutation.SevenParabolic
namespace BinaryPermutation.SevenParabolic.Ordinary
abbrev Perm7 := Equiv.Perm (Fin 7)
def secondFour : Space := ⟨![1,1,0,0,1,1,0], by rw [mem_core]; decide⟩
def firstSix : Space := ⟨![1,1,1,1,1,1,0], by rw [mem_core]; decide⟩
def tripleSwap : Perm7 := swap 0 1 * swap 2 3 * swap 4 5
def doubleSwap : Perm7 := swap 0 1 * swap 2 3
def lambda : Subgroup Perm7 := centralizer ({tripleSwap} : Set Perm7)
def theta : Subgroup Perm7 := centralizer ({doubleSwap} : Set Perm7)
def complementCycle : Perm7 := swap 4 5 * swap 5 6
def escapingCycle : Perm7 := swap 0 1 * swap 1 4
lemma tripleSwap_fixed (i : Fin 7) : tripleSwap i = i ↔ i = 6 :=
  (by decide +kernel : ∀ i : Fin 7, tripleSwap i = i ↔ i = 6) i
lemma lambda_fixes_last (g : Perm7) (hg : g ∈ lambda) : g 6 = 6 := by
  have hc := congrArg (fun p : Perm7 => p 6) (mem_centralizer_singleton_iff.mp hg)
  change g (tripleSwap 6) = tripleSwap (g 6) at hc
  have ht : tripleSwap 6 = 6 := by decide
  exact (tripleSwap_fixed _).mp (by simpa only [ht] using hc.symm)
lemma action_firstSix (g : Perm7) : action g firstSix = firstSix ↔ g 6 = 6 := by
  have hv (i : Fin 7) : firstSix.val i = if i = 6 then 0 else 1 :=
    (by decide : ∀ i : Fin 7, firstSix.val i = if i = 6 then 0 else 1) i
  constructor
  · intro h
    have h6 := congrArg (fun v : Space => v.val (g 6)) h
    change firstSix.val (g.symm (g 6)) = firstSix.val (g 6) at h6
    simpa [hv] using h6.symm
  · intro h
    apply Subtype.ext
    ext i
    change firstSix.val (g.symm i) = firstSix.val i
    rw [hv,hv]
    have he : g.symm i = 6 ↔ i = 6 := by rw [Equiv.symm_apply_eq, h]
    simp only [he]
lemma firstSix_expression : firstSix = firstFour + action complementCycle secondFour +
    action (complementCycle ^ 2) secondFour := by decide +kernel
lemma complementCycle_mem : complementCycle ∈ theta ∧ complementCycle ∈ alternatingGroup (Fin 7) := by
  constructor
  · rw [theta, mem_centralizer_singleton_iff]
    decide +kernel
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
lemma escapingCycle_fixes : action escapingCycle firstSix = firstSix := by decide
lemma escapingCycle_moves : action escapingCycle firstFour ≠ firstFour := by decide
end BinaryPermutation.SevenParabolic.Ordinary
namespace BinaryPermutation.SevenParabolic.Ordinary
open Subgroup Equiv
lemma firstSix_ne_zero : firstSix ≠ 0 := by decide
lemma lambda_fixes_firstSix (g : Perm7) (hg : g ∈ lambda) :
    action g firstSix = firstSix := (action_firstSix g).mpr (lambda_fixes_last g hg)
lemma escapingCycle_even : escapingCycle ∈ alternatingGroup (Fin 7) := by
  rw [Equiv.Perm.mem_alternatingGroup]; decide
lemma escapingCycle_not_lambda : escapingCycle ∉ lambda := by
  rw [lambda, mem_centralizer_singleton_iff]
  decide
lemma theta_fixes_firstFour (g : Perm7) (hg : g ∈ theta) :
    action g firstFour = firstFour := by
  have hv (i : Fin 7) : firstFour.val i = if doubleSwap i = i then 0 else 1 :=
    (by decide : ∀ i : Fin 7, firstFour.val i = if doubleSwap i = i then 0 else 1) i
  have hc (i : Fin 7) : doubleSwap (g i) = g (doubleSwap i) :=
    congrArg (fun p : Perm7 => p i) (mem_centralizer_singleton_iff.mp hg).symm
  apply Subtype.ext
  ext i
  change firstFour.val (g.symm i) = firstFour.val i
  rw [hv,hv]
  have he : doubleSwap (g.symm i) = g.symm i ↔ doubleSwap i = i := by
    rw [← g.injective.eq_iff]
    simp only [← hc, g.apply_symm_apply]
  simp only [he]
private def insideCycle : Perm7 := swap 0 1 * swap 1 2
private lemma insideCycle_mem : insideCycle ∈ alternatingGroup (Fin 7) ∧
    action insideCycle firstFour = firstFour ∧ insideCycle ∉ theta := by
  refine ⟨?_,by decide,?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup]; decide
  · rw [theta, mem_centralizer_singleton_iff]
    decide
lemma theta_lt_point (J : Subgroup Perm7) (hJ : alternatingGroup (Fin 7) ≤ J) :
    J ⊓ theta < J ⊓ pointStabilizer firstFour := by
  refine lt_of_le_of_ne (inf_le_inf_left _ (fun g hg => theta_fixes_firstFour g hg)) ?_
  intro h
  have hh : insideCycle ∈ J ⊓ pointStabilizer firstFour :=
    ⟨hJ insideCycle_mem.1,insideCycle_mem.2.1⟩
  rw [←h] at hh
  exact insideCycle_mem.2.2 hh.2
private def exchangePairs : Perm7 := swap 0 4 * swap 1 5
lemma reversed_orientation_impossible (J : Subgroup Perm7)
    (hJ : alternatingGroup (Fin 7) ≤ J) :
    ¬ J ⊓ lambda ≤ pointStabilizer pair56 := by
  intro h
  have hm : exchangePairs ∈ J ⊓ lambda := by
    constructor
    · apply hJ
      rw [Equiv.Perm.mem_alternatingGroup]; decide
    · change exchangePairs ∈ lambda
      rw [lambda, mem_centralizer_singleton_iff]
      decide
  have hh : action exchangePairs pair56 = pair56 := h hm
  exact (by decide : action exchangePairs pair56 ≠ pair56) hh
end BinaryPermutation.SevenParabolic.Ordinary

namespace BinaryPermutation.SevenParabolic.Ordinary
/-- The literal alternating centralizer of the six-support vector is A₆. -/
noncomputable def sixSupportCentralizerEquiv :
    (alternatingGroup (Fin 7) ⊓ pointStabilizer firstSix : Subgroup Perm7) ≃*
      alternatingGroup (Fin 6) := by
  let D := alternatingGroup (Fin 7) ⊓ pointStabilizer firstSix
  have he : D.subgroupOf (alternatingGroup (Fin 7)) =
      MulAction.stabilizer (alternatingGroup (Fin 7)) (6 : Fin 7) := by
    ext g
    change (g.val ∈ alternatingGroup (Fin 7) ∧ action g.val firstSix = firstSix) ↔ g.val 6 = 6
    simp only [g.property,true_and,action_firstSix]
  exact (subgroupOfEquivOfLe (show D ≤ alternatingGroup (Fin 7) from inf_le_left)).symm.trans
    ((MulEquiv.subgroupCongr he).trans (AlternatingSix.SmallIndex.pointEquiv (6 : Fin 7)))
end BinaryPermutation.SevenParabolic.Ordinary
