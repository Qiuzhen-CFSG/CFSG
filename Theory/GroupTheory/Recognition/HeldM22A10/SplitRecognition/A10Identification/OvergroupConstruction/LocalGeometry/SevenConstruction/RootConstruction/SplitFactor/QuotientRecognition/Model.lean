module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.RootConstruction.SplitFactor.RootQuotient
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.Tactic

/-!
# The involution centralizer used in Held's A7 recognition

The actual centralizer of (01)(23) in A7 has order 24 and every homomorphism
from it to an odd-order finite group is trivial. The order follows by taking
the even half of the symmetric-group centralizer. Twenty-four explicit words
in a reflection, a rotation and a disjoint three-cycle then exhaust it. The
reflection, rotation and the reflection times the three-cycle have two-power
order, which proves triviality of every odd-order image.

The cardinality argument adapts the existing permutation calculation in
GorensteinWalter/ASevenInvolutionCentralizerOddPart.lean; the small word
certificate is checked by the kernel.

Source: D. Held, Illinois J. Math. 13 (1969), 224–240,
DOI 10.1215/ijm/1256053756, Lemma 5.4, printed p.237.
-/

open Subgroup Equiv

namespace Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.QuotientRecognition.Model

private abbrev A7 := alternatingGroup (Fin 7)
private theorem involution_cycleType :
    (sevenInvolution : Equiv.Perm (Fin 7)).cycleType = {2, 2} := by
  decide

private theorem perm_centralizer_card :
    Nat.card (Subgroup.centralizer
      ({(sevenInvolution : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))) = 48 := by
  rw [Equiv.Perm.nat_card_centralizer, involution_cycleType]
  norm_num

/-- The centralizer of the concrete double transposition in `A₇` has order
`24`. -/
public theorem centralizer_card :
    Nat.card sevenInvolutionCentralizer = 24 := by
  let C : Subgroup (Equiv.Perm (Fin 7)) :=
    Subgroup.centralizer ({(sevenInvolution : Equiv.Perm (Fin 7))} : Set (Equiv.Perm (Fin 7)))
  let A : Subgroup (Equiv.Perm (Fin 7)) := alternatingGroup (Fin 7)
  have hAindex : A.index = 2 := alternatingGroup.index_eq_two
  have hcC : (Equiv.swap (4 : Fin 7) 5) ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyP : y = (sevenInvolution : Equiv.Perm (Fin 7)) := by simpa using hy
    subst y
    decide
  have hcA : (Equiv.swap (4 : Fin 7) 5) ∉ A := by
    intro h
    change Equiv.Perm.sign (Equiv.swap (4 : Fin 7) 5) = 1 at h
    norm_num [Equiv.Perm.sign_swap] at h
    exact (by decide : (4 : Fin 7) ≠ 5) h
  let D : Subgroup (Equiv.Perm (Fin 7)) := Lattice.inf C A
  have hrel : D.relIndex C = 2 := by
    rw [Subgroup.relIndex_eq_two_iff]
    refine ⟨Equiv.swap (4 : Fin 7) 5, hcC, ?_⟩
    intro b hbC
    have hbcC : b * Equiv.swap (4 : Fin 7) 5 ∈ C := C.mul_mem hbC hcC
    by_cases hbA : b ∈ A
    · right
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbC, hbA⟩
      · intro hbc
        have hbcA : b * Equiv.swap (4 : Fin 7) 5 ∈ A :=
          (Subgroup.mem_inf.mp hbc).2
        have hiff : b * Equiv.swap (4 : Fin 7) 5 ∈ A ↔
            (b ∈ A ↔ Equiv.swap (4 : Fin 7) 5 ∈ A) :=
          Subgroup.mul_mem_iff_of_index_two hAindex
        have hbnot : ¬ b ∈ A := by
          intro hbA'
          exact hcA ((hiff.mp hbcA).1 hbA')
        exact hbnot hbA
    · left
      constructor
      · exact Subgroup.mem_inf.mpr ⟨hbcC, by
          exact (Subgroup.mul_mem_iff_of_index_two hAindex).2
            (iff_of_false hbA hcA)⟩
      · intro hbD
        exact hbA ((Subgroup.mem_inf.mp hbD).2)
  have hrel' : (D.subgroupOf C).index = 2 := by
    exact hrel
  have hperm : Nat.card C = 48 := perm_centralizer_card
  have hDleC : D ≤ C := inf_le_left
  have hcardSub : Nat.card (D.subgroupOf C) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDleC).toEquiv
  have hcardC : Nat.card D * 2 = Nat.card C := by
    have h := Subgroup.card_mul_index (D.subgroupOf C)
    rw [hcardSub, hrel'] at h
    exact h
  have hcard24 : Nat.card D = 24 := by omega
  have hmap : (Subgroup.centralizer ({sevenInvolution} : Set A7)).map A7.subtype = D := by
    ext p
    constructor
    · rintro ⟨x, hxC, rfl⟩
      constructor
      · change (x : Equiv.Perm (Fin 7)) ∈ C
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyP : y = (sevenInvolution : Equiv.Perm (Fin 7)) := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hxC) sevenInvolution (by simp)
        exact congrArg Subtype.val hcomm
      · exact x.2
    · rintro ⟨hpC, hpA⟩
      refine ⟨⟨p, hpA⟩, ?_, rfl⟩
      have hx : (⟨p, hpA⟩ : A7) ∈ Subgroup.centralizer ({sevenInvolution} : Set A7) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hyA : y = sevenInvolution := by simpa using hy
        subst y
        have hcomm := (Subgroup.mem_centralizer_iff.mp hpC)
          (sevenInvolution : Equiv.Perm (Fin 7)) (by simp)
        exact Subtype.ext hcomm
      exact hx
  have hcardMap : Nat.card (Subgroup.centralizer ({sevenInvolution} : Set A7)) =
      Nat.card ((Subgroup.centralizer ({sevenInvolution} : Set A7)).map A7.subtype) := by
    exact Nat.card_congr (Subgroup.equivMapOfInjective
      (Subgroup.centralizer ({sevenInvolution} : Set A7)) A7.subtype
        A7.subtype_injective).toEquiv
  rw [hcardMap, hmap, hcard24]


private def a : A7 := ⟨swap 4 5 * swap 5 6, by simp [Perm.sign_mul]⟩
private def v : A7 := ⟨swap 0 2 * swap 2 1 * swap 1 3 * swap 4 5,
  by simp [Perm.sign_mul]⟩
private def s : A7 := ⟨swap 0 1 * swap 4 5, by simp [Perm.sign_mul]⟩

private theorem a_mem : a ∈ sevenInvolutionCentralizer := by
  apply mem_centralizer_singleton_iff.mpr
  decide +kernel
private theorem v_mem : v ∈ sevenInvolutionCentralizer := by
  apply mem_centralizer_singleton_iff.mpr
  decide +kernel
private theorem s_mem : s ∈ sevenInvolutionCentralizer := by
  apply mem_centralizer_singleton_iff.mpr
  decide +kernel

private def word (i : Fin 2 × Fin 4 × Fin 3) : sevenInvolutionCentralizer :=
  ⟨s ^ i.1.val * v ^ i.2.1.val * a ^ i.2.2.val,
    mul_mem (mul_mem (pow_mem s_mem _) (pow_mem v_mem _)) (pow_mem a_mem _)⟩

private theorem word_injective : Function.Injective word := by
  have h : Function.Injective (fun i =>
      (((word i : A7) : Perm (Fin 7)) 0, ((word i : A7) : Perm (Fin 7)) 2,
        ((word i : A7) : Perm (Fin 7)) 4)) := by decide +kernel
  intro i j hij
  exact h (congrArg (fun g : sevenInvolutionCentralizer =>
    (((g : A7) : Perm (Fin 7)) 0, ((g : A7) : Perm (Fin 7)) 2,
      ((g : A7) : Perm (Fin 7)) 4)) hij)

private theorem word_surjective : Function.Surjective word := by
  apply (Function.Injective.bijective_of_nat_card_le word_injective ?_).2
  rw [centralizer_card]
  simp

private theorem eq_one_of_two_power {K : Type*} [Group K] [Finite K]
    (hK : Odd (Nat.card K)) {x : K} {n : ℕ} (h : x ^ (2 ^ n) = 1) : x = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h) (orderOf_dvd_natCard x)
  have hc : (2 ^ n).Coprime (Nat.card K) := hK.coprime_two_left.pow_left n
  simpa [hc.gcd_eq_one] using hd

public theorem hom_to_odd_trivial {K : Type*} [Group K] [Finite K]
    (hK : Odd (Nat.card K)) (f : sevenInvolutionCentralizer →* K)
    (x : sevenInvolutionCentralizer) : f x = 1 := by
  let ss : sevenInvolutionCentralizer := ⟨s, s_mem⟩
  let vv : sevenInvolutionCentralizer := ⟨v, v_mem⟩
  let aa : sevenInvolutionCentralizer := ⟨a, a_mem⟩
  have hs : f ss = 1 := eq_one_of_two_power hK (n := 1) (by
    rw [← map_pow]
    have he : ss ^ (2 ^ 1) = 1 := by decide +kernel
    rw [he, map_one])
  have hv : f vv = 1 := eq_one_of_two_power hK (n := 2) (by
    rw [← map_pow]
    have he : vv ^ (2 ^ 2) = 1 := by decide +kernel
    rw [he, map_one])
  have hsa : f (ss * aa) = 1 := eq_one_of_two_power hK (n := 1) (by
    rw [← map_pow]
    have he : (ss * aa) ^ (2 ^ 1) = 1 := by decide +kernel
    rw [he, map_one])
  have ha : f aa = 1 := by simpa [map_mul, hs] using hsa
  obtain ⟨i, rfl⟩ := word_surjective x
  change f (ss ^ i.1.val * vv ^ i.2.1.val * aa ^ i.2.2.val) = 1
  simp only [map_mul, map_pow, hs, hv, ha, one_pow, mul_one]

end Theory.GroupTheory.HeldM22A10.A10Identification.OvergroupConstruction.LocalGeometry.SevenConstruction.SplitFactor.QuotientRecognition.Model
