module

public import Theory.GroupAction.FourthPowerFixed
public import Mathlib.GroupTheory.Index

/-!
# The displacement line of a noninvariant binary hyperplane

An automorphism a of fourth power one on a binary group of order sixteen
has fixed groups of orders two and four for a and a², respectively.
If a hyperplane is invariant under a² but not under a, its a²-displacement
is a line outside the fixed group of a.

The square displacement has equal image and kernel, of order four.
Every invariant hyperplane contains this image, so its displacement has
order two. If that line were fixed by a, the hyperplane would be the
kernel of the third displacement, which is invariant under a.

Source: the linear calculation in D. Parrott, *A characterization of the
Tits' simple group* (1972), pp.674 and 677, expressed without coordinates.
-/

open Subgroup
open scoped IsMulCommutative

namespace MulAut

/-- The square displacement of an a²-invariant hyperplane which is not
a-invariant is a line containing no nonidentity a-fixed element. The
homomorphism is supplied with its literal evaluation formula. -/
public theorem square_displacement_of_noninvariant_hyperplane
    {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (a : MulAut W) (ha4 : a ^ 4 = 1) (hW : Nat.card W = 16)
    (hF : Nat.card (FixedPoints.subgroup (zpowers a) W) = 2)
    (hF2 : Nat.card (FixedPoints.subgroup (zpowers (a ^ 2)) W) = 4)
    (U : Subgroup W) (hU : Nat.card U = 8)
    (hU2 : ∀ u ∈ U, a (a u) ∈ U)
    (hUnot : ∃ u ∈ U, a u ∉ U) :
    ∃ s : W →* W, (∀ w, s w = a (a w) * w) ∧
      Nat.card (U.map s) = 2 ∧ ∀ w ∈ U.map s, w ≠ 1 → a w ≠ w := by
  have hself (w : W) : w * w = 1 := by
    simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 W) w
  have hinv (w : W) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (hself w)
  have hfour (w : W) : a (a (a (a w))) = w :=
    congrArg (fun f : MulAut W => f w) ha4
  let d : W →* W := {
    toFun := fun w => a w * w
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul]; ac_rfl }
  let s : W →* W := {
    toFun := fun w => a (a w) * w
    map_one' := by simp
    map_mul' := by intros; simp only [map_mul]; ac_rfl }
  let F := FixedPoints.subgroup (zpowers a) W
  let F2 := FixedPoints.subgroup (zpowers (a ^ 2)) W
  have hdker : d.ker = F := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixed_zpowers_iff]
    change a w * w = 1 ↔ a w = w
    rw [mul_eq_one_iff_eq_inv, hinv]
  have hsker : s.ker = F2 := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixed_zpowers_iff]
    change a (a w) * w = 1 ↔ a (a w) = w
    rw [mul_eq_one_iff_eq_inv, hinv]
  have hFF2 : F ≤ F2 := by
    intro w hw
    have hh := (mem_fixed_zpowers_iff a w).mp hw
    apply (mem_fixed_zpowers_iff _ _).mpr
    change a (a w) = w
    rw [hh, hh]
  have hsrangeLe : s.range ≤ F2 := by
    rintro _ ⟨w, rfl⟩
    apply (mem_fixed_zpowers_iff _ _).mpr
    change a (a (a (a w) * w)) = a (a w) * w
    simp only [map_mul, hfour]
    exact mul_comm _ _
  have hsrangeCard : Nat.card s.range = 4 := by
    have hc := s.ker.card_mul_index
    rw [index_ker, hsker, hF2, hW] at hc
    omega
  have hsrange : s.range = F2 := eq_of_le_of_card_ge hsrangeLe (by
    rw [hsrangeCard, hF2])
  have hUindex : U.index = 2 := by
    have hc := U.card_mul_index
    rw [hU, hW] at hc
    omega
  have hF2U : F2 ≤ U := by
    rw [← hsrange]
    rintro _ ⟨w, rfl⟩
    apply (U.mul_mem_iff_of_index_two hUindex).mpr
    exact ⟨fun hh => by simpa only [hfour] using hU2 _ hh, hU2 w⟩
  have hFindex : F.index = 8 := by
    have hc := F.card_mul_index
    rw [hF, hW] at hc
    omega
  have hF2index : F2.index = 4 := by
    have hc := F2.card_mul_index
    rw [hF2, hW] at hc
    omega
  have hline : Nat.card (U.map s) = 2 := by
    have hc := relIndex_mul_index hF2U
    rw [hUindex, hF2index, ← hsker, relIndex_ker] at hc
    omega
  let t := d.comp s
  have htrange : Nat.card t.range = 2 := by
    rw [show t.range = s.range.map d from MonoidHom.range_comp d s, hsrange,
      ← relIndex_ker, hdker]
    have hc := relIndex_mul_index hFF2
    rw [hF2index, hFindex] at hc
    omega
  have htker : Nat.card t.ker = 8 := by
    have hc := t.ker.card_mul_index
    rw [index_ker, htrange, hW] at hc
    omega
  have hta (w : W) : t (a w) = a (t w) := by
    change a (a (a (a w)) * a w) * (a (a (a w)) * a w) =
      a (a (a (a w) * w) * (a (a w) * w))
    simp only [map_mul]
  refine ⟨s, fun _ => rfl, hline, ?_⟩
  intro w hw hwne hwfix
  have hw2 : w ^ 2 = 1 := by simpa only [pow_two] using hself w
  have hgen : zpowers w = U.map s := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hw)
    rw [Nat.card_zpowers, orderOf_eq_prime hw2 hwne, hline]
  have hLfixed : U.map s ≤ d.ker := by
    rw [← hgen, hdker]
    exact zpowers_le.mpr ((mem_fixed_zpowers_iff _ _).mpr hwfix)
  have hUt : U ≤ t.ker := by
    intro u hu
    exact hLfixed (mem_map_of_mem s hu)
  have hUeq : U = t.ker := eq_of_le_of_card_ge hUt (by rw [htker, hU])
  obtain ⟨u, hu, hnu⟩ := hUnot
  apply hnu
  rw [hUeq, MonoidHom.mem_ker, hta]
  have htu : t u = 1 := hUt hu
  rw [htu, map_one]

end MulAut
