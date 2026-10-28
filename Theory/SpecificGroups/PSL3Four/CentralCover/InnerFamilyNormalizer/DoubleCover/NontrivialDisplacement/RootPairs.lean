module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover
public import Theory.GroupTheory.SpecificGroups.KleinFourGenerators

/-!
# Swapped root pairs and the kernel of a central projection

In a group of class at most two, an involution interchanging two root groups
has three diagonal commutators, from the nonzero vectors of a binary plane.
If every projectively fixed element is fixed, equal projected diagonal
commutators must be equal upstairs. Expanding the third diagonal then reduces
all four root commutators to two. Independence of their projected images
makes the projection injective on the derived subgroup.

`RootPair` is an explicit local presentation to be constructed for a Sylow
subgroup of the double cover; this file does not assert that construction.
The transfer argument in the parent uses perfectness to rule out the resulting
injectivity. No four-cover comparison is used.

Source: the covering facts in Aschbacher–Smith I.2.2(3b), printed pp.409–410,
and the center-C₂ graph-field case of 16.4.9(2), printed p.1191
(combined manuscript, 1 March 2004).
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
variable {K B : Type*} [Group K] [Group B]

/-- A class-two root presentation. The four cross commutators generate the
 derived subgroup, their squares are one, and the three diagonal commutators
 have the same projective image. The two off-diagonal images are independent.
 This records local group structure, not a displacement conclusion. -/
structure RootPair (f : K →* B) (b : MulAut K) where
  x : K
  y : K
  class_two : _root_.commutator K ≤ center K
  derived_generated : _root_.commutator K ≤
    closure ({⁅b x, x⁆, ⁅b x, y⁆, ⁅b y, x⁆, ⁅b y, y⁆} : Set K)
  derived_square : ∀ z ∈ _root_.commutator K, z ^ 2 = 1
  diagonal_images : f ⁅b x, x⁆ = f ⁅b y, y⁆
  third_image : f ⁅b x, x⁆ = f ⁅b (x * y), x * y⁆
  cross_one : f ⁅b x, y⁆ ≠ 1
  cross_two : f ⁅b y, x⁆ ≠ 1
  cross_product : f (⁅b x, y⁆ * ⁅b y, x⁆) ≠ 1

private theorem comm_center (h : _root_.commutator K ≤ center K) (u v : K) :
    ⁅u, v⁆ ∈ center K :=
  h (commutator_mem_commutator (mem_top _) (mem_top _))

private theorem central_comm_left (h : _root_.commutator K ≤ center K) (u v w : K) :
    ⁅u * v, w⁆ = ⁅v, w⁆ * ⁅u, w⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul,
    (mem_center_iff.mp (comm_center h v w) u), mul_inv_cancel_right]

private theorem central_comm_right (h : _root_.commutator K ≤ center K) (u v w : K) :
    ⁅u, v * w⁆ = ⁅u, v⁆ * ⁅u, w⁆ := by
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc
    ⁅u, v⁆ * v * ⁅u, w⁆ * v⁻¹ = ⁅u, v⁆ * (v * ⁅u, w⁆) * v⁻¹ := by group
    _ = ⁅u, v⁆ * (⁅u, w⁆ * v) * v⁻¹ := by
      rw [mem_center_iff.mp (comm_center h u w) v]
    _ = _ := by group

theorem involutive_apply (b : MulAut K) (hb : b ^ 2 = 1) (u : K) :
    b (b u) = u := by
  have he := congrArg (fun a : MulAut K => a u) hb
  simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using he

private theorem norm_action (b : MulAut K) (hb : b ^ 2 = 1) (u : K) :
    b (u * b u) = ⁅b u, u⁆ * (u * b u) := by
  rw [map_mul, involutive_apply b hb]
  simp only [commutatorElement_def]
  group

private theorem diagonal_eq_of_fixed_lifts (f : K →* B) (b : MulAut K)
    (hb : b ^ 2 = 1) (hc : _root_.commutator K ≤ center K)
    (hfix : ∀ u, f (b u) = f u → b u = u)
    (x y : K) (he : f ⁅b x, x⁆ = f ⁅b y, y⁆) :
    ⁅b x, x⁆ = ⁅b y, y⁆ := by
  let nx := x * b x
  let ny := y * b y
  have hn : b (nx * ny⁻¹) = (⁅b x, x⁆ * ⁅b y, y⁆⁻¹) * (nx * ny⁻¹) := by
    rw [map_mul, map_inv, norm_action b hb x, norm_action b hb y,
      _root_.mul_inv_rev]
    have hz := mem_center_iff.mp ((center K).inv_mem (comm_center hc (b y) y))
      (nx * ny⁻¹)
    calc
      (⁅b x, x⁆ * nx) * (ny⁻¹ * ⁅b y, y⁆⁻¹) =
          ⁅b x, x⁆ * ((nx * ny⁻¹) * ⁅b y, y⁆⁻¹) := by group
      _ = ⁅b x, x⁆ * (⁅b y, y⁆⁻¹ * (nx * ny⁻¹)) := by rw [hz]
      _ = _ := by group
  have hsame : b (nx * ny⁻¹) = nx * ny⁻¹ := hfix _ (by
    rw [hn, map_mul, map_mul, map_inv, he, mul_inv_cancel, one_mul])
  have hmul : ⁅b x, x⁆ * ⁅b y, y⁆⁻¹ = 1 := by
    apply mul_right_cancel (b := nx * ny⁻¹)
    simpa only [one_mul] using hn.symm.trans hsame
  exact mul_inv_eq_one.mp hmul

/-- Trivial displacement collapses the four root commutators to two independent images. -/
theorem RootPair.kernel_inf_derived_eq_bot (f : K →* B) (b : MulAut K)
    (hb : b ^ 2 = 1) (d : RootPair f b)
    (hfix : ∀ u, f (b u) = f u → b u = u) :
    f.ker ⊓ _root_.commutator K = ⊥ := by
  let p := ⁅b d.x, d.y⁆
  let q := ⁅b d.y, d.x⁆
  let t := ⁅b d.x, d.x⁆
  have ht : ⁅b d.y, d.y⁆ = t :=
    (diagonal_eq_of_fixed_lifts f b hb d.class_two hfix _ _ d.diagonal_images).symm
  have ht2 : t * t = 1 := by
    simpa only [pow_two] using d.derived_square t
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hthird : ⁅b (d.x * d.y), d.x * d.y⁆ = p * q := by
    rw [map_mul, central_comm_left d.class_two,
      central_comm_right d.class_two, central_comm_right d.class_two, ht]
    change (q * t) * (t * p) = p * q
    calc
      (q * t) * (t * p) = q * (t * t) * p := by group
      _ = q * p := by rw [ht2, mul_one]
      _ = p * q := mem_center_iff.mp (comm_center d.class_two (b d.x) d.y) q
  have htval : t = p * q :=
    (diagonal_eq_of_fixed_lifts f b hb d.class_two hfix _ _ d.third_image).trans hthird
  have hd : _root_.commutator K ≤ closure ({p, q} : Set K) := by
    apply d.derived_generated.trans
    apply (closure_le _).mpr
    intro u hu
    have hp : p ∈ closure ({p, q} : Set K) := subset_closure (by simp)
    have hq : q ∈ closure ({p, q} : Set K) := subset_closure (by simp)
    rcases hu with rfl | rfl | rfl | rfl
    · change t ∈ _
      rw [htval]
      exact mul_mem hp hq
    · exact hp
    · exact hq
    · rw [ht, htval]
      exact mul_mem hp hq
  have hp2 : p * p = 1 := by
    simpa only [pow_two] using d.derived_square p
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hq2 : q * q = 1 := by
    simpa only [pow_two] using d.derived_square q
      (commutator_mem_commutator (mem_top _) (mem_top _))
  have hpq : Commute p q :=
    (mem_center_iff.mp (comm_center d.class_two (b d.x) d.y) q).symm
  apply bot_unique
  rintro u ⟨hu, hdU⟩
  have hu' : f u = 1 := hu
  rcases (mem_closure_pair_iff p q hp2 hq2 hpq u).mp (hd hdU) with rfl | rfl | rfl | rfl
  · exact mem_bot.mpr rfl
  · exact (d.cross_one hu').elim
  · exact (d.cross_two hu').elim
  · exact (d.cross_product hu').elim


variable {H : Type*} [Group H]

/-- A root presentation inside an actual invariant Sylow subgroup of the cover. -/
structure LiftedRootPair (c : PerfectCentralCovering.Cover H PSL) (a : MulAut H) where
  sylow : Sylow 2 H
  action : MulAut sylow
  compatible : ∀ x : sylow, (action x : H) = a x
  roots : RootPair (c.toMonoidHom.comp (sylow : Subgroup H).subtype) action


end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
