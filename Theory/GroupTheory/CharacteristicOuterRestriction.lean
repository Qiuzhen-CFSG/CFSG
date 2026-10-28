module

public import Theory.GroupTheory.CharacteristicRestrictionInnerSquares
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.OddKernelInvolutionFibers
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Detecting outer automorphisms on a characteristic subgroup

Restriction normalizes the actual conjugation image. It therefore maps Out(B)
to the quotient of that image's normalizer by the image itself. The map is
injective when automorphisms fixing the characteristic subgroup are inner.

For an odd self-centralizing characteristic subgroup, a central involution in
the quotient supplies an innerness criterion. Correct a kernel automorphism
by an element of the subgroup's centralizer so that it fixes the involution.
Its remaining displacements centralize both the subgroup and the involution;
if these fixed points are central, perfectness kills the displacement.

Source application: Aschbacher--Smith, A.3.6(4), printed pp.43--45, and
11.4.3, printed p.778. No splitting or elementary-kernel hypothesis is used.
-/

public section
noncomputable section
open Subgroup
namespace Subgroup.CharacteristicOuterRestriction

variable {B : Type*} [Group B] (N : Subgroup B) [N.Characteristic]

/-- The literal conjugation image on the characteristic kernel. -/
abbrev innerActionImage : Subgroup (MulAut N) :=
  (MulAut.conjNormal : B →* MulAut N).range

/-- Its relative normalizer quotient, with the image normal only inside its normalizer. -/
abbrev ActionNormalizerQuotient :=
  normalizer (innerActionImage N : Set (MulAut N)) ⧸
    (innerActionImage N).subgroupOf (normalizer (innerActionImage N : Set (MulAut N)))

/-- Restriction, with its codomain restricted to the actual action normalizer. -/
def normalizerRestriction : MulAut B →*
    normalizer (innerActionImage N : Set (MulAut N)) :=
  (MulAut.characteristic N).codRestrict _
    (characteristic_mem_normalizer_conjNormal_range N)

private theorem inner_le_normalizerRestriction_kernel :
    MulAut.innerSubgroup B ≤
      ((QuotientGroup.mk' ((innerActionImage N).subgroupOf
        (normalizer (innerActionImage N : Set (MulAut N))))).comp
          (normalizerRestriction N)).ker := by
  rintro a ⟨b, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mpr
  change MulAut.characteristic N (MulAut.conj b) ∈ innerActionImage N
  rw [characteristic_conj_eq_conjNormal]
  exact ⟨b, rfl⟩

/-- Outer restriction is defined without assuming splitting or faithfulness. -/
def outerRestriction : MulAut.Outer B →* ActionNormalizerQuotient N :=
  QuotientGroup.lift (MulAut.innerSubgroup B)
    ((QuotientGroup.mk' ((innerActionImage N).subgroupOf
      (normalizer (innerActionImage N : Set (MulAut N))))).comp
        (normalizerRestriction N)) (inner_le_normalizerRestriction_kernel N)

/-- Detecting inner automorphisms in the pointwise restriction kernel makes
outer restriction injective. -/
theorem outerRestriction_injective
    (hk : (MulAut.characteristic N).ker ≤ MulAut.innerSubgroup B) :
    Function.Injective (outerRestriction N) := by
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  symm
  apply le_antisymm _ (inner_le_normalizerRestriction_kernel N)
  intro a ha
  have hm' := (QuotientGroup.eq_one_iff (normalizerRestriction N a)).mp ha
  have hm : MulAut.characteristic N a ∈ innerActionImage N := hm'
  obtain ⟨b, hb⟩ := hm
  have hcorr : MulAut.conj b⁻¹ * a ∈ (MulAut.characteristic N).ker := by
    change MulAut.characteristic N (MulAut.conj b⁻¹ * a) = 1
    rw [map_mul, characteristic_conj_eq_conjNormal, map_inv, hb, inv_mul_cancel]
  have hi := hk hcorr
  have he : a = MulAut.conj b * (MulAut.conj b⁻¹ * a) := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  rw [he]
  exact (MulAut.innerSubgroup B).mul_mem ⟨b, rfl⟩ hi

private theorem displacement_centralizes (a : MulAut B)
    (ha : MulAut.characteristic N a = 1) (g : B) :
    g⁻¹ * a g ∈ centralizer (N : Set B) := by
  have hfix (n : B) (hn : n ∈ N) : a n = n :=
    congrArg Subtype.val (DFunLike.congr_fun ha (⟨n, hn⟩ : N))
  intro n hn
  have he := hfix (g * n * g⁻¹) ((inferInstance : N.Normal).conj_mem n hn g)
  simp only [map_mul, map_inv, hfix n hn] at he
  have hh := congrArg (fun x : B => g⁻¹ * x * a g) he
  group at hh
  simpa only [mul_assoc, zpow_neg_one] using hh.symm

/-- An odd self-centralizing characteristic kernel detects inner automorphisms
if a central quotient involution has no noncentral fixed point in its centralizer. -/
theorem restriction_kernel_le_inner_of_involution [Finite B] [Group.IsPerfect B]
    (hself : centralizer (N : Set B) ≤ N)
    (hodd : Odd (Nat.card N)) (t : B) (ht : orderOf t = 2)
    (htcentral : QuotientGroup.mk' N t ∈ center (B ⧸ N))
    (hfixed : centralizer (N : Set B) ⊓ centralizer ({t} : Set B) ≤ center B) :
    (MulAut.characteristic N).ker ≤ MulAut.innerSubgroup B := by
  intro a ha
  let C := centralizer (N : Set B)
  let q := QuotientGroup.mk' C
  have hcodd : Nat.Coprime 2 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk']
    exact hodd.coprime_two_left.of_dvd_right (card_dvd_of_le hself)
  have hsame : q t = q (a t) :=
    QuotientGroup.eq.mpr (displacement_centralizes N a ha t)
  obtain ⟨c, hc⟩ := involutions_same_image_conj_ker q hcodd ht
    ((a.orderOf_eq t).trans ht) hsame
  have hcC : (c : B) ∈ C := by
    simpa only [q, QuotientGroup.ker_mk'] using c.property
  let b : MulAut B := MulAut.conj (c : B)⁻¹ * a
  have hbN : MulAut.characteristic N b = 1 := by
    rw [show b = MulAut.conj (c : B)⁻¹ * a from rfl, map_mul, ha, mul_one,
      characteristic_conj_eq_conjNormal]
    rw [← MonoidHom.mem_ker, MulAut.conjNormal_ker_eq_centralizer]
    exact C.inv_mem hcC
  have hbt : b t = t := by
    change (c : B)⁻¹ * a t * ((c : B)⁻¹)⁻¹ = t
    rw [← hc]
    group
  have hfix (n : B) (hn : n ∈ N) : b n = n :=
    congrArg Subtype.val (DFunLike.congr_fun hbN (⟨n, hn⟩ : N))
  have hdisp (g : B) : g⁻¹ * b g ∈ center B := by
    apply hfixed
    refine ⟨displacement_centralizes N b hbN g, ?_⟩
    have hn : g * t * g⁻¹ * t⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      change QuotientGroup.mk' N (g * t * g⁻¹ * t⁻¹) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv,
        mem_center_iff.mp htcentral, mul_inv_cancel_right, mul_inv_cancel]
    have he := hfix _ hn
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hbt] at he
    have hh := congrArg (fun x : B => g⁻¹ * x * t * b g) he
    group at hh
    apply mem_centralizer_singleton_iff.mpr
    simpa only [mul_assoc, zpow_neg_one] using hh
  have hb : b = 1 := MulAut.eq_one_of_central_displacement b hdisp
  refine ⟨(c : B), ?_⟩
  have he : a = MulAut.conj (c : B) * b := by
    dsimp [b]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simpa only [hb, mul_one] using he.symm

end Subgroup.CharacteristicOuterRestriction
