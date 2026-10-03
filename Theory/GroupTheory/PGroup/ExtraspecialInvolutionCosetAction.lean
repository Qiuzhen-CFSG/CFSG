module

public import Theory.GroupTheory.PGroup.ClassTwoCyclicCenter
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Involution cosets and fusion in extraspecial two-groups

The nonidentity central cosets represented by square-one elements carry a
canonical permutation action of the automorphism group. In an extraspecial
two-group every noncentral central coset is a single inner conjugacy class:
a nontrivial commutator is the unique nonidentity central element.
Consequently, an ambient orbit on these cosets lifts to ambient conjugacy.

If there are five such cosets and five divides the actual permutation image,
a five-cycle joins all of them. This gives the involution fusion step for the
quaternion–dihedral central product, with its separate geometric census and
outer-image calculation left as explicit inputs. No transitivity of an
odd-order action on the ten individual involutions is asserted; the inner
action supplies the central adjustment.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup
open scoped commutatorElement

namespace IsExtraspecial

/-- Noncentral elements with the same central coset are inner conjugate. -/
public theorem isConj_of_center_quotient_eq
    {H : Type*} [Group H] [IsExtraspecial 2 H]
    {x y : H} (hx : x ∉ center H)
    (hxy : QuotientGroup.mk' (center H) x = QuotientGroup.mk' (center H) y) :
    IsConj x y := by
  by_cases heq : x = y
  · exact heq ▸ IsConj.refl x
  obtain ⟨a, ha⟩ : ∃ a : H, a * x ≠ x * a := by
    simpa only [mem_center_iff, not_forall] using hx
  have hc : ⁅a, x⁆ ∈ center H :=
    (IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient
      (commutator_mem_commutator (mem_top a) (mem_top x))
  have hcne : ⁅a, x⁆ ≠ 1 := fun h => ha (commutatorElement_eq_one_iff_mul_comm.mp h)
  have hd : y / x ∈ center H := QuotientGroup.eq_iff_div_mem.mp hxy.symm
  have hdne : y / x ≠ 1 := by
    intro h
    rw [div_eq_mul_inv] at h
    exact heq (eq_of_mul_inv_eq_one h).symm
  obtain ⟨z, _, hz⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp
    (IsExtraspecial.center_order_p 2 H)
  have he : ⁅a, x⁆ = y / x := congrArg Subtype.val
    ((hz ⟨⁅a, x⁆, hc⟩ (fun h => hcne (congrArg Subtype.val h))).trans
      (hz ⟨y / x, hd⟩ (fun h => hdne (congrArg Subtype.val h))).symm)
  apply isConj_iff.mpr
  refine ⟨a, ?_⟩
  calc
    a * x * a⁻¹ = ⁅a, x⁆ * x := by group
    _ = y := by rw [he, div_eq_mul_inv, inv_mul_cancel_right]

end IsExtraspecial

namespace Subgroup

/-- Nonidentity central cosets admitting a square-one representative. -/
@[expose] public def CentralInvolutionCosets (H : Type*) [Group H] :=
  {v : H ⧸ center H // v ≠ 1 ∧ ∃ x : H, x ^ 2 = 1 ∧ QuotientGroup.mk' (center H) x = v}

public instance {H : Type*} [Group H] [Finite H] : Finite (CentralInvolutionCosets H) := by
  unfold CentralInvolutionCosets
  infer_instance

private theorem centralInvolutionCoset_map {H : Type*} [Group H]
    (a : MulAut H) (v : CentralInvolutionCosets H) :
    quotientAut (center H) a v.val ≠ 1 ∧
      ∃ x : H, x ^ 2 = 1 ∧ QuotientGroup.mk' (center H) x = quotientAut (center H) a v.val := by
  refine ⟨fun h => v.property.1 ((quotientAut (center H) a).injective (h.trans (map_one _).symm)), ?_⟩
  obtain ⟨x, hx, he⟩ := v.property.2
  exact ⟨a x, by rw [← map_pow, hx, map_one], by rw [← quotientAut_apply_mk, he]⟩

/-- The natural automorphism action on central involution cosets. -/
public def centralInvolutionCosetAction {H : Type*} [Group H] :
    MulAut H →* Equiv.Perm (CentralInvolutionCosets H) where
  toFun a :=
    { toFun v := ⟨quotientAut (center H) a v.val, centralInvolutionCoset_map a v⟩
      invFun v := ⟨quotientAut (center H) a⁻¹ v.val, centralInvolutionCoset_map a⁻¹ v⟩
      left_inv v := by
        apply Subtype.ext
        change (quotientAut (center H) a⁻¹ * quotientAut (center H) a) v.val = v.val
        rw [← map_mul, inv_mul_cancel, map_one]
        rfl
      right_inv v := by
        apply Subtype.ext
        change (quotientAut (center H) a * quotientAut (center H) a⁻¹) v.val = v.val
        rw [← map_mul, mul_inv_cancel, map_one]
        rfl }
  map_one' := by
    ext v
    apply Subtype.ext
    change quotientAut (center H) 1 v.val = v.val
    rw [map_one]
    rfl
  map_mul' a b := by
    ext v
    apply Subtype.ext
    change quotientAut (center H) (a * b) v.val =
      quotientAut (center H) a (quotientAut (center H) b v.val)
    rw [map_mul]
    rfl

/-- The permutation action agrees with the canonical action on the central quotient. -/
@[simp] public theorem centralInvolutionCosetAction_val {H : Type*} [Group H]
    (a : MulAut H) (v : CentralInvolutionCosets H) :
    (centralInvolutionCosetAction a v).val = quotientAut (center H) a v.val := by
  rfl

/-- The point represented by a noncentral square-one element. -/
@[expose] public def centralInvolutionCoset {H : Type*} [Group H]
    (x : H) (hx : x ^ 2 = 1) (hxZ : x ∉ center H) : CentralInvolutionCosets H :=
  ⟨QuotientGroup.mk' (center H) x, fun h => hxZ ((QuotientGroup.eq_one_iff x).mp h), x, hx, rfl⟩

/-- An ambient conjugator between central involution cosets lifts to an element conjugator. -/
public theorem isConj_of_centralInvolutionCoset_orbit
    {K : Type*} [Group K] (H : Subgroup K) [H.Normal] [IsExtraspecial 2 H]
    (x y : H) (hx : x ^ 2 = 1) (hxZ : x ∉ center H)
    (hy : y ^ 2 = 1) (hyZ : y ∉ center H)
    (g : K)
    (hg : centralInvolutionCosetAction (MulAut.conjNormal g)
      (centralInvolutionCoset x hx hxZ) = centralInvolutionCoset y hy hyZ) :
    IsConj (x : K) (y : K) := by
  have hcoset : QuotientGroup.mk' (center H) (MulAut.conjNormal g x) =
      QuotientGroup.mk' (center H) y := by
    have hh := congrArg Subtype.val hg
    change quotientAut (center H) (MulAut.conjNormal g)
      (QuotientGroup.mk' (center H) x) = QuotientGroup.mk' (center H) y at hh
    rwa [quotientAut_apply_mk] at hh
  have hn : MulAut.conjNormal g x ∉ center H := by
    intro h
    apply hxZ
    rw [mem_center_iff] at h ⊢
    intro z
    apply (MulAut.conjNormal g : MulAut H).injective
    simpa only [map_mul] using h (MulAut.conjNormal g z)
  obtain ⟨a, ha⟩ := isConj_iff.mp
    (IsExtraspecial.isConj_of_center_quotient_eq hn hcoset)
  apply isConj_iff.mpr
  refine ⟨(a : K) * g, ?_⟩
  have hh := congrArg Subtype.val ha
  change (a : K) * (g * (x : K) * g⁻¹) * (a : K)⁻¹ = (y : K) at hh
  calc
    ((a : K) * g) * (x : K) * ((a : K) * g)⁻¹ =
      (a : K) * (g * (x : K) * g⁻¹) * (a : K)⁻¹ := by group
    _ = y := hh

private theorem exists_pow_apply_eq_of_five_points
    {X : Type*} [Finite X] (hX : Nat.card X = 5)
    (p : Equiv.Perm X) (hp : orderOf p = 5) (x y : X) :
    ∃ n : ℕ, (p ^ n) x = y := by
  classical
  let := Fintype.ofFinite X
  have hcard : Fintype.card X = 5 := by rwa [Nat.card_eq_fintype_card] at hX
  have hcycle : p.IsCycle := Equiv.Perm.isCycle_of_prime_order' (by rw [hp]; decide)
    (by rw [hcard, hp]; decide)
  have hsupport : p.support = Finset.univ := Finset.eq_univ_of_card _
    (by rw [← hcycle.orderOf, hp, hcard])
  apply hcycle.exists_pow_eq
  · exact Equiv.Perm.mem_support.mp (hsupport ▸ Finset.mem_univ x)
  · exact Equiv.Perm.mem_support.mp (hsupport ▸ Finset.mem_univ y)

/-- A five-divisible image on five central involution cosets fuses all noncentral involutions. -/
public theorem isConj_noncentral_involutions_of_five_cosets
    {K : Type*} [Group K] [Finite K]
    (H : Subgroup K) [H.Normal] [IsExtraspecial 2 H]
    (hpoints : Nat.card (CentralInvolutionCosets H) = 5)
    (hfive : 5 ∣ Nat.card ((centralInvolutionCosetAction (H := H)).comp
      (MulAut.conjNormal : K →* MulAut H)).range)
    (x y : H) (hx : orderOf x = 2) (hxZ : x ∉ center H)
    (hy : orderOf y = 2) (hyZ : y ∉ center H) :
    IsConj (x : K) (y : K) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let a := (centralInvolutionCosetAction (H := H)).comp (MulAut.conjNormal : K →* MulAut H)
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := a.range) 5 hfive
  obtain ⟨g, hg⟩ := q.property
  have hg5 : orderOf (a g) = 5 := by rw [hg, orderOf_coe, hq]
  have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
  have hy2 : y ^ 2 = 1 := hy ▸ pow_orderOf_eq_one y
  obtain ⟨n, hn⟩ := exists_pow_apply_eq_of_five_points hpoints (a g) hg5
    (centralInvolutionCoset x hx2 hxZ) (centralInvolutionCoset y hy2 hyZ)
  apply isConj_of_centralInvolutionCoset_orbit H x y hx2 hxZ hy2 hyZ (g ^ n)
  change a (g ^ n) _ = _
  rwa [map_pow]

end Subgroup
