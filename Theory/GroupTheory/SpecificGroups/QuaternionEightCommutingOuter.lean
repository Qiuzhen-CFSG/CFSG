module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.Fintype.Prod

/-!
# Commuting outer involutions of the quaternion group

Two commuting outer automorphisms of square one on Q₈ have inner product.
This is the elementary comparison of their transpositions in Out(Q₈) ≃ S₃.
We prove the comparison directly, without constructing that quotient: encode
an automorphism by the images of the two quaternion generators, and use a
kernel-checked finite table. The result transports along any quaternion model.

The generator-image encoding follows `QuaternionEightAut.lean`. This comparison
is used in Janko–Thompson (1970), §4, case (b)(ii), printed p.391,
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

namespace QuaternionGroup
private abbrev Q := QuaternionGroup 2
private def pairMap (p : Q × Q) : Q → Q
  | a i => p.1 ^ i.val
  | xa i => p.2 * p.1 ^ i.val
set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem commuting_outer_table : ∀ p q : Q × Q,
    (∀ x, pairMap p (pairMap p x) = x) →
    (∀ x, pairMap q (pairMap q x) = x) →
    (¬ ∃ b, ∀ x, pairMap p x = b*x*b⁻¹) →
    (¬ ∃ b, ∀ x, pairMap q x = b*x*b⁻¹) →
    (∀ x, pairMap p (pairMap q x) = pairMap q (pairMap p x)) →
    ∃ b, ∀ x, pairMap p (pairMap q x) = b*x*b⁻¹ := by
  decide

private theorem pairMap_aut (e : MulAut Q) (x : Q) :
    pairMap (e (a 1), e (xa 0)) x = e x := by
  cases x with
  | a i =>
    change (e (a 1)) ^ i.val = e (a i)
    rw [← map_pow, a_one_pow, ZMod.natCast_zmod_val]
  | xa i =>
    change e (xa 0) * (e (a 1)) ^ i.val = e (xa i)
    rw [← map_pow, ← map_mul, a_one_pow, ZMod.natCast_zmod_val, xa_mul_a, zero_add]

/-- Commuting outer involutions of the quaternion group of order eight have
inner product. Equivalently, their images in its outer automorphism group coincide. -/
public theorem exists_conj_of_commuting_outer_involutions_two
    (e f : MulAut (QuaternionGroup 2)) (he : e^2=1) (hf : f^2=1)
    (heo : ¬ ∃ b, e = MulAut.conj b) (hfo : ¬ ∃ b, f = MulAut.conj b)
    (hef : Commute e f) : ∃ b, e*f = MulAut.conj b := by
  have he2 (x : Q) : e (e x) = x := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun he x
  have hf2 (x : Q) : f (f x) = x := by
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply] using DFunLike.congr_fun hf x
  have heo' : ¬ ∃ b, ∀ x, e x = b*x*b⁻¹ := by
    rintro ⟨b, hb⟩
    exact heo ⟨b, MulEquiv.ext hb⟩
  have hfo' : ¬ ∃ b, ∀ x, f x = b*x*b⁻¹ := by
    rintro ⟨b, hb⟩
    exact hfo ⟨b, MulEquiv.ext hb⟩
  have hc (x : Q) : e (f x) = f (e x) := DFunLike.congr_fun hef.eq x
  obtain ⟨b, hb⟩ := commuting_outer_table (e (a 1), e (xa 0)) (f (a 1), f (xa 0))
    (by simpa only [pairMap_aut] using he2)
    (by simpa only [pairMap_aut] using hf2)
    (by simpa only [pairMap_aut] using heo')
    (by simpa only [pairMap_aut] using hfo')
    (by simpa only [pairMap_aut] using hc)
  exact ⟨b, MulEquiv.ext (by simpa only [pairMap_aut, MulAut.mul_apply, MulAut.conj_apply] using hb)⟩


/-- The commuting-outer-involution comparison transported to any quaternion
group of order eight. -/
public theorem exists_conj_of_commuting_outer_involutions_of_equiv
    {G : Type*} [Group G] (model : G ≃* QuaternionGroup 2)
    (e f : MulAut G) (he : e^2=1) (hf : f^2=1)
    (heo : ¬ ∃ b, e = MulAut.conj b) (hfo : ¬ ∃ b, f = MulAut.conj b)
    (hef : Commute e f) : ∃ b, e*f = MulAut.conj b := by
  let a := MulAut.congr model
  have ho (g : MulAut G) (hg : ¬ ∃ b, g = MulAut.conj b) :
      ¬ ∃ b, a g = MulAut.conj b := by
    rintro ⟨b, hb⟩
    apply hg
    refine ⟨model.symm b, ?_⟩
    ext x
    apply model.injective
    have hh := DFunLike.congr_fun hb (model x)
    simpa [a, MulAut.congr_apply, MulAut.conj_apply] using hh
  obtain ⟨b, hb⟩ := exists_conj_of_commuting_outer_involutions_two (a e) (a f)
    (by rw [← map_pow, he, map_one]) (by rw [← map_pow, hf, map_one])
    (ho e heo) (ho f hfo) (hef.map a)
  refine ⟨model.symm b, ?_⟩
  ext x
  apply model.injective
  have hh := DFunLike.congr_fun hb (model x)
  simpa [a, MulAut.congr_apply, MulAut.conj_apply] using hh
end QuaternionGroup

