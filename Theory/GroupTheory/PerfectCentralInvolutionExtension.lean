module

public import Theory.GroupTheory.PerfectCentralCoverExistence
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.IntervalCases

/-!
# Perfect bases and involutory complements in central extensions

A splitting theorem for finite central p-group extensions of a group lifts
any embedded copy of that group, by applying it to the literal full preimage.
Two lifts of the factors of a direct product commute when the first factor is
perfect: conjugation gives a second lift of the same homomorphism, and the
uniqueness theorem for maps from perfect groups identifies the two lifts.

For a semidirect product of a perfect base with C₂, a base lift extends to the
whole group if the complement generator is conjugate, in the ambient target,
to the image of a square-one element of the base. Lift a conjugator to obtain
a square-one lift of the generator; uniqueness on the perfect base supplies
the semidirect-product relation.

The consumer is the odd-prime Sp₄ two-primary calculation: two SL₂ factors
form the base, and the plane swap fuses to a one-plane sign. This is the
local lifting step behind GLS3 §6.1 and Aschbacher–Smith I.1.1–4,
printed pp.407–408. No multiplier bound is assumed by these general lemmas.
-/

public section

open Subgroup
namespace PerfectCentralCovering
universe u v w

private def involutionHom {E : Type*} [Group E] (t : E) (ht : t ^ 2 = 1) :
    Multiplicative (ZMod 2) →* E where
  toFun a := t ^ a.toAdd.val
  map_one' := by simp
  map_mul' a b := by
    have ha : a.toAdd.val < 2 := ZMod.val_lt _
    have hb : b.toAdd.val < 2 := ZMod.val_lt _
    change t ^ (a.toAdd + b.toAdd).val = t ^ a.toAdd.val * t ^ b.toAdd.val
    rw [ZMod.val_add]
    interval_cases ha' : a.toAdd.val <;> interval_cases hb' : b.toAdd.val <;>
      simp_all [pow_two]

private theorem involutionHom_generator {E : Type*} [Group E] (t : E) (ht : t ^ 2 = 1) :
    involutionHom t ht (.ofAdd 1) = t := by
  change t ^ 1 = t
  exact pow_one t

private theorem c2_hom_ext {G : Type*} [Group G]
    (a b : Multiplicative (ZMod 2) →* G)
    (h : a (.ofAdd 1) = b (.ofAdd 1)) : a = b := by
  apply MonoidHom.ext
  intro c
  have hc : c.toAdd = 0 ∨ c.toAdd = 1 := by
    have hv := ZMod.val_lt c.toAdd
    have hv' : c.toAdd.val = 0 ∨ c.toAdd.val = 1 := by omega
    rcases hv' with hv' | hv'
    · left
      exact ZMod.val_injective 2 hv'
    · right
      exact ZMod.val_injective 2 hv'
  rcases hc with hc | hc
  · have he : c = 1 := hc
    simp [he]
  · have he : c = .ofAdd 1 := hc
    simpa [he] using h

/-- A perfect-base semidirect product lifts once its base lifts and its
involutory complement is conjugate to an involution in that base. -/
theorem exists_lift_semidirect_of_involution_fusion
    {N E G : Type*} [Group N] [Group.IsPerfect N] [Group E] [Group G]
    (f : E →* G) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (φ : Multiplicative (ZMod 2) →* MulAut N)
    (j : N ⋊[φ] Multiplicative (ZMod 2) →* G)
    (s : N →* E) (hs : f.comp s = j.comp SemidirectProduct.inl)
    (n : N) (hn : n ^ 2 = 1)
    (hconj : IsConj (j (SemidirectProduct.inl n))
      (j (SemidirectProduct.inr (.ofAdd 1)))) :
    ∃ t : N ⋊[φ] Multiplicative (ZMod 2) →* E, f.comp t = j := by
  have hs' (x : N) : f (s x) = j (SemidirectProduct.inl x) := DFunLike.congr_fun hs x
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  obtain ⟨a, ha⟩ := hf g
  let y := a * s n * a⁻¹
  have hy : y ^ 2 = 1 := by simp [y, conj_pow, ← map_pow, hn]
  let c := involutionHom y hy
  have hc : f.comp c = j.comp SemidirectProduct.inr := by
    apply c2_hom_ext
    change f (involutionHom y hy (.ofAdd 1)) = j (SemidirectProduct.inr (.ofAdd 1))
    rw [involutionHom_generator]
    change f (a * s n * a⁻¹) = _
    rw [map_mul, map_mul, map_inv, ha, hs' n]
    exact hg
  have hc' (b : Multiplicative (ZMod 2)) :
      f (c b) = j (SemidirectProduct.inr b) := DFunLike.congr_fun hc b
  have hcompat (b : Multiplicative (ZMod 2)) :
      s.comp (φ b).toMonoidHom = (MulAut.conj (c b)).toMonoidHom.comp s := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq f hk
    ext x
    change f (s (φ b x)) = f (c b * s x * (c b)⁻¹)
    rw [map_mul, map_mul, map_inv, hs',
      hs', hc']
    rw [← map_inv, ← map_mul, ← map_mul, SemidirectProduct.inl_aut, map_inv]
  refine ⟨SemidirectProduct.lift s c hcompat, ?_⟩
  apply SemidirectProduct.hom_ext
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inl] using hs
  · simpa only [MonoidHom.comp_assoc, SemidirectProduct.lift_comp_inr] using hc

/-- Lifts of direct-product factors commute when the first factor is perfect. -/
theorem exists_product_lift_of_factor_lifts
    {L M E G : Type*} [Group L] [Group.IsPerfect L] [Group M] [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ center E) (j : L × M →* G)
    (s : L →* E) (t : M →* E)
    (hs : f.comp s = j.comp (MonoidHom.inl L M))
    (ht : f.comp t = j.comp (MonoidHom.inr L M)) :
    ∃ r : L × M →* E, f.comp r = j := by
  have hs' (x : L) : f (s x) = j (x, 1) := DFunLike.congr_fun hs x
  have ht' (y : M) : f (t y) = j (1, y) := DFunLike.congr_fun ht y
  have hc (x : L) (y : M) : Commute (s x) (t y) := by
    have he : (MulAut.conj (t y)).toMonoidHom.comp s = s := by
      apply monoidHom_eq_of_isPerfect_of_comp_eq f hk
      ext z
      change f (t y * s z * (t y)⁻¹) = f (s z)
      rw [map_mul, map_mul, map_inv, hs', ht']
      change j (1, y) * j (z, 1) * (j (1, y))⁻¹ = j (z, 1)
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    have hh := DFunLike.congr_fun he x
    change t y * s x * (t y)⁻¹ = s x at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  refine ⟨s.noncommCoprod t hc, ?_⟩
  ext z
  change f (s z.1 * t z.2) = j z
  rw [map_mul, hs', ht']
  simpa using (map_mul j (z.1, 1) (1, z.2)).symm

/-- A splitting theorem for a group applies to its literal embedded preimage. -/
theorem exists_lift_of_splits_central_pGroup
    {E : Type u} {L : Type v} {G : Type w}
    [Group E] [Finite E] [Group L] [Group G] {r : ℕ}
    (hsplit : ∀ (D : Type u) [Group D] [Finite D] (q : D →* L),
      Function.Surjective q → q.ker ≤ center D → IsPGroup r q.ker →
      ∃ s : L →* D, q.comp s = MonoidHom.id L)
    (f : E →* G) (hf : Function.Surjective f)
    (hk : f.ker ≤ center E) (hr : IsPGroup r f.ker)
    (j : L →* G) (hj : Function.Injective j) :
    ∃ s : L →* E, f.comp s = j := by
  let H := j.range.comap f
  let e := MonoidHom.ofInjective hj
  let q₀ : H →* j.range := f.subgroupComap j.range
  let q : H →* L := e.symm.toMonoidHom.comp q₀
  have hq (x : H) : j (q x) = f x := by
    exact congrArg Subtype.val (e.apply_symm_apply (q₀ x))
  have hqsurj : Function.Surjective q :=
    e.symm.surjective.comp (f.subgroupComap_surjective_of_surjective j.range hf)
  have hqker {x : H} (hx : x ∈ q.ker) : (x : E) ∈ f.ker := by
    change f x = 1
    rw [← hq, MonoidHom.mem_ker.mp hx, map_one]
  have hqcentral : q.ker ≤ center H := by
    intro x hx
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp (hk (hqker hx)) y)
  let k : q.ker →* f.ker :=
    (H.subtype.comp q.ker.subtype).codRestrict f.ker (fun x => hqker x.property)
  have hki : Function.Injective k := by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : f.ker => (z : E)) h))
  obtain ⟨s, hs⟩ := hsplit H q hqsurj hqcentral (hr.of_injective k hki)
  refine ⟨H.subtype.comp s, ?_⟩
  apply MonoidHom.ext
  intro x
  change f (s x) = j x
  rw [← hq]
  exact congrArg j (DFunLike.congr_fun hs x)

end PerfectCentralCovering
