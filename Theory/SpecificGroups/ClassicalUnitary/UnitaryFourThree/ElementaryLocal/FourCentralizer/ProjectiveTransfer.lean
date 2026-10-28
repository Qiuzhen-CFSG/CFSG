module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

/-!
# Centralizers of pairs through a central quotient

For a surjection f with central kernel Z, take the inverse image K of the
centralizer of {f(a), f(b)}. The commutators with a and b define a homomorphism
K → Z × Z whose kernel is the ordinary centralizer of {a,b}. Counting its
image gives |C({f(a),f(b)})| dividing |Z|² |C({a,b})|. This retains every
projectively centralizing element, including those with nontrivial scalar
commutators. If f(a) has square one, the commutator of a with a projectively
commuting element has square one as well.

These elementary central-extension facts support the PSU₄(3) local calculation
for Aschbacher–Smith, Theorem 0.1.2(4), printed p.4 of `refs/quasithin.pdf`.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- A central commutator with an element whose image is an involution has square one. -/
theorem commutator_square_eq_one_of_central_kernel (f : G →* H)
    (hc : f.ker ≤ center G) (a b : G)
    (ha : (f a) ^ 2 = 1) (hab : Commute (f a) (f b)) : ⁅a, b⁆ ^ 2 = 1 := by
  have hz : ⁅a, b⁆ ∈ f.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hab.eq
  have ha2 : a ^ 2 ∈ f.ker := by
    simpa only [MonoidHom.mem_ker, map_pow] using ha
  have hzero : ⁅a ^ 2, b⁆ = 1 :=
    commutatorElement_eq_one_iff_mul_comm.mpr (mem_center_iff.mp (hc ha2) b).symm
  rw [pow_two, commutatorElement_mul_left_eq_conj_mul,
    mem_center_iff.mp (hc hz) a, mul_inv_cancel_right] at hzero
  simpa only [pow_two] using hzero

private def commutatorRow (f : G →* H) (hc : f.ker ≤ center G)
    (a b t : G) (ht : t = a ∨ t = b) :
    (centralizer ({f a, f b} : Set H)).comap f →* f.ker where
  toFun x := ⟨⁅t, (x : G)⁆, by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact x.property (f t) (by rcases ht with rfl | rfl <;> simp)⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' x y := by
    apply Subtype.ext
    change ⁅t, (x : G) * (y : G)⁆ = ⁅t, (x : G)⁆ * ⁅t, (y : G)⁆
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hz : ⁅t, (y : G)⁆ ∈ f.ker := by
      apply MonoidHom.mem_ker.mpr
      rw [map_commutatorElement]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact y.property (f t) (by rcases ht with rfl | rfl <;> simp)
    calc
      _ = ⁅t, (x : G)⁆ * ((x : G) * ⁅t, (y : G)⁆) * (x : G)⁻¹ := by group
      _ = ⁅t, (x : G)⁆ * ⁅t, (y : G)⁆ := by
        rw [mem_center_iff.mp (hc hz) x]
        group

/-- The two scalar-commutator rows bound the full centralizer in the quotient. -/
theorem centralizer_pair_card_dvd_of_central_kernel [Finite G] (f : G →* H)
    (hf : Function.Surjective f) (hc : f.ker ≤ center G) (a b : G) :
    Nat.card (centralizer ({f a, f b} : Set H)) ∣
      Nat.card f.ker ^ 2 * Nat.card (centralizer ({a, b} : Set G)) := by
  let C := centralizer ({f a, f b} : Set H)
  let K := C.comap f
  let D := centralizer ({a, b} : Set G)
  let c := (commutatorRow f hc a b a (Or.inl rfl)).prod
    (commutatorRow f hc a b b (Or.inr rfl))
  have hDK : D ≤ K := by
    intro x hx y hy
    rcases hy with rfl | hy
    · simpa only [map_mul] using congrArg f (hx a (by simp))
    · obtain rfl := Set.mem_singleton_iff.mp hy
      simpa only [map_mul] using congrArg f (hx b (by simp))
  have hker : c.ker.map K.subtype = D := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : c y = 1 := hy
      have ha : ⁅a, (y : G)⁆ = 1 := congrArg (fun p : f.ker × f.ker => (p.1 : G)) hy'
      have hb : ⁅b, (y : G)⁆ = 1 := congrArg (fun p : f.ker × f.ker => (p.2 : G)) hy'
      intro z hz
      rcases hz with rfl | hz
      · exact commutatorElement_eq_one_iff_mul_comm.mp ha
      · obtain rfl := Set.mem_singleton_iff.mp hz
        exact commutatorElement_eq_one_iff_mul_comm.mp hb
    · intro hx
      refine ⟨⟨x, hDK hx⟩, ?_, rfl⟩
      apply MonoidHom.mem_ker.mpr
      apply Prod.ext <;> apply Subtype.ext
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (hx a (by simp))
      · exact commutatorElement_eq_one_iff_mul_comm.mpr (hx b (by simp))
  have hcard : Nat.card K = Nat.card c.range * Nat.card D := by
    rw [← hker, card_map_of_injective K.subtype_injective,
      ← c.ker.index_mul_card, index_ker]
  have hdiv : Nat.card c.range ∣ Nat.card f.ker ^ 2 := by
    simpa only [Nat.card_prod, pow_two] using c.range.card_subgroup_dvd_card
  have hCK : Nat.card C ∣ Nat.card K :=
    card_dvd_of_surjective (f.subgroupComap C)
      (f.subgroupComap_surjective_of_surjective C hf)
  rw [hcard] at hCK
  exact hCK.trans (Nat.mul_dvd_mul hdiv (dvd_refl _))
end Subgroup
