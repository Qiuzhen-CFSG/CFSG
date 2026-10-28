module

public import Theory.SpecificGroups.HeisenbergPrime.ElementaryPlane
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.ElementaryAbelian.ExtraspecialEquiv
import Mathlib.Tactic.Group

/-!
# Outer cubic actions on rank-two ternary groups

An outside element of order three cannot act by an inner automorphism on
an embedded elementary group of order nine or the exponent-three Heisenberg
group in an ambient group of three-rank at most two. If conjugation by d
agrees with conjugation by x, then d*x⁻¹ still has order three, lies outside
the embedded group, and centralizes it. Its join with an actual elementary
plane has order 27, contradicting the rank bound.

The model equivalences transport both the exponent and the elementary plane.
Trivial action on the Frattini quotient is trivial in the elementary case
and inner in the extraspecial case, so it is excluded as well. The embedding
formulation preserves nested subgroup maps in the application.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup
namespace RankTwoInnerCubicAction
variable {G P : Type*} [Group G] [Group P]

/-- Correcting an inner cubic actor gives an outside centralizing cubic element. -/
theorem centralizing_correction (ι : P →* G) (d : G) (x : P)
    (hd : orderOf d = 3) (hout : d ∉ ι.range) (hx : x ^ 3 = 1)
    (hinner : ∀ y : P, d * ι y * d⁻¹ = ι (x * y * x⁻¹)) :
    orderOf (d * (ι x)⁻¹) = 3 ∧ d * (ι x)⁻¹ ∉ ι.range ∧
      d * (ι x)⁻¹ ∈ centralizer (ι.range : Set G) := by
  have hcomm : Commute d (ι x) := by
    have he := hinner x
    simp only [mul_inv_cancel_right] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hnot : d * (ι x)⁻¹ ∉ ι.range := by
    intro hm
    apply hout
    simpa using ι.range.mul_mem hm (show ι x ∈ ι.range from ⟨x, rfl⟩)
  refine ⟨orderOf_eq_prime ?_ (fun he => hnot (he ▸ ι.range.one_mem)), hnot, ?_⟩
  · rw [hcomm.inv_right.mul_pow, ← hd, pow_orderOf_eq_one, hd, inv_pow,
      ← map_pow, hx, map_one, inv_one, mul_one]
  · rintro _ ⟨y, rfl⟩
    have he := hinner (x⁻¹ * y * x)
    simp only [map_mul, map_inv] at he
    have he' : d * ((ι x)⁻¹ * ι y * ι x) * d⁻¹ = ι y := by
      calc
        _ = ι x * ((ι x)⁻¹ * ι y * ι x) * (ι x)⁻¹ := he
        _ = ι y := by group
    calc
      ι y * (d * (ι x)⁻¹) =
          (d * ((ι x)⁻¹ * ι y * ι x) * d⁻¹) * (d * (ι x)⁻¹) := by rw [he']
      _ = (d * (ι x)⁻¹) * ι y := by group

/-- An exponent-three group with an elementary plane admits no outside inner
cubic actor in an ambient group of three-rank at most two. -/
theorem not_inner_of_plane [Finite G]
    (ι : P →* G) (hi : Function.Injective ι) (hr : primeRank 3 G ≤ 2)
    (hp : ∀ x : P, x ^ 3 = 1)
    (hplane : ∃ E : Subgroup P, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2)
    (d : G) (hd : orderOf d = 3) (hout : d ∉ ι.range) :
    ¬ ∃ x : P, ∀ y : P, d * ι y * d⁻¹ = ι (x * y * x⁻¹) := by
  rintro ⟨x, hx⟩
  obtain ⟨hc, houtc, hcent⟩ := centralizing_correction ι d x hd hout (hp x) hx
  obtain ⟨E, hE, hcard⟩ := hplane
  let : IsElementaryAbelian 3 E := hE
  let : IsElementaryAbelian 3 (E.map ι) := IsElementaryAbelian.map ι
  have hfix : E.map ι ≤ centralizer ({d * (ι x)⁻¹} : Set G) := by
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (hcent y (map_le_range ι E hy))
  have hlow := IsElementaryAbelian.primeRank_ge_of_fixed_join (E.map ι)
    (d * (ι x)⁻¹) hc (fun hm => houtc (map_le_range ι E hm)) hfix
    ((Subgroup.card_map_of_injective hi).trans hcard)
  omega

private theorem elementary_of_model
    (e : P ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) :
    IsElementaryAbelian 3 P := by
  refine { toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp [mul_comm])⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  apply e.injective
  rw [map_pow, map_one]
  have hz (z : ZMod 3) : (3 : ℕ) • z = 0 := by
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  exact Prod.ext (hz (e x).1.toAdd) (hz (e x).2.toAdd)

/-- The actual elementary-nine and Heisenberg models supply exponent three
and an elementary subgroup of order nine. -/
theorem model_exponent_and_plane
    (hm : Nonempty (P ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (P ≃* HeisenbergPrime 3)) :
    (∀ x : P, x ^ 3 = 1) ∧
      ∃ E : Subgroup P, IsElementaryAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  rcases hm with hm | hm
  · obtain ⟨e⟩ := hm
    let : IsElementaryAbelian 3 P := elementary_of_model e
    have hp := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 3 P)
    refine ⟨hp, ⊤, ?_, ?_⟩
    · exact { toIsMulCommutative := inferInstance
              exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
                (fun x => Subtype.ext (hp x)) }
    · rw [Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_congr e.toEquiv,
        Nat.card_prod]
      change Nat.card (ZMod 3) * Nat.card (ZMod 3) = 3 ^ 2
      rw [Nat.card_zmod]
      rfl
  · obtain ⟨e⟩ := hm
    have hp (x : P) : x ^ 3 = 1 := e.injective (by
      rw [map_pow, HeisenbergPrime.pow_prime (by decide), map_one])
    obtain ⟨E, hE, hc⟩ := HeisenbergPrime.exists_elementary_plane (p := 3) (by decide)
    let : IsElementaryAbelian 3 E := hE
    exact ⟨hp, E.map e.symm.toMonoidHom, IsElementaryAbelian.map _,
      (Subgroup.card_map_of_injective e.symm.injective).trans hc⟩

/-- The concrete model obstruction, retaining an arbitrary injective embedding. -/
theorem not_inner_of_models [Finite G]
    (ι : P →* G) (hi : Function.Injective ι) (hr : primeRank 3 G ≤ 2)
    (hm : Nonempty (P ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (P ≃* HeisenbergPrime 3))
    (d : G) (hd : orderOf d = 3) (hout : d ∉ ι.range) :
    ¬ ∃ x : P, ∀ y : P, d * ι y * d⁻¹ = ι (x * y * x⁻¹) := by
  obtain ⟨hp, hE⟩ := model_exponent_and_plane hm
  exact not_inner_of_plane ι hi hr hp hE d hd hout

/-- An outside cubic actor has nontrivial action on the literal Frattini quotient. -/
theorem frattini_action_ne_one [Finite G] [Finite P]
    (ι : P →* G) (hi : Function.Injective ι) (hr : primeRank 3 G ≤ 2)
    (hm : Nonempty (P ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (P ≃* HeisenbergPrime 3))
    (d : G) (hd : orderOf d = 3) (hout : d ∉ ι.range)
    (α : MulAut P) (hα : ∀ y : P, ι (α y) = d * ι y * d⁻¹) :
    quotientAut (frattini P) α ≠ 1 := by
  intro hq
  apply not_inner_of_models ι hi hr hm d hd hout
  have hin : ∃ x : P, MulAut.conj x = α := by
    rcases hm with hm | hm
    · obtain ⟨e⟩ := hm
      let : IsElementaryAbelian 3 P := elementary_of_model e
      let : Fact (IsPGroup 3 P) := ⟨IsElementaryAbelian.isPGroup 3 P⟩
      have hf : frattini P = ⊥ := frattini_eq_bot_of_isElementaryAbelian (p := 3)
      have hid : α = 1 := by
        ext y
        have he := DFunLike.congr_fun hq (QuotientGroup.mk' (frattini P) y)
        rw [quotientAut_apply_mk] at he
        have hm : α y / y ∈ frattini P := QuotientGroup.eq_iff_div_mem.mp he
        rw [hf, mem_bot, div_eq_one] at hm
        exact hm
      exact ⟨1, by simpa using hid.symm⟩
    · obtain ⟨e⟩ := hm
      let : IsExtraspecial 3 P := (HeisenbergPrime.isExtraspecial (p := 3)
        (by decide)).of_mulEquiv e.symm
      have hmem : α ∈ (quotientAut (frattini P)).ker := hq
      rw [IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p := 3)] at hmem
      exact hmem
  obtain ⟨x, hx⟩ := hin
  refine ⟨x, fun y => ?_⟩
  rw [← hα, ← hx]
  rfl

/-- For a normal subgroup with either model, ambient cubic conjugation
from outside the subgroup is an outer automorphism. -/
theorem conjNormal_not_inner [Finite G]
    (X : Subgroup G) [X.Normal] (hr : primeRank 3 G ≤ 2)
    (hm : Nonempty (X ≃* (Multiplicative (ZMod 3) × Multiplicative (ZMod 3))) ∨
      Nonempty (X ≃* HeisenbergPrime 3))
    (d : G) (hd : orderOf d = 3) (hout : d ∉ X) :
    MulAut.conjNormal d ∉ (MulAut.conj : X →* MulAut X).range := by
  rintro ⟨x, hx⟩
  apply not_inner_of_models X.subtype X.subtype_injective hr hm d hd
    (by simpa only [range_subtype] using hout)
  refine ⟨x, fun y => ?_⟩
  exact (MulAut.conjNormal_apply d y).symm.trans
    (congrArg (fun f : MulAut X => (f y : G)) hx.symm)

end RankTwoInnerCubicAction
