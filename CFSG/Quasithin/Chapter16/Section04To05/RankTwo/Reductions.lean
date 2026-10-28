module

public import CFSG.Quasithin.Chapter16.Section04To05.Terminal
public import Theory.ElementaryAbelian.Basic

/-!
# Normalizer transport and the exceptional cover obstruction

For the long-root argument, the containment C_T(X) ≤ T^g and invariance
of X force invariance of C_T(X), by equality of finite orders.
For the final cover reduction, a faithful embedding of R into the actual
elementary residual centralizer transports along R ≃ T_C. The resulting
exponent-two condition contradicts an order-four lift in a commuting
factorization of an involution.

These are deductions from the displayed source inputs, not proofs of the
root-centralizer descriptions or exceptional-cover lift theorem.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.1201–1202.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.RankTwo
open Subgroup
open scoped IsMulCommutative
variable {G : Type*} [Group G]

/-- The finite containment C_T(X) ≤ T^g becomes equality after conjugation
when g normalizes X. This is the normalizer step on printed p.1201. -/
theorem normalizes_centralizer_intersection [Finite G]
    {T X : Subgroup G} {g : G}
    (hgX : g ∈ normalizer (X : Set G))
    (htransport : T ⊓ centralizer (X : Set G) ≤ T.conjBy g) :
    g ∈ normalizer ((T ⊓ centralizer (X : Set G) : Subgroup G) : Set G) := by
  let V := T ⊓ centralizer (X : Set G)
  let e := MulAut.conj g
  have hle : V ≤ V.conjBy g := by
    intro y hy
    obtain ⟨t, ht, he⟩ := htransport hy
    change e t = y at he
    refine ⟨t, ⟨ht, ?_⟩, he⟩
    change t ∈ centralizer (X : Set G)
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : e x ∈ X := (mem_normalizer_iff.mp hgX x).mp hx
    have hh := mem_centralizer_iff.mp hy.2 (e x) hx'
    rw [← he] at hh
    have hh' := congrArg e.symm hh
    simpa only [map_mul, MulEquiv.symm_apply_apply] using hh'
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (eq_of_le_of_card_ge hle
    (le_of_eq (card_map_of_injective e.injective))).symm

/-- Faithfulness of R on the elementary residual centralizer, together with
R ≃ T_C, makes T_C elementary abelian. The centralizer must be an actual
group and the map must be injective; an order bound alone does not suffice. -/
theorem commutingSylow_elementary_of_embedding
    {R TC : Subgroup G} {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (e : R ≃* TC) (f : R →* E) (hf : Function.Injective f) :
    IsElementaryAbelian 2 TC := by
  let j : TC →* E := f.comp e.symm.toMonoidHom
  have hj : Function.Injective j := hf.comp e.symm.injective
  refine {
    toIsMulCommutative := ⟨⟨fun x y => hj (by simp only [map_mul, mul_comm])⟩⟩
    exponent_dvd_p := (Monoid.exponent_dvd_of_monoidHom j hj).trans
      (IsElementaryAbelian.exponent_dvd_p 2 E) }

/-- The short-root order-four lift rules out the remaining double cover:
a commuting elementary factor cannot turn an order-four element into an
involution. The model-specific lift and residual-centralizer description
are explicit earlier inputs (I.2.2(5b) and 16.1.4). -/
theorem no_order_four_lift_of_elementary_residual
    {L R TC : Subgroup G} {E : Type*} [Group E] [IsElementaryAbelian 2 E]
    (e : R ≃* TC) (f : R →* E) (hf : Function.Injective f)
    (hTC : TC ≤ centralizer (L : Set G))
    {u c v : G} (hu : orderOf u = 2) (hc : c ∈ TC) (hv : v ∈ L)
    (huv : u = c * v) (hv4 : orderOf v = 4) : False := by
  let := commutingSylow_elementary_of_embedding e f hf
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have hcomm : Commute c v := (mem_centralizer_iff.mp (hTC hc) v hv).symm
  have hu2 : u ^ 2 = 1 := (orderOf_eq_prime_iff.mp hu).1
  have hv2 : v ^ 2 = 1 := by
    simpa only [huv, hcomm.mul_pow, hc2, one_mul] using hu2
  have hd := orderOf_dvd_of_pow_eq_one hv2
  rw [hv4] at hd
  omega

end CFSG.Quasithin.Chapter16.Intersections.RankTwo
