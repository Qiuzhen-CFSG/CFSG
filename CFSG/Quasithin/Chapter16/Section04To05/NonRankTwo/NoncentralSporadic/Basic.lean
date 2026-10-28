module

public import CFSG.Quasithin.Chapter16.Section04To05.NonRankTwo.Products
public import Theory.Frattini.PGroup
public import Theory.GroupTheory.PResidual.Defs

/-!
# Elementary deductions in the noncentral sporadic branch

Two-centrality is expressed on an actual group and transported through actual
isomorphisms. The common residual is O²(C_L(u)), using the relative centralizer
inside L and mapping its two-residual back into the ambient group.

The small-centralizer deduction proves the elementary, order, Frattini and omega
conclusions for R and T_C once the model supplies a faithful small elementary
centralizer. The identification R ≃ T_C comes from genuine earlier Sylow and
conjugation inputs. The covering deduction rules out order-four projections.
Neither deduction asserts the still missing model-specific premises.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.4.11(3),
16.5.5–6 and the noncentral branch of 16.5.11, printed pp.1193–1200.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic

open Subgroup
open scoped IsMulCommutative

/-- An involution central in a Sylow two-subgroup of its actual group. -/
def TwoCentral {H : Type*} [Group H] (v : H) : Prop :=
  orderOf v = 2 ∧ ∃ S : Sylow 2 H, v ∈ S ∧
    (S : Subgroup H) ≤ centralizer ({v} : Set H)

/-- Two-centrality is preserved by genuine multiplicative equivalences. -/
theorem TwoCentral.map {H J : Type*} [Group H] [Group J] [Finite H]
    {v : H} (hv : TwoCentral v) (e : H ≃* J) : TwoCentral (e v) := by
  obtain ⟨ho, S, hvS, hc⟩ := hv
  refine ⟨(e.orderOf_eq v).trans ho, S.mapSurjective (f := e.toMonoidHom) e.surjective,
    ⟨v, hvS, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  simpa using congrArg e (mem_centralizer_singleton_iff.mp (hc hs))

/-- Two-centrality is invariant under conjugation. -/
theorem TwoCentral.of_isConj {H : Type*} [Group H] [Finite H] {v w : H}
    (hv : TwoCentral v) (h : IsConj v w) : TwoCentral w := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp h
  exact hv.map (MulAut.conj g)

/-- A finite group with one involution class has only two-central involutions.
A nontrivial Sylow center supplies the representative. -/
theorem twoCentral_of_single_involution_class {H : Type*} [Group H] [Finite H]
    (hfuse : ∀ v w : H, orderOf v = 2 → orderOf w = 2 → IsConj v w)
    {v : H} (hv : orderOf v = 2) : TwoCentral v := by
  have hp : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv, pow_one])
  obtain ⟨S, hS⟩ := hp.exists_le_sylow
  have hvS : v ∈ S := hS (mem_zpowers v)
  have hvne : (⟨v, hvS⟩ : S) ≠ 1 := by
    intro he
    have he' : v = 1 := congrArg Subtype.val he
    simp [he'] at hv
  let : Nontrivial S := ⟨⟨_, _, hvne⟩⟩
  let : Nontrivial (center S) := S.isPGroup'.center_nontrivial
  have hdvd : 2 ∣ Nat.card (center S) := by
    rcases (S.isPGroup'.to_subgroup (center S)).card_eq_or_dvd with h | h
    · exact False.elim (by have := Finite.one_lt_card (α := center S); omega)
    · exact h
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := center S) 2 hdvd
  have hw2 : orderOf ((w : S) : H) = 2 := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hw]
  apply TwoCentral.of_isConj (v := ((w : S) : H)) _ (hfuse _ v hw2 hv)
  refine ⟨hw2, S, (w : S).property, ?_⟩
  intro s hs
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val ((mem_center_iff.mp w.property) ⟨s, hs⟩)

/-- Convert intrinsic two-centrality to the existing ambient-subgroup convention. -/
theorem TwoCentral.ambient {G : Type*} [Group G] {L : Subgroup G}
    {v : L} (hv : TwoCentral v) : IsTwoCentralIn L (v : G) := by
  obtain ⟨ho, S, hvS, hc⟩ := hv
  refine ⟨(Subgroup.orderOf_coe v).trans ho, (S : Subgroup L).map L.subtype,
    ⟨S, rfl⟩, ⟨v, hvS, rfl⟩, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hc hs)))

/-- The actual subgroup X = O²(C_L(u)) in the sporadic cases of 16.5.5. -/
def commonResidual {G : Type*} [Group G] (L : Subgroup G) (u : G) : Subgroup G :=
  (pResidual 2 ↥(L ⊓ centralizer ({u} : Set G))).map
    (L ⊓ centralizer ({u} : Set G)).subtype

/-- The common residual lies in the relative centralizer used to define it. -/
theorem commonResidual_le {G : Type*} [Group G] (L : Subgroup G) (u : G) :
    commonResidual L u ≤ L ⊓ centralizer ({u} : Set G) := map_subtype_le _

private theorem elementary_of_injective {A B : Type*} [Group A] [Group B]
    [IsElementaryAbelian 2 B] (f : A →* B) (hf : Function.Injective f) :
    IsElementaryAbelian 2 A := by
  refine {
    toIsMulCommutative := ⟨⟨?_⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro a b
    apply hf
    simp only [map_mul, mul_comm]
  · intro a
    apply hf
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 B) _

/-- An injective action into a small elementary centralizer gives the order
and Frattini assertions for both isomorphic two-subgroups. The model
calculation must supply the faithful map and the centralizer bound. -/
theorem small_of_faithful_elementary_centralizer
    {A B C : Type*} [Group A] [Group B] [Group C]
    [Finite A] [Finite B] [Finite C] [Nontrivial A]
    [IsElementaryAbelian 2 C]
    (f : A →* C) (hf : Function.Injective f) (hC : Nat.card C ≤ 4)
    (e : A ≃* B) :
    IsElementaryAbelian 2 A ∧ IsElementaryAbelian 2 B ∧
    (Nat.card A = 2 ∨ Nat.card A = 4) ∧ Nat.card B = Nat.card A ∧
    frattini A = ⊥ ∧ frattini B = ⊥ := by
  let : IsElementaryAbelian 2 A := elementary_of_injective f hf
  let : IsElementaryAbelian 2 B := elementary_of_injective e.symm.toMonoidHom e.symm.injective
  let : Fact (IsPGroup 2 A) := ⟨IsElementaryAbelian.isPGroup 2 A⟩
  let : Fact (IsPGroup 2 B) := ⟨IsElementaryAbelian.isPGroup 2 B⟩
  have hbound : Nat.card A ≤ 4 := (Nat.card_le_card_of_injective f hf).trans hC
  have hdiv : 2 ∣ Nat.card A := by
    rcases (IsElementaryAbelian.isPGroup 2 A).card_eq_or_dvd with h | h
    · exact False.elim (by have := Finite.one_lt_card (α := A); omega)
    · exact h
  refine ⟨inferInstance, inferInstance, ?_, Nat.card_congr e.symm.toEquiv,
    frattini_eq_bot_of_isElementaryAbelian (p := 2),
    frattini_eq_bot_of_isElementaryAbelian (p := 2)⟩
  have := Finite.card_pos (α := A)
  omega

/-- Output of the noncentral centralizer calculation on printed p.1199.
This is a conclusion to establish, not part of the earlier source setup. -/
def SmallIntersections {G : Type*} [Group G] (T : Sylow 2 G) (L R : Subgroup G) : Prop :=
  IsElementaryAbelian 2 R ∧ IsElementaryAbelian 2 (commutingSylow T L) ∧
    (Nat.card R = 2 ∨ Nat.card R = 4) ∧ Nat.card (commutingSylow T L) = Nat.card R ∧
    frattini R = ⊥ ∧ frattini (commutingSylow T L) = ⊥ ∧ omegaOneAmbient R = R

/-- Apply the faithful-centralizer calculation to the actual R and T_C.
Their isomorphism is constructed from 16.4.10 and the transport in 16.4.2(4),
using the proved conjugation identity. -/
theorem small_intersections_of_faithful_centralizer
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {z g u : G}
    {L R : Subgroup G} (h : IntersectionSetup T z L g R)
    (hfull : SylowIn R ((centralizer (L : Set G)).conjBy g))
    (htransport : (T : Subgroup G) ⊓
        normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g)
    (huR : u ∈ R) (hu2 : orderOf u = 2)
    {C : Type*} [Group C] [Finite C] [IsElementaryAbelian 2 C]
    (f : R →* C) (hf : Function.Injective f) (hC : Nat.card C ≤ 4) :
    SmallIntersections T L R := by
  have hu1 : (⟨u, huR⟩ : R) ≠ 1 := by
    intro he
    have he' : u = 1 := congrArg Subtype.val he
    simp [he'] at hu2
  let : Nontrivial R := ⟨⟨_, _, hu1⟩⟩
  have heq := h.eq_conjugate_commutingSylow hfull htransport
  let e : R ≃* commutingSylow T L := (MulEquiv.subgroupCongr heq).trans
    ((commutingSylow T L).equivMapOfInjective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm
  obtain ⟨hR, hTC, hcard, hecard, hphiR, hphiTC⟩ :=
    small_of_faithful_elementary_centralizer f hf hC e
  let : IsElementaryAbelian 2 R := hR
  exact ⟨hR, hTC, hcard, hecard, hphiR, hphiTC, omegaOneAmbient_eq_self R⟩

/-- An involution factoring over an elementary commuting subgroup has
a component projection of square one. -/
theorem projection_square_eq_one {G : Type*} [Group G]
    {L C : Subgroup G} [IsElementaryAbelian 2 C]
    (hC : C ≤ centralizer (L : Set G)) {u c v : G}
    (hc : c ∈ C) (hv : v ∈ L) (hu : u ^ 2 = 1) (he : u = c * v) : v ^ 2 = 1 := by
  have hc2 : c ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian c hc
  have hcv : Commute c v := (mem_centralizer_iff.mp (hC hc) v hv).symm
  rw [he, hcv.mul_pow, hc2, one_mul] at hu
  exact hu

/-- The order-four lifts in I.2.2 cannot occur over an elementary T_C.
The covering theorem must supply the order-four assertion. -/
theorem no_order_four_projection {G : Type*} [Group G]
    {L C : Subgroup G} [IsElementaryAbelian 2 C]
    (hC : C ≤ centralizer (L : Set G)) {u c v : G}
    (hc : c ∈ C) (hv : v ∈ L) (hu : orderOf u = 2) (he : u = c * v)
    (hv4 : orderOf v = 4) : False := by
  have hd := orderOf_dvd_of_pow_eq_one
    (projection_square_eq_one hC hc hv (by rw [← hu, pow_orderOf_eq_one]) he)
  rw [hv4] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter16.Intersections.NonRankTwo.NoncentralSporadic
