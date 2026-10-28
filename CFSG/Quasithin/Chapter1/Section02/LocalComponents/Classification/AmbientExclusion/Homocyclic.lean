module

public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.CenterFrattiniSource.OmegaActions.Nilpotent
public import Theory.GroupTheory.PGroup.Homocyclic

/-!
# The exact extra restriction in the single-prime homocyclic case

Let K be perfect and satisfy the nilpotent alternative of A.3.6. The central
involution in K/F*(K) acts by inversion on Ω₁(Oₚ(K))/Φ(Ω₁(Oₚ(K))). If Oₚ(K)
is abelian, its omega subgroup is elementary abelian, so its Frattini subgroup
is trivial. An element of order p in Z(K) ∩ Oₚ(K) would therefore be both
fixed and inverted, which is impossible for odd p. Hence that intersection
is trivial.

When F*(K) = Oₚ(K) is abelian, Z(K) = 1. Consequently the additional equality
Z(K) = Φ(F*(K)) is equivalent to Oₚ(K) being elementary abelian. If an actual
isomorphism identifies this core with C_(p^a) × C_(p^a), the equality is
therefore equivalent to a = 1. The final theorem applies this equivalence to
the actual image of a C-component under the quotient by the two-core.

This is a reduction, not an ambient exclusion theorem. Neither the exponent
restriction nor the center–Frattini equality is assumed or established for
every QTKE local group. In particular all homocyclic exponents remain allowed
in A36Nilpotent and in these input isomorphisms.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.3.6 and
its proof, pp.43–45; Proposition 1.2.1(4d), p.504.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.RadicalActions
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.Section02.AmbientExclusion
open CenterFrattiniSource
universe u

private theorem central_omega_eq_one
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hn : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pCore p K)]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K))
    (x : omegaCore p K) (hx : (x : K) ∈ center K) : x = 1 := by
  let : IsElementaryAbelian p (omega (pCore p K) (p := p) 1) :=
    IsElementaryAbelian.omega₁_of_isMulCommutative _
  let : IsElementaryAbelian p (omegaCore p K) :=
    IsElementaryAbelian.of_surjective _ (MonoidHom.subgroupMap_surjective _ _)
  let : Fact (IsPGroup p (omegaCore p K)) := ⟨Nilpotent.omega_isPGroup⟩
  have hphi : frattini (omegaCore p K) = ⊥ :=
    frattini_eq_bot_of_isElementaryAbelian (p := p)
  let q := QuotientGroup.mk' (frattini (omegaCore p K))
  have hq : Function.Injective q := (MonoidHom.ker_eq_bot_iff q).mp (by
    rw [QuotientGroup.ker_mk', hphi])
  obtain ⟨e, he⟩ := nilpotent_exists_inverting_quotient hn hp hd
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (generalizedFitting K) (e.symm (-1))
  have hfix : omegaCoreAction p K g x = x := by
    apply Subtype.ext
    rw [omegaCoreAction_apply, mem_center_iff.mp hx g, mul_inv_cancel_right]
  have hinv : (q x)⁻¹ = q x := by
    rw [← he (q x), ← hg, Nilpotent.quotientAction_apply_mk]
    change quotientAut (frattini (omegaCore p K)) (omegaCoreAction p K g) (q x) = q x
    rw [quotientAut_apply_mk, hfix]
  have hxi : x⁻¹ = x := hq (by simpa only [map_inv] using hinv)
  have hx2 : x ^ 2 = 1 := by
    calc x ^ 2 = x * x := pow_two x
         _ = x⁻¹ * x := congrArg (fun y => y * x) hxi.symm
         _ = 1 := inv_mul_cancel x
  have hxp : x ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p (omegaCore p K)) x
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.coprime_two_left.mpr hp) (orderOf_dvd_of_pow_eq_one hx2)
    (orderOf_dvd_of_pow_eq_one hxp))

/-- The center meets an abelian core trivially in the nilpotent A.3.6 branch.
A nontrivial intersection would contain an element of order p. Its omega
image would be both fixed and inverted by the actual quotient action. -/
theorem center_inf_abelian_core_eq_bot
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hn : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pCore p K)]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K)) :
    center K ⊓ pCore p K = ⊥ := by
  by_contra hne
  let D := center K ⊓ pCore p K
  have hD : IsPGroup p D := (pCore_isPGroup (p := p) (G := K)).to_le inf_le_right
  let : Nontrivial D := (nontrivial_iff_ne_bot D).mpr hne
  obtain ⟨n, hn0, hncard⟩ := hD.nontrivial_iff_card.mp inferInstance
  have hpD : p ∣ Nat.card D := by rw [hncard]; exact dvd_pow_self p (by omega)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpD
  let y : pCore p K := ⟨x, x.property.2⟩
  have hy : y ^ p = 1 := by
    apply Subtype.ext
    exact congrArg (fun z : D => (z : K)) (hx ▸ pow_orderOf_eq_one x)
  have hyw : y ∈ omega (pCore p K) (p := p) 1 := subset_closure (by
    change y ^ (p ^ 1) = 1
    simpa only [pow_one] using hy)
  let z : omegaCore p K := ⟨x, mem_map.mpr ⟨y, hyw, rfl⟩⟩
  have hz := central_omega_eq_one hn hp hd z x.property.1
  have hxK : (x : K) = 1 := congrArg (fun a : omegaCore p K => (a : K)) hz
  have hx1 : x = 1 := Subtype.ext hxK
  exact (Fact.out : p.Prime).ne_one (hx.symm.trans (hx1 ▸ orderOf_one))

/-- When the entire Fitting subgroup is this abelian core, the component
has trivial center, even at higher homocyclic exponents. -/
theorem center_eq_bot_of_abelian_fitting_core
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hn : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pCore p K)]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K))
    (hF : generalizedFitting K = pCore p K) : center K = ⊥ := by
  have hz : center K ≤ fittingSubgroup K := le_sSup ⟨inferInstance, inferInstance⟩
  rw [← hn.1, hF] at hz
  rw [← inf_eq_left.mpr hz]
  exact center_inf_abelian_core_eq_bot hn hp hd

/-- For an abelian single-prime Fitting subgroup, the additional printed
equality is exactly the elementary-abelian restriction. -/
theorem centerFrattini_iff_elementary_of_abelian_fitting_core
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hn : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    [IsMulCommutative (pCore p K)]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K))
    (hF : generalizedFitting K = pCore p K) :
    CenterFrattini K ↔ IsElementaryAbelian p (pCore p K) := by
  have hz := center_eq_bot_of_abelian_fitting_core hn hp hd hF
  unfold CenterFrattini
  rw [hz]
  constructor
  · intro heq
    have hphi : frattini (generalizedFitting K) = ⊥ :=
      (map_eq_bot_iff_of_injective _ (generalizedFitting K).subtype_injective).mp heq.symm
    rw [hF] at hphi
    let : Fact (IsPGroup p (pCore p K)) := ⟨pCore_isPGroup⟩
    exact (frattini_eq_bot_iff_isElementaryAbelian (p := p)).mp hphi
  · intro he
    let : IsElementaryAbelian p (generalizedFitting K) := hF.symm ▸ he
    let : Fact (IsPGroup p (generalizedFitting K)) := ⟨hF.symm ▸ pCore_isPGroup⟩
    rw [frattini_eq_bot_of_isElementaryAbelian (p := p), Subgroup.map_bot]

/-- The precise exponent restriction forced by the printed equality in the
single-prime homocyclic case. The input allows every positive exponent. -/
theorem centerFrattini_iff_homocyclic_exponent_one
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (hn : A36Nilpotent K) {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hd : p ∣ Nat.card (fittingSubgroup K))
    (hF : generalizedFitting K = pCore p K)
    {a : ℕ} (ha : 1 ≤ a)
    (e : pCore p K ≃* StandardHomocyclicCover (Fin 2) (p ^ a)) :
    CenterFrattini K ↔ a = 1 := by
  let : IsMulCommutative (pCore p K) := IsMulCommutative.of_comm (fun x y =>
    e.injective (by simp only [map_mul, mul_comm]))
  have hexp : Monoid.exponent (pCore p K) = p ^ a :=
    (Monoid.exponent_eq_of_mulEquiv e).trans (standardHomocyclicCover_exponent _ _)
  rw [centerFrattini_iff_elementary_of_abelian_fitting_core hn hp hd hF]
  constructor
  · intro he
    let := he
    have hdvd := IsElementaryAbelian.exponent_dvd_p p (pCore p K)
    rw [hexp] at hdvd
    have hle : p ^ a ≤ p ^ 1 := by
      simpa only [pow_one] using Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd
    exact le_antisymm ((Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hle) ha
  · intro ha1
    exact { toIsMulCommutative := inferInstance
            exponent_dvd_p := by rw [hexp, ha1, pow_one] }

/-- The same equivalence for the actual image of the specified C-component
in H/O₂(H). The single-prime hypothesis is an explicit subcase restriction;
it is not asserted for every nilpotent branch. In a QTKE ambient application,
an additional ambient argument must still establish a = 1. -/
theorem quotient_centerFrattini_iff_homocyclic_exponent_one
    {H : Type u} [Group H] [Finite H] {L : Subgroup H} (hL : L.IsCComponent)
    (hn : A36Nilpotent (L.map (QuotientGroup.mk' (pCore 2 H))))
    (hc : A36Common (L.map (QuotientGroup.mk' (pCore 2 H))))
    {p : ℕ} [Fact p.Prime]
    (hd : p ∣ Nat.card (fittingSubgroup (L.map (QuotientGroup.mk' (pCore 2 H)))))
    (hs : ∀ q : ℕ, q.Prime → Odd q →
      q ∣ Nat.card (fittingSubgroup (L.map (QuotientGroup.mk' (pCore 2 H)))) → q = p)
    {a : ℕ} (ha : 1 ≤ a)
    (e : pCore p (L.map (QuotientGroup.mk' (pCore 2 H))) ≃*
      StandardHomocyclicCover (Fin 2) (p ^ a)) :
    CenterFrattini (L.map (QuotientGroup.mk' (pCore 2 H))) ↔ a = 1 := by
  let := pCore_isNilpotent (p := 2) (G := H)
  let : Group.IsPerfect (L.map (QuotientGroup.mk' (pCore 2 H))) :=
    (hL.map_quotient _).perfect
  have hp3 := (RadicalStructure.radical_core (Or.inr hn) hd).2.1
  have hp : Odd p := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left (by omega)
  exact centerFrattini_iff_homocyclic_exponent_one hn hp hd
    (RadicalStructure.core_eq_generalizedFitting (Or.inr hn) hc hs).symm ha e


end CFSG.Quasithin.Chapter1.Section02.AmbientExclusion
