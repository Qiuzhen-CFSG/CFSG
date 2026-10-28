module
public import Theory.GroupTheory.OddPrimeSectionCentralizers
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupAction.KleinFourAbelianCardinality
public import Theory.ElementaryAbelian.Injective

/-!
# Fixed cubic lines in a rank-two-covered three-core

A four-group acting on an elementary group of order27 has three fixed
subgroups of order3 when each is cyclic: the abelian Klein-four cardinality
formula and the exponent bound force equality. If one actor commutes with
the full ambient action modulo the abelian three-core, its fixed line maps
to a proper nonzero normal subgroup of the original group. The cyclicity
input is discharged by the actual covering map and A.1.31(1).

Source: Aschbacher--Smith, A.1.31(3), printed pp.27--28. The original
covering-group prime rank and the literal target three-core are preserved.
-/

public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Theory.GroupTheory.ThreeSection

variable {T V : Type*} [Group T] [Finite T] [IsElementaryAbelian 2 T]
  [Group V] [Finite V] [IsElementaryAbelian 3 V]

/-- Every involution fixes a cubic line in an elementary group of order27
when all three involution fixed subgroups are cyclic. -/
theorem fixed_card_three (α : T →* MulAut V) (hT : Nat.card T = 4)
    (hV : Nat.card V = 27)
    (hc : ∀ t : T, t ≠ 1 → IsCyclic (α t).fixedSubgroup)
    (t : T) (ht : t ≠ 1) : Nat.card (α t).fixedSubgroup = 3 := by
  classical
  have hi (a : T) : Function.Involutive (α a) := by
    have hp : a ^ 2 = 1 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 T) a
    have he : α a ^ 2 = 1 := by rw [← map_pow, hp, map_one]
    exact fun x => DFunLike.congr_fun he x
  have hbound (a : T) (ha : a ≠ 1) : Nat.card (α a).fixedSubgroup ≤ 3 := by
    let : IsCyclic (α a).fixedSubgroup := hc a ha
    apply Nat.le_of_dvd (by decide : 0 < 3)
    rw [← IsCyclic.exponent_eq_card]
    let : IsElementaryAbelian 3 (α a).fixedSubgroup :=
      IsElementaryAbelian.of_injective (α a).fixedSubgroup.subtype
        (α a).fixedSubgroup.subtype_injective
    exact IsElementaryAbelian.exponent_dvd_p 3 (α a).fixedSubgroup
  have hthree : 3 ≤ ENat.card T := by
    let : Fintype T := Fintype.ofFinite T
    rw [ENat.card_eq_coe_fintype_card, ← Nat.card_eq_fintype_card, hT]
    decide
  obtain ⟨s, hs, hst⟩ := ENat.exists_ne_ne_of_three_le hthree 1 t
  have hts : t * s ≠ 1 := by
    intro he
    have ht2 : t * t = 1 := by
      simpa only [pow_two] using Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 T) t
    exact hst (mul_left_cancel (he.trans ht2.symm))
  have hab : Commute (α t) (α s) := by
    change α t * α s = α s * α t
    rw [← map_mul, ← map_mul, mul_comm]
  have hformula := Theory.GroupAction.brauerWielandt_fixedSubgroup_card_of_isMulCommutative
    (by rw [hV]; decide) (α t) (α s) (hi t) (hi s) hab
  rw [hV, ← map_mul] at hformula
  have hp := Nat.card_pos (α := ((α t).fixedSubgroup ⊓ (α s).fixedSubgroup : Subgroup V))
  have h1 := hbound t ht
  have h2 := hbound s hs
  have h3 := hbound (t * s) hts
  have h23 : Nat.card (α s).fixedSubgroup * Nat.card (α (t * s)).fixedSubgroup ≤ 9 :=
    Nat.mul_le_mul h2 h3
  have hmul := Nat.mul_le_mul_left (Nat.card (α t).fixedSubgroup) h23
  rw [← Nat.mul_assoc] at hmul
  nlinarith


/-- A fixed line of a conjugation operator commuting with the whole ambient
action is a normal subgroup of the original ambient group. -/
theorem normal_fixed_image {E : Type*} [Group E]
    (V : Subgroup E) [V.Normal] (a : MulAut V)
    (ha : ∀ g : E, Commute a (MulAut.conjNormal g : MulAut V)) :
    (a.fixedSubgroup.map V.subtype).Normal := by
  constructor
  rintro x ⟨v, hv, rfl⟩ g
  refine ⟨(MulAut.conjNormal g : MulAut V) v, ?_, rfl⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  have he := DFunLike.congr_fun (ha g).eq v
  change a ((MulAut.conjNormal g : MulAut V) v) =
    (MulAut.conjNormal g : MulAut V) (a v) at he
  rw [(MulAut.mem_fixedSubgroup _ _).mp hv] at he
  exact he

/-- Rank greater than one supplies a literal elementary four-subgroup. -/
theorem exists_elementary_four {E : Type*} [Group E] [Finite E]
    (hr : 1 < primeRank 2 E) :
    ∃ T : Subgroup E, IsElementaryAbelian 2 T ∧ Nat.card T = 4 := by
  obtain ⟨A, hA, hc⟩ := exists_elementaryAbelian_card_primeRank (G := E) (p := 2)
  let : IsElementaryAbelian 2 A := hA
  have hd : 2 ^ 2 ∣ Nat.card A := by
    rw [hc]
    exact pow_dvd_pow 2 (by omega)
  obtain ⟨B, hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := A) 2 hd
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  refine ⟨B.map A.subtype, IsElementaryAbelian.map A.subtype, ?_⟩
  rw [card_map_of_injective A.subtype_injective, hB]
  norm_num


private theorem fixed_conjNormal {E : Type*} [Group E] (Q : Subgroup E) [Q.Normal] (z : E) :
    (MulAut.conjNormal z : MulAut Q).fixedSubgroup =
      (centralizer ({z} : Set E)).subgroupOf Q := by
  ext q
  rw [MulAut.mem_fixedSubgroup, mem_subgroupOf]
  change (MulAut.conjNormal z : MulAut Q) q = q ↔
    (q : E) ∈ centralizer ({z} : Set E)
  rw [Subtype.ext_iff, MulAut.conjNormal_apply,
    mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul, eq_comm]

variable {D E : Type*} [Group D] [Finite D] [Group E] [Finite E]

/-- A nonidentity element of the specified four-group central modulo the
three-core supplies the desired proper normal cubic subgroup. -/
theorem reducible_of_four_central_mod_core
    (f : D →* E) (hf : Function.Surjective f) (hrank : primeRank 3 D ≤ 2)
    (hF : generalizedFitting E = pCore 3 E)
    [IsElementaryAbelian 3 (pCore 3 E)] (hV : Nat.card (pCore 3 E) = 27)
    (T : Subgroup E) [IsElementaryAbelian 2 T] (hT : Nat.card T = 4)
    (t : T) (ht : t ≠ 1)
    (hcentral : ∀ g : E, g * (t : E) * g⁻¹ * (t : E)⁻¹ ∈ pCore 3 E) :
    ∃ R : Subgroup E, R.Normal ∧ R ≠ ⊥ ∧ R < pCore 3 E := by
  let ρ : E →* MulAut (pCore 3 E) := MulAut.conjNormal
  let α : T →* MulAut (pCore 3 E) := ρ.comp T.subtype
  have hpow (a : T) : (a : E) ^ 2 = 1 := congrArg Subtype.val
    (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 T) a)
  have hcyc (a : T) (ha : a ≠ 1) : IsCyclic (α a).fixedSubgroup := by
    have hao : orderOf (a : E) = 2 := orderOf_eq_prime (hpow a)
      (fun he => ha (Subtype.ext he))
    have hp : IsPGroup 2 (zpowers (a : E)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])
    have hn : zpowers (a : E) ≠ ⊥ := by
      intro he
      exact ha (Subtype.ext (mem_bot.mp (he ▸ mem_zpowers (a : E))))
    have hh := cyclic_primeCore_centralizer_of_surjective_rank_le_two
      (by decide : Odd 3) hrank f hf hF (zpowers (a : E)) hp hn
    rw [zpowers_eq_closure, centralizer_closure] at hh
    change IsCyclic (MulAut.conjNormal (a : E) : MulAut (pCore 3 E)).fixedSubgroup
    rw [fixed_conjNormal]
    exact hh
  let C := (α t).fixedSubgroup
  let R := C.map (pCore 3 E).subtype
  have hC : Nat.card C = 3 := fixed_card_three α hT hV hcyc t ht
  have hR : Nat.card R = 3 := (card_map_of_injective (pCore 3 E).subtype_injective).trans hC
  have hnormal : R.Normal := by
    apply normal_fixed_image
    intro g
    have hk : pCore 3 E ≤ ρ.ker := by
      intro x hx
      apply MulEquiv.ext
      intro v
      apply Subtype.ext
      change x * (v : E) * x⁻¹ = v
      rw [setLike_mul_comm (s := pCore 3 E) hx v.property, mul_inv_cancel_right]
    have hc := hk (hcentral g)
    change ρ (g * (t : E) * g⁻¹ * (t : E)⁻¹) = 1 at hc
    have he : ⁅ρ g, ρ (t : E)⁆ = 1 := by
      simpa only [map_mul, map_inv, commutatorElement_def] using hc
    exact (commutatorElement_eq_one_iff_commute.mp he).symm
  refine ⟨R, hnormal, ?_, lt_of_le_of_ne (map_subtype_le C) ?_⟩
  · intro he
    have hc := card_eq_one.mpr he
    omega
  · intro he
    have hh := congrArg (fun H : Subgroup E => Nat.card H) he
    rw [hR, hV] at hh
    omega

end Theory.GroupTheory.ThreeSection
