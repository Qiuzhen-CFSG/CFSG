module

public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.LocalData
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.Transfer
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.Transfer
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Sylow three-subgroups from a nonsplit G₂ torus normalizer

An embedded product of two cyclic groups of order q+1 has index with exactly
one factor of three when q is minus one modulo three. Adjoin a disjoint
normalizing element of order three to the torus's Sylow three-subgroup.
The resulting subgroup is Sylow in the literal octonion automorphism model.
The full torus's swap and inversion formulas restrict to its generators,
providing every field of `LocalData` without a bound on the valuation of q+1.

The geometric torus and Weyl elements remain explicit inputs here; descent
constructs them in the parent development. This is a conditional local
calculation, not an assertion of the ordinary multiplier theorem.

Source: the ordinary G₂ entry underlying Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1. The G₂ model and order formula are
licensed ATLAS ports; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
open Subgroup
variable {F : Type*} [Field F] [Finite F]

private theorem nine_not_dvd_torus_index {C : Type*} [Group C] [Finite C]
    (ι : C × C →* Model F) (hi : Function.Injective ι)
    (hC : Nat.card C = Nat.card F + 1) (hd : 3 ∣ Nat.card F + 1) :
    ¬ 9 ∣ ι.range.index := by
  rw [OddQuadraticTorus.quadratic_index ι hC,
    (MonoidHom.ker_eq_bot_iff ι).mpr hi, card_bot, one_mul]
  have hq : Nat.card F % 3 = 2 := by omega
  intro he
  have hzero := (CharP.cast_eq_zero_iff (ZMod 9) 9 _).mpr he
  obtain ⟨a, ha, hqa⟩ : ∃ a : Fin 9, a.val % 3 = 2 ∧ (Nat.card F : ZMod 9) = a := by
    refine ⟨⟨Nat.card F % 9, Nat.mod_lt _ (by decide)⟩, ?_, rfl⟩
    simpa [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] using hq
  simp only [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub (show 1 ≤ Nat.card F from Nat.card_pos),
    Nat.cast_add, Nat.cast_one, hqa] at hzero
  have hcalc : ∀ a : Fin 9, a.val % 3 = 2 →
      (a : ZMod 9)^6 * (a-1)^2 * (a^4+a^2+1) ≠ 0 := by decide +kernel
  exact hcalc a ha hzero

/-- The full nonsplit torus and its rational Weyl actions construct every
field of `LocalData`, with no restriction on the three-part of q+1. -/
theorem exists_localData_of_torus
    {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]
    (ι : C × C →* Model F) (hi : Function.Injective ι)
    (hC : Nat.card C = Nat.card F + 1) (hd : 3 ∣ Nat.card F + 1)
    (c s w : Model F) (hc : c^3 = 1) (hcout : c ∉ ι.range)
    (hcycle : ∀ l m, c * ι (l,m) * c⁻¹ = ι (m*l⁻¹,l⁻¹))
    (hswap : ∀ l m, s * ι (l,m) * s⁻¹ = ι (m,l))
    (hinv : ∀ l m, w * ι (l,m) * w⁻¹ = (ι (l,m))⁻¹)
    (hfix : Commute w c) : Nonempty (LocalData F) := by
  let P : Sylow 3 C := Classical.choice inferInstance
  let T : Subgroup (Model F) := ((P : Subgroup C).prod (P : Subgroup C)).map ι
  have hTle : T ≤ ι.range := map_le_range _ _
  have hcord : orderOf c = 3 := orderOf_eq_prime hc (fun he => hcout (he ▸ ι.range.one_mem))
  have hnorm : c ∈ normalizer (T : Set (Model F)) := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,rfl⟩
      exact ⟨(m*l⁻¹,l⁻¹), ⟨P.mul_mem hm (P.inv_mem hl), P.inv_mem hl⟩,
        (hcycle l m).symm⟩
    · rintro ⟨⟨l,m⟩,⟨hl,hm⟩,he⟩
      refine ⟨(m⁻¹,l*m⁻¹),⟨P.inv_mem hm,P.mul_mem hl (P.inv_mem hm)⟩,?_⟩
      apply (MulAut.conj c).injective
      change c*ι (m⁻¹,l*m⁻¹)*c⁻¹ = c*x*c⁻¹
      rw [hcycle]
      simpa using he
  have hcnorm : zpowers c ≤ normalizer (T : Set (Model F)) := zpowers_le.mpr hnorm
  have hdis : Disjoint T (zpowers c) :=
    T.disjoint_zpowers_of_prime_order_not_mem c hcord (fun hc => hcout (hTle hc))
  let H := T ⊔ zpowers c
  have hcardH : Nat.card H = Nat.card T * 3 := by
    dsimp [H]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint T _ hcnorm hdis, Nat.card_zpowers,hcord]
  have hindex : 3 * H.index = T.index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := T))
    rw [← mul_assoc, ← hcardH, H.card_mul_index, T.card_mul_index]
  have hTindex : T.index = (P : Subgroup C).index * (P : Subgroup C).index * ι.range.index := by
    dsimp [T]
    rw [index_map_of_injective _ hi,index_prod]
  have hnotnine : ¬ 9 ∣ T.index := by
    rw [hTindex]
    have hcop : Nat.Coprime 9 ((P : Subgroup C).index * (P : Subgroup C).index) := by
      apply Nat.Coprime.pow_left (m := 3) (n := 2)
      exact (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index).mul_right
        (Nat.prime_three.coprime_iff_not_dvd.mpr P.not_dvd_index)
    exact fun hh => nine_not_dvd_torus_index ι hi hC hd (hcop.dvd_mul_left.mp hh)
  have hHindex : ¬ 3 ∣ H.index := by
    intro hi
    apply hnotnine
    rw [← hindex]
    exact Nat.mul_dvd_mul_left 3 hi
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have hTp : IsPGroup 3 T := by
    apply IsPGroup.map
    apply IsPGroup.of_card (n := k+k)
    rw [Nat.card_congr (Subgroup.prodEquiv (P : Subgroup C) (P : Subgroup C)).toEquiv,
      Nat.card_prod,hk,pow_add]
  have hcp : IsPGroup 3 (zpowers c) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hcord,pow_one])
  let Q : Sylow 3 (Model F) := (hTp.to_sup_of_normal_left' hcp hcnorm).toSylow hHindex
  obtain ⟨z,hz⟩ := IsCyclic.exists_generator (α := P)
  refine ⟨{
    sylow := Q
    torus := T
    first := ι (z,1)
    second := ι (1,z)
    cycle := c
    swap := s
    inverter := w
    torus_generated := OddQuadraticTorus.pair_generates ι _ z hz
    generators_commute := (Commute.all ((z : C),1) (1,(z : C))).map ι
    swap_first := hswap z 1
    swap_second := hswap 1 z
    sylow_generated := rfl
    cycle_normalizes := hnorm
    inverts_torus := ?_
    fixes_cycle := hfix }⟩
  rintro t ⟨⟨l,m⟩,_,rfl⟩
  exact hinv l m
end Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
end
