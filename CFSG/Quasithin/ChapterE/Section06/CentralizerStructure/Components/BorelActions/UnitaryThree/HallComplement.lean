module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import Mathlib.GroupTheory.SchurZassenhaus

/-!
# Splitting the cyclic PSU₃ Borel action

An action kernel of index q − 1 in a group of order dividing q³(q² − 1)
has order dividing q³(q + 1). For even q these orders are coprime, so
Schur–Zassenhaus supplies a complement. The actual conjugation homomorphism
identifies its kernel with C_L(V), and maps the complement isomorphically
to the cyclic action specified in E.6.8(1).

The order bound is an explicit premise here. The owning unitary module
proves it from the PSU₃ model and the supplied Sylow subgroup before
assembling ModelWitness.
Source: Aschbacher–Smith E.6.8(1) and E.6.11, printed pp.247,249–250.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree

private theorem kernel_card_coprime_index
    {B A : Type*} [Group B] [Finite B] [Group A] {n : ℕ}
    (hn : 0 < n) (f : B →* A) (hi : f.ker.index = 2 ^ n - 1)
    (horder : Nat.card B ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1)) :
    Nat.Coprime (Nat.card f.ker) f.ker.index := by
  let q := 2 ^ n
  have hq : 1 < q := one_lt_pow₀ (by decide) (by omega)
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    simpa [mul_comm] using Nat.sq_sub_sq q 1
  have hd : (q - 1) * Nat.card f.ker ∣ (q - 1) * (q ^ 3 * (q + 1)) := by
    have ho : Nat.card B ∣ q ^ 3 * (q ^ 2 - 1) := horder
    rw [← f.ker.index_mul_card, hi] at ho
    change (q - 1) * Nat.card f.ker ∣ q ^ 3 * (q ^ 2 - 1) at ho
    simpa only [hfactor, mul_assoc, mul_left_comm, mul_comm] using ho
  have hk : Nat.card f.ker ∣ q ^ 3 * (q + 1) :=
    (Nat.mul_dvd_mul_iff_left (by omega : 0 < q - 1)).mp hd
  have hcq : Nat.Coprime (q - 1) q := by
    rw [Nat.coprime_self_sub_left (by omega)]
    exact Nat.coprime_one_left q
  have heven : Even q := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd : Odd (q - 1) := Nat.Even.sub_odd (by omega) heven odd_one
  have hplus : Nat.Coprime (q - 1) (q + 1) := by
    have hh : q + 1 = (q - 1) + 2 := by omega
    rw [hh, Nat.coprime_self_add_right]
    exact Nat.coprime_two_right.mpr hodd
  rw [hi]
  exact ((hcq.pow_right 3).mul_right hplus).symm.of_dvd_left hk

/-- Construct the cyclic complement from the PSU₃ normalizer order bound. -/
theorem complement_of_order_bound
    {G : Type*} [Group G] [Finite G]
    {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G} {n : ℕ}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 0 < n)
    (horder : Nat.card (L ⊓ M : Subgroup G) ∣ (2 ^ n) ^ 3 * ((2 ^ n) ^ 2 - 1)) :
    ∃ X : Subgroup G, X ≤ L ⊓ M ∧
      Nonempty (X ≃* Multiplicative (ZMod (2 ^ n - 1))) ∧
      (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M ∧
      (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥ := by
  have hp : 1 < 2 ^ n := one_lt_pow₀ (by decide) (by omega)
  let : NeZero (2 ^ n - 1) := ⟨by omega⟩
  let B := L ⊓ M
  have hBN := component_intersection_normalizes h hU hL.1
  let e := (subgroupOfEquivOfLe hBN).symm
  let f : B →* inducedAutomizer V B :=
    (V.normalizerMonoidHom.rangeRestrict.subgroupMap
      (B.subgroupOf (normalizer (V : Set G)))).comp e.toMonoidHom
  have hf : Function.Surjective f :=
    (MonoidHom.subgroupMap_surjective _ _).comp e.surjective
  obtain ⟨a⟩ := b.action
  have hi : f.ker.index = 2 ^ n - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_congr a.toEquiv]
    simp only [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hker : f.ker.map B.subtype = L ⊓ centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property.1, ?_⟩
      change (y : G) ∈ Subgroup.centralizer (V : Set G)
      have heq : V.normalizerMonoidHom ⟨(y : G), hBN y.property⟩ = 1 :=
        congrArg (fun z => z.val.val) hy
      simpa only [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] using
        (show (⟨(y : G), hBN y.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker from heq)
    · intro hx
      let y : B := ⟨x, hx.1, h.centralizer_le hx.2⟩
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      apply Subtype.ext
      apply Subtype.ext
      change V.normalizerMonoidHom ⟨x, hBN y.property⟩ = 1
      change (⟨x, hBN y.property⟩ : normalizer (V : Set G)) ∈ V.normalizerMonoidHom.ker
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hx.2
  obtain ⟨X₀, hc⟩ := exists_right_complement'_of_coprime
    (kernel_card_coprime_index hn f hi horder)
  let X := X₀.map B.subtype
  refine ⟨X, Subgroup.map_subtype_le X₀, ?_, ?_, ?_⟩
  · exact ⟨(X₀.equivMapOfInjective B.subtype B.subtype_injective).symm.trans
      (hc.symm.QuotientMulEquiv.symm.trans
        ((QuotientGroup.quotientKerEquivOfSurjective f hf).trans a))⟩
  · rw [← hker, ← Subgroup.map_sup, hc.sup_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · rw [← hker, ← Subgroup.map_inf _ _ _ B.subtype_injective,
      hc.disjoint.eq_bot, Subgroup.map_bot]

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions.UnitaryThree
