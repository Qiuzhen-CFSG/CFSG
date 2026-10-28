module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Common
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Alternating.Centers
public import Theory.Alternating.Aut
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Tactic

/-!
# Characteristic-two fixed actions on A₇

Every automorphism of A₇ is induced by a permutation. An involution has one,
two, or three transpositions. A single transposition fixes S₅, whose two-core
is trivial. Two transpositions leave three letters fixed; their three-cycle
generates a normal subgroup of order three in the literal fixed subgroup.
This subgroup centralizes the two-core, ruling out characteristic two.
Thus only cycle type (2,2,2) remains.

The marked-cover application retains the original automorphism and central
quotient map. Oddness of the center is an explicit hypothesis; the parent
source assembly owns its discharge and the even-cover exclusion.

Source: Aschbacher--Smith, proof of 1.1.5(3)(d), printed pp.502--503.
The sign-corrected S₅ construction is adapted from
`Theory/SpecificGroups/Alternating/SmallFixedComponents.lean`; its two-core
argument is adapted from the later-source Chapter15 alternating-seven
`FixedModel/Embedding.lean`. The original modules are preserved, and no
later chapter proof is imported.
-/

public section

namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
open Subgroup Equiv Equiv.Perm Theory.GroupTheory GLS3.Chapter5
open Chapter15.Section03.Candidates.ComponentStructure

private abbrev S7 := Perm (Fin 7)
private abbrev S5 := Perm (Fin 5)
private abbrev A7 := alternatingGroup (Fin 7)
private abbrev act : Perm (Fin 7) →* MulAut A7 := MulAut.conjNormal
private def t : Perm (Fin 7) := swap 0 1 * swap 2 3
private def c : A7 := ⟨swap 4 5 * swap 5 6, by simp [mem_alternatingGroup]⟩
private def z : (act t).fixedSubgroup := ⟨c, by
  rw [MulAut.mem_fixedSubgroup]
  apply Subtype.ext
  decide +kernel⟩
private lemma z_order : orderOf z = 3 := by
  apply orderOf_eq_prime
  · apply Subtype.ext
    apply Subtype.ext
    decide +kernel
  · intro h
    have he := congrArg (fun x : (act t).fixedSubgroup => x.val.val) h
    exact (by decide +kernel : c.val ≠ 1) he

private lemma conjugate_c (g : (act t).fixedSubgroup) :
    g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z⁻¹ := by
  have hg := congrArg Subtype.val ((MulAut.mem_fixedSubgroup _ _).mp g.property)
  change t * g.val.val * t⁻¹ = g.val.val at hg
  have hcomm := mul_inv_eq_iff_eq_mul.mp hg
  have hfixed (i : Fin 7) (hi : t i = i) : t (g.val.val i) = g.val.val i := by
    have h := congrArg (fun p : Perm (Fin 7) => p i) hcomm
    change t (g.val.val i) = g.val.val (t i) at h
    rwa [hi] at h
  have hcalc : ∀ i j k : Fin 7,
      t i = i → t j = j → t k = k → i ≠ j → j ≠ k → i ≠ k →
      swap i j * swap j k = c.val ∨ swap i j * swap j k = c.val⁻¹ := by
    decide +kernel
  have h := hcalc (g.val.val 4) (g.val.val 5) (g.val.val 6)
    (hfixed 4 (by decide)) (hfixed 5 (by decide)) (hfixed 6 (by decide))
    (g.val.val.injective.ne (by decide)) (g.val.val.injective.ne (by decide))
    (g.val.val.injective.ne (by decide))
  have he : g.val.val * c.val * g.val.val⁻¹ =
      swap (g.val.val 4) (g.val.val 5) * swap (g.val.val 5) (g.val.val 6) := by
    calc
      _ = (g.val.val * swap 4 5 * g.val.val⁻¹) *
          (g.val.val * swap 5 6 * g.val.val⁻¹) := by dsimp [c]; group
      _ = _ := by rw [swap_apply_apply, swap_apply_apply]
  rcases h with h | h
  · left; apply Subtype.ext; apply Subtype.ext; exact he.trans h
  · right; apply Subtype.ext; apply Subtype.ext; exact he.trans h

private instance normal_z : (zpowers z).Normal where
  conj_mem := by
    intro x hx g
    obtain ⟨k, rfl⟩ := hx
    change (MulAut.conj g) (z ^ k) ∈ zpowers z
    rw [map_zpow]
    apply zpow_mem
    rcases conjugate_c g with h | h
    · change g * z * g⁻¹ ∈ zpowers z
      rw [h]; exact mem_zpowers z
    · change g * z * g⁻¹ ∈ zpowers z
      rw [h]; exact inv_mem (mem_zpowers z)

private lemma double_obstruction : ¬ CFSG.Quasithin.HasCharacteristicTwo (act t).fixedSubgroup := by
  intro hchar
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := (act t).fixedSubgroup)).exists_card_eq
  have hd : Disjoint (zpowers z) (pCore 2 (act t).fixedSubgroup) :=
    disjoint_of_coprime_natCard (by
      rw [Nat.card_zpowers, z_order, hn]
      exact (by decide : Nat.Coprime 3 2).pow_right n)
  have hc := commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  have hz := hchar (hc (mem_zpowers z))
  have he : z = 1 := hd.le_bot ⟨mem_zpowers z, hz⟩
  have ho := z_order
  rw [he, orderOf_one] at ho
  contradiction

private def signPair : ℤˣ →* Perm (Fin 2) where
  toFun s := if s = 1 then 1 else swap 0 1
  map_one' := by simp
  map_mul' a b := by
    rcases Int.units_eq_one_or a with rfl | rfl <;>
      rcases Int.units_eq_one_or b with rfl | rfl <;> decide

private def fiveLetterExtension : Perm (Fin 5) →* S7 :=
  (Equiv.permCongrHom (finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7)).toMonoidHom.comp
    ((sumCongrHom (Fin 5) (Fin 2)).comp
      ((MonoidHom.id (Perm (Fin 5))).prod (signPair.comp sign)))

private theorem fiveLetterExtension_even (σ : Perm (Fin 5)) :
    fiveLetterExtension σ ∈ alternatingGroup (Fin 7) := by
  rw [mem_alternatingGroup]
  change sign ((finSumFinEquiv : Fin 5 ⊕ Fin 2 ≃ Fin 7).permCongr
    (Equiv.sumCongr σ (signPair (sign σ)))) = 1
  rw [sign_permCongr, sign_sumCongr]
  rcases Int.units_eq_one_or (sign σ) with h | h <;> rw [h] <;> decide

private theorem fiveLetterExtension_fixed : ∀ σ,
    swap (5 : Fin 7) 6 * fiveLetterExtension σ * (swap 5 6)⁻¹ =
      fiveLetterExtension σ := by
  decide +kernel

private def standardSwapEmbedding : Perm (Fin 5) →* A7 :=
  fiveLetterExtension.codRestrict _ fiveLetterExtension_even

private theorem standardSwapEmbedding_injective : Function.Injective standardSwapEmbedding := by
  intro σ τ h
  have hp := (Equiv.permCongrHom finSumFinEquiv).injective (congrArg Subtype.val h)
  have hq := sumCongrHom_injective hp
  exact congrArg Prod.fst hq

private def standardSwapFixedHom : Perm (Fin 5) →*
    automorphismFixedSubgroup (act (swap 5 6)) :=
  standardSwapEmbedding.codRestrict _ (fun σ => Subtype.ext (fiveLetterExtension_fixed σ))

private theorem standardSwapFixed_card :
    Nat.card (automorphismFixedSubgroup (act (swap 5 6))) = 120 := by
  let C : Subgroup S7 := centralizer {swap 5 6}
  let χ : C →* ℤˣ := sign.comp C.subtype
  have hc : Nat.card C = 240 := by
    rw [nat_card_centralizer]
    have hs : (swap (5 : Fin 7) 6).cycleType = {2} :=
      isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))
    rw [hs]
    norm_num [Nat.factorial]
  have hχ : Function.Surjective χ := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, map_one χ⟩
    · refine ⟨⟨swap 5 6, mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
      exact sign_swap (show (5 : Fin 7) ≠ 6 by decide)
  have hi : χ.ker.index = 2 := by
    rw [index_ker, MonoidHom.range_eq_top.mpr hχ, Nat.card_congr topEquiv.toEquiv]
    simp [Nat.card_eq_fintype_card]
  have hk := χ.ker.card_mul_index
  rw [hi, hc] at hk
  have he := Nat.card_congr (alternatingCentralizerSignKernelEquivFixedConjNormal
    (swap (5 : Fin 7) 6)).toEquiv
  change Nat.card χ.ker = _ at he
  change Nat.card χ.ker * 2 = 240 at hk
  rw [← he]
  omega

private noncomputable def standardSwapFixedEquiv :
    automorphismFixedSubgroup (act (swap 5 6)) ≃* Perm (Fin 5) :=
  (MulEquiv.ofBijective standardSwapFixedHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨
      fun _ _ h => standardSwapEmbedding_injective (congrArg Subtype.val h), by
        rw [standardSwapFixed_card]
        norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]⟩)).symm

private noncomputable def swapFixedEquiv (σ : S7) (hσ : σ.IsSwap) :
    automorphismFixedSubgroup (act σ) ≃* Perm (Fin 5) := by
  have hc : IsConj σ (swap (5 : Fin 7) 6) :=
    isConj_of_cycleType_eq ((isSwap_iff_cycleType.mp hσ).trans
      (isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide))).symm)
  let p := (isConj_iff.mp hc).choose
  have hp := (isConj_iff.mp hc).choose_spec
  refine (fixedSubgroupMulEquivOfCompat (act p) _ _ ?_).trans standardSwapFixedEquiv
  intro g
  have he : act p * act σ = act (swap 5 6) * act p := by
    rw [← map_mul, ← map_mul]
    exact congrArg act (mul_inv_eq_iff_eq_mul.mp hp)
  exact congrArg (fun a : MulAut A7 => a g) he

private lemma s5_twoCore_eq_bot : pCore 2 S5 = ⊥ := by
  by_contra h
  have hn : Nontrivial (pCore 2 S5) := (Subgroup.nontrivial_iff_ne_bot _).2 h
  have hle := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5)
    (by simp) hn
  have hp := (pCore_isPGroup (p := 2) (G := S5)).to_le hle
  obtain ⟨n, hn⟩ := hp.exists_card_dvd_pow
  have hc : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  rw [hc] at hn
  have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 60).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this
private lemma swap_obstruction (σ : S7) (hs : σ.IsSwap) :
    ¬ CFSG.Quasithin.HasCharacteristicTwo (act σ).fixedSubgroup := by
  intro h
  have hf : (act σ).fixedSubgroup = automorphismFixedSubgroup (act σ) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  rw [hf] at h
  have hc := h.of_equiv (swapFixedEquiv σ hs)
  change centralizer (pCore 2 S5 : Set S5) ≤ pCore 2 S5 at hc
  rw [s5_twoCore_eq_bot] at hc
  have he : (swap (0 : Fin 5) 1) = 1 := hc (by simp [mem_centralizer_iff])
  have hn : swap (0 : Fin 5) 1 ≠ 1 := by decide
  exact hn he

private noncomputable def fixedConjugacy (σ τ : Perm (Fin 7)) (hc : IsConj σ τ) :
    (MulAut.conjNormal (H := alternatingGroup (Fin 7)) σ).fixedSubgroup ≃*
      (MulAut.conjNormal (H := alternatingGroup (Fin 7)) τ).fixedSubgroup := by
  have hf (s : Perm (Fin 7)) :
      (MulAut.conjNormal (H := alternatingGroup (Fin 7)) s).fixedSubgroup =
        automorphismFixedSubgroup (MulAut.conjNormal s) := by
    ext x
    rw [MulAut.mem_fixedSubgroup]
    rfl
  rw [hf σ, hf τ]
  let p := (isConj_iff.mp hc).choose
  have hp := (isConj_iff.mp hc).choose_spec
  refine fixedSubgroupMulEquivOfCompat (act p) _ _ ?_
  intro g
  have he : act p * act σ =
      act τ * act p := by
    rw [← map_mul, ← map_mul]
    exact congrArg act (mul_inv_eq_iff_eq_mul.mp hp)
  exact congrArg (fun a : MulAut (alternatingGroup (Fin 7)) => a g) he

/-- Intrinsic restriction on characteristic-two fixed groups of involutions of A₇. -/
theorem seven_fixed_action (β : MulAut (alternatingGroup (Fin 7)))
    (hβ : orderOf β = 2) (hc : HasCharacteristicTwo β.fixedSubgroup) :
    ∃ σ : Perm (Fin 7), σ.cycleType = {2, 2, 2} ∧ β = MulAut.conjNormal σ := by
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    7 (by decide) (by decide)
  obtain ⟨σ, rfl⟩ := hbij.surjective β
  refine ⟨σ, ?_, rfl⟩
  have ho : orderOf σ = 2 := (orderOf_injective act hbij.injective σ).symm.trans hβ
  obtain ⟨k, hk⟩ := cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hb := σ.sum_cycleType_le
  rw [hk, Multiset.sum_replicate] at hb
  simp only [smul_eq_mul, Fintype.card_fin] at hb
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact (swap_obstruction σ
      (isSwap_iff_cycleType.mpr (by simpa using hk)) hc).elim
  · have ht : σ.cycleType = t.cycleType := by
      calc
        _ = {2, 2} := by simpa using hk
        _ = _ := by decide +kernel
    exact (double_obstruction
      (hc.of_equiv (fixedConjugacy σ t (isConj_of_cycleType_eq ht)))).elim
  · simpa using hk

variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
    {α : MulAut L} {P : Sylow 2 L}

/-- The marked A₇ model action once oddness of the cover's center is known. -/
theorem seven_of_odd_center (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* alternatingGroup (Fin 7))
    (hodd : Odd (Nat.card (center L))) : ModelAction115 L α := by
  obtain ⟨ho, hc, _, _⟩ := d.centralQuotient_model_inputs e
  obtain ⟨σ, hs, ha⟩ := seven_fixed_action (MulAut.centralQuotientAction e α) ho hc
  refine .seven σ hs (action_of_odd_center e (Or.inr rfl) hodd σ ?_)
  intro x
  have h := congrArg (fun a : MulAut (alternatingGroup (Fin 7)) =>
    a (e (QuotientGroup.mk' (center L) x))) ha
  rw [MulAut.centralQuotientAction_apply] at h
  exact congrArg Subtype.val h

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions.Alternating
