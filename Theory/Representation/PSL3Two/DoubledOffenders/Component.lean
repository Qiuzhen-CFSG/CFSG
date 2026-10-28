module

public import Theory.Representation.PSL3Two.DoubledFixedSpace
public import Theory.SpecificGroups.PSL3Two.SourceFlag
public import Theory.Representation.BinaryOffender.PermutationConjugacy
/-!
# Offenders in the upper-triangular component Sylow

An elementary subgroup of UT₃(2) has rank at most two, since UT₃(2) itself
contains an element of order four. Every nonidentity upper-triangular matrix
has at most sixteen fixed vectors on the doubled module, forcing an offender
to have rank two. If it contains a matrix outside the marked shear radical,
a second independent element reduces the common fixed space to at most four
vectors, contradicting the offender inequality. The small certificates check
only eight matrices and 64 vectors; no GL₆(2) enumeration is used.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the central
branch of 13.6.20, printed p.931.
-/

public section
open Matrix Representation Representation.BinaryOffender Subgroup
open Matrix.PSL3Two
namespace BinaryLinearThree.DoubledOffenders
private theorem upper_injective : Function.Injective Bruhat.upper := by decide +kernel
private theorem upper_covers (g : Group) (hg : g ∈ borelSL) : ∃ i, Bruhat.upper i = g := by
  let f : Fin 8 → borelSL := fun i => ⟨Bruhat.upper i, Bruhat.upper_mem i⟩
  have hi : Function.Injective f := fun i j h => upper_injective (congrArg Subtype.val h)
  have hs : Function.Surjective f := (Nat.bijective_iff_injective_and_card f).mpr
    ⟨hi, by rw [card_borelSL, Nat.card_fin]⟩ |>.2
  obtain ⟨i, he⟩ := hs ⟨g, hg⟩
  exact ⟨i, congrArg Subtype.val he⟩

private theorem upper_single_fixed_card : ∀ i : Fin 8, Bruhat.upper i ≠ 1 →
    Fintype.card {v : Vector × Vector // (W.prod W) (Bruhat.upper i) v = v} ≤ 16 := by
  decide +kernel

private theorem upper_pair_fixed_card : ∀ i j : Fin 8,
    (Bruhat.upper i).val 0 1 ≠ 0 →
    Bruhat.upper j ≠ 1 → Bruhat.upper j ≠ Bruhat.upper i →
    Fintype.card {v : Vector × Vector //
      (W.prod W) (Bruhat.upper i) v = v ∧ (W.prod W) (Bruhat.upper j) v = v} ≤ 4 := by
  decide +kernel

private theorem upper_mem_R_iff (i : Fin 8) : Bruhat.upper i ∈ R ↔
    (Bruhat.upper i).val 0 1 = 0 := by
  constructor
  · rintro ⟨x, hx⟩
    exact congrArg (fun g : Group => g.val 0 1) hx.symm
  · intro hi
    refine ⟨Multiplicative.ofAdd ((Bruhat.upper i).val 0 2, (Bruhat.upper i).val 1 2), ?_⟩
    revert hi
    revert i
    decide +kernel

private theorem dim_le_of_card (S : Submodule (ZMod 2) (Vector × Vector))
    {n : ℕ} (hc : Nat.card S ≤ 2 ^ n) : Module.finrank (ZMod 2) S ≤ n := by
  have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S)
  rw [Nat.card_zmod] at he
  exact (pow_le_pow_iff_right₀ (by decide : 1 < 2)).mp (he ▸ hc)

private theorem rank_upper {E : Subgroup Group} (hE : IsElementaryTwo E)
    (hEB : E ≤ borelSL) : rank E ≤ 2 := by
  let : IsElementaryAbelian 2 E := hE.2
  have hne : E ≠ borelSL := by
    intro he
    have hs := elemPow_eq_one_of_isElementaryAbelian (p := 2) (Bruhat.upper 5)
      (he ▸ Bruhat.upper_mem 5)
    exact (by decide : Bruhat.upper 5 ^ 2 ≠ 1) hs
  have hc : Nat.card E < 8 := by
    have hle := card_le_of_le hEB
    rw [card_borelSL] at hle
    have hn : Nat.card E ≠ 8 := fun he => hne
      (eq_of_le_of_card_ge hEB (by rw [card_borelSL, he]))
    omega
  exact Nat.le_of_lt_succ (Nat.log_lt_of_lt_pow' (by decide : 3 ≠ 0) hc)

private theorem rank_lower {E : Subgroup Group} (hE : IsOffender (W.prod W) E)
    (hEB : E ≤ borelSL) : 2 ≤ rank E := by
  obtain ⟨g, hg⟩ := ne_bot_iff_exists_ne_one.mp hE.1.1
  have hg' : (g : Group) ≠ 1 := fun he => hg (Subtype.ext he)
  obtain ⟨i, hi⟩ := upper_covers g (hEB g.property)
  let f : fixedSpace (W.prod W) E →
      {v : Vector × Vector // (W.prod W) (Bruhat.upper i) v = v} :=
    fun v => ⟨v, hi ▸ v.property g⟩
  have hinj : Function.Injective f := by
    intro x y he
    have hv := congrArg Subtype.val he
    exact Subtype.ext hv
  have hc := Nat.card_le_card_of_injective f hinj
  rw [Nat.card_eq_fintype_card (α := {v : Vector × Vector //
    (W.prod W) (Bruhat.upper i) v = v})] at hc
  have hd := dim_le_of_card (fixedSpace (W.prod W) E)
    (n := 4) (hc.trans (upper_single_fixed_card i (hi ▸ hg')))
  have he := fixedCodim_add_finrank (W.prod W) E
  have hdim : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
    simp [Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]
  rw [hdim] at he
  have := hE.2
  omega

lemma offender_borel_iff (E : Subgroup Group) (hEB : E ≤ borelSL) :
    IsOffender (W.prod W) E ↔ E = R := by
  constructor
  · intro hE
    let : IsElementaryAbelian 2 E := hE.1.2
    have hlo := rank_lower hE hEB
    have hhi := rank_upper hE.1 hEB
    have hER : E ≤ R := by
      by_contra hn
      obtain ⟨g, hg, hgR⟩ := SetLike.not_le_iff_exists.mp hn
      have hgz : Nat.card (zpowers g) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one
          (elemPow_eq_one_of_isElementaryAbelian g hg))
      have hnz : ¬ E ≤ zpowers g := by
        intro hh
        have hc : Nat.card E ≤ 2 := (card_le_of_le hh).trans hgz
        have hl := Nat.log_mono_right hc (b := 2)
        change rank E ≤ Nat.log 2 2 at hl
        rw [show Nat.log 2 2 = 1 by decide] at hl
        omega
      obtain ⟨h, hh, hhz⟩ := SetLike.not_le_iff_exists.mp hnz
      have hhn : h ≠ 1 := fun he => hhz (he ▸ (zpowers g).one_mem)
      have hhg : h ≠ g := fun he => hhz (he ▸ mem_zpowers g)
      obtain ⟨i, hi⟩ := upper_covers g (hEB hg)
      obtain ⟨j, hj⟩ := upper_covers h (hEB hh)
      have hia : (Bruhat.upper i).val 0 1 ≠ 0 := by
        intro ha
        exact hgR (hi ▸ (upper_mem_R_iff i).mpr ha)
      let f : fixedSpace (W.prod W) E → {v : Vector × Vector //
          (W.prod W) (Bruhat.upper i) v = v ∧ (W.prod W) (Bruhat.upper j) v = v} :=
        fun v => ⟨v, hi ▸ v.property ⟨g, hg⟩, hj ▸ v.property ⟨h, hh⟩⟩
      have hinj : Function.Injective f := by
        intro x y he
        have hv := congrArg Subtype.val he
        exact Subtype.ext hv
      have hc := Nat.card_le_card_of_injective f hinj
      rw [Nat.card_eq_fintype_card (α := {v : Vector × Vector //
        (W.prod W) (Bruhat.upper i) v = v ∧ (W.prod W) (Bruhat.upper j) v = v})] at hc
      have hd := dim_le_of_card (fixedSpace (W.prod W) E) (n := 2)
        (hc.trans (upper_pair_fixed_card i j hia (hj ▸ hhn) (by simpa [hi, hj] using hhg)))
      have he := fixedCodim_add_finrank (W.prod W) E
      have hdim : Module.finrank (ZMod 2) (Vector × Vector) = 6 := by
        simp [Vector, Matrix.PSL3Two.Fano.Vector, Module.finrank_prod]
      rw [hdim] at he
      have := hE.2
      omega
    apply eq_of_le_of_card_ge hER
    rw [card_R]
    by_contra hn
    have hl := Nat.log_lt_of_lt_pow' (by decide : 2 ≠ 0) (show Nat.card E < 2 ^ 2 by omega)
    change rank E < 2 at hl
    omega
  · rintro rfl
    exact DoubledFixedSpace.radical_isOffender
end BinaryLinearThree.DoubledOffenders
