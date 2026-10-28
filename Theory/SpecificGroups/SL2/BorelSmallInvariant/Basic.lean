module

public import Theory.SpecificGroups.SL2.UpperUnipotent
public import Theory.GroupTheory.PResidual.Defs
public import Mathlib.Algebra.CharP.Reduced
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Small invariant subgroups of the rank-one Borel

The normalizer of the standard upper root group in SL₂(F) is precisely the
upper triangular subgroup. In a finite field of characteristic two, squaring
is surjective, so its diagonal torus is transitive on the nonidentity root
elements. Every nontrivial normalized root subgroup is therefore the whole
root group. Projecting to a nontrivial coordinate gives the same lower bound
for subgroups of two independently acted-on root groups.

For |F| ≥ 4 the torus has odd order and a nonidentity element. Its commutators
with the root group exhaust that group, so every two-group quotient of the
Borel is trivial. This proves B = O²(B), with the residual convention.

These are the elementary matrix calculations used in Aschbacher–Smith,
`refs/quasithin.pdf`, printed p.1164, proof of 15.4.20.
-/

@[expose] public section

open Matrix
open scoped MatrixGroups commutatorElement

namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F]
local notation "u" => transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one

/-- The actual normalizer of the standard upper unipotent subgroup. -/
abbrev rankOneBorel (F : Type*) [Field F] : Subgroup (SL(2, F)) :=
  Subgroup.normalizer (upperUnipotent F : Set (SL(2, F)))

theorem upper_mem_rankOneBorel (t : F) : u t ∈ rankOneBorel F :=
  (upperUnipotent F).le_normalizer ((mem_upperUnipotent F _).mpr ⟨t, rfl⟩)

theorem triangular_conj_upper {g : SL(2, F)} (hg : g.val 1 0 = 0) (t : F) :
    g * u t * g⁻¹ = u (g.val 0 0 ^ 2 * t) := by
  have hd : g.val 0 0 * g.val 1 1 = 1 := by
    simpa only [det_fin_two, hg, mul_zero, sub_zero] using g.property
  have hne : g.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h11 : g.val 1 1 = (g.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  have key : g * u t = u (g.val 0 0 ^ 2 * t) * g := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_apply, Fin.sum_univ_two, transvection_coe, hg, h11, sq, mul_assoc]
    field_simp
    ring
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

theorem mem_rankOneBorel_iff (g : SL(2, F)) : g ∈ rankOneBorel F ↔ g.val 1 0 = 0 := by
  constructor
  · intro hg
    have hu : g * u (1 : F) * g⁻¹ ∈ upperUnipotent F :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp
        ((mem_upperUnipotent F _).mpr ⟨1, rfl⟩)
    obtain ⟨t, ht⟩ := (mem_upperUnipotent F _).mp hu
    have he := congrArg (fun A : SL(2, F) => A.val 1 0) ht
    simp [adjugate_fin_two, mul_apply, Fin.sum_univ_two, transvection_coe] at he
    exact mul_self_eq_zero.mp (by linear_combination he)
  · intro hg
    have hconj (a : SL(2, F)) (ha : a.val 1 0 = 0) (x : SL(2, F))
        (hx : x ∈ upperUnipotent F) : a * x * a⁻¹ ∈ upperUnipotent F := by
      obtain ⟨t, rfl⟩ := (mem_upperUnipotent F x).mp hx
      rw [triangular_conj_upper ha]
      exact (mem_upperUnipotent F _).mpr ⟨_, rfl⟩
    apply Subgroup.mem_normalizer_iff.mpr
    intro x
    constructor
    · exact hconj g hg x
    · intro hx
      have hi : g⁻¹.val 1 0 = 0 := by simp [adjugate_fin_two, hg]
      simpa [mul_assoc] using hconj g⁻¹ hi _ hx

theorem diag_mem_rankOneBorel (a : F) (ha : a ≠ 0) :
    diag2 a ha ∈ rankOneBorel F := by
  rw [mem_rankOneBorel_iff]
  simp [diag2_coe']

theorem diag_conj_upper (a : F) (ha : a ≠ 0) (t : F) :
    diag2 a ha * u t * (diag2 a ha)⁻¹ = u (a ^ 2 * t) := by
  simpa [diag2_coe'] using
    triangular_conj_upper ((mem_rankOneBorel_iff _).mp (diag_mem_rankOneBorel a ha)) t

theorem rankOneBorel_factor (g : rankOneBorel F) :
    ∃ (t a : F) (ha : a ≠ 0), (g : SL(2, F)) = u t * diag2 a ha := by
  have h10 := (mem_rankOneBorel_iff g.val).mp g.property
  have hd : g.val.val 0 0 * g.val.val 1 1 = 1 := by
    simpa only [det_fin_two, h10, mul_zero, sub_zero] using g.val.property
  have ha : g.val.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hd
  have h11 : g.val.val 1 1 = (g.val.val 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hd
  refine ⟨g.val.val 0 1 * g.val.val 0 0, g.val.val 0 0, ha, ?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mul_apply, Fin.sum_univ_two, transvection_coe, diag2_coe',
      h10, h11, mul_assoc, mul_inv_cancel₀ ha]

variable [Finite F] [CharP F 2]

/-- A nontrivial root subgroup normalized by the Borel is the whole root group. -/
theorem eq_upperUnipotent_of_normalized (W : Subgroup (SL(2, F)))
    (hWU : W ≤ upperUnipotent F) (hne : W ≠ ⊥)
    (hn : rankOneBorel F ≤ Subgroup.normalizer (W : Set (SL(2, F)))) : W = upperUnipotent F := by
  rcases W.bot_or_exists_ne_one with h | ⟨w, hw, hw1⟩
  · exact (hne h).elim
  obtain ⟨t, rfl⟩ := (mem_upperUnipotent F w).mp (hWU hw)
  have ht : t ≠ 0 := by
    intro h; subst t; exact hw1 (transvection_coeff_zero _)
  apply le_antisymm hWU
  intro x hx
  obtain ⟨s, rfl⟩ := (mem_upperUnipotent F x).mp hx
  by_cases hs : s = 0
  · subst s; simpa only [transvection_coeff_zero] using W.one_mem
  obtain ⟨a, ha⟩ := isSquare_of_charTwo' (s / t)
  have ha0 : a ≠ 0 := by
    intro h; simp [h, div_eq_zero_iff, hs, ht] at ha
  have he : a ^ 2 * t = s := by rw [sq, ← ha, div_mul_cancel₀ _ ht]
  have hm := (Subgroup.mem_normalizer_iff.mp
    (hn (diag_mem_rankOneBorel a ha0)) (u t)).mp hw
  simpa only [diag_conj_upper, he] using hm

noncomputable def borelDiagonalHom : Fˣ →* rankOneBorel F where
  toFun a := ⟨diag2 a a.ne_zero, diag_mem_rankOneBorel (a : F) a.ne_zero⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;> simp [diag2_coe']
  map_mul' a b := by
    apply Subtype.ext; apply Subtype.ext
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [diag2_coe', mul_apply, Fin.sum_univ_two, mul_comm]

/-- The Borel has no nontrivial two-group quotient when the field has at least four elements. -/
theorem rankOneBorel_isPPerfect (hq : 4 ≤ Nat.card F) : IsPPerfect 2 (rankOneBorel F) := by
  classical
  let := Fintype.ofFinite F
  have heven : Even (Nat.card F) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.even_iff.mpr (FiniteField.even_card_of_char_two (ringChar.eq F 2))
  have hodd : Odd (Nat.card Fˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd (by omega) heven odd_one
  have hlarge : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hlarge
  obtain ⟨a, ha⟩ := exists_ne (1 : Fˣ)
  have ha1 : (a : F) ≠ 1 := by simpa using ha
  have hasq : (a : F) ^ 2 ≠ 1 := by
    intro h
    apply ha1
    exact (frobenius_inj F 2) (by simpa [frobenius_def] using h)
  intro N hN hQ
  let := hN
  let π := QuotientGroup.mk' N
  have hdiag (b : Fˣ) : borelDiagonalHom b ∈ N := by
    apply (QuotientGroup.eq_one_iff _).mp
    obtain ⟨k, hk⟩ := hQ (π (borelDiagonalHom b))
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (hodd.coprime_two_left.pow_left k)
    · exact orderOf_dvd_of_pow_eq_one hk
    · exact dvd_trans (orderOf_map_dvd (π.comp borelDiagonalHom) b) (orderOf_dvd_natCard b)
  have hu (t : F) : (⟨u t, upper_mem_rankOneBorel t⟩ : rankOneBorel F) ∈ N := by
    let b := t / ((a : F)^2 - 1)
    let d : rankOneBorel F := borelDiagonalHom a
    let v : rankOneBorel F := ⟨u b, upper_mem_rankOneBorel b⟩
    have hc : ⁅d, v⁆ ∈ N := by
      simpa only [commutatorElement_def, mul_assoc] using
        N.mul_mem (hdiag a) (hN.conj_mem _ (N.inv_mem (hdiag a)) v)
    have he : ⁅d, v⁆ = ⟨u t, upper_mem_rankOneBorel t⟩ := by
      apply Subtype.ext
      exact commutator_diag2_transvection (a : F) a.ne_zero b t
        (div_mul_cancel₀ t (sub_ne_zero_of_ne hasq)).symm
    exact he ▸ hc
  apply top_unique
  intro g _
  obtain ⟨t, b, hb, he⟩ := rankOneBorel_factor g
  have hg : g = ⟨u t, upper_mem_rankOneBorel t⟩ * borelDiagonalHom (Units.mk0 b hb) :=
    Subtype.ext he
  rw [hg]
  exact N.mul_mem (hu t) (hdiag _)

/-- A nontrivial subgroup of two root groups, normalized by the product Borel, has order ≥ |F|. -/
theorem card_le_of_root_prod_normalized
    (W : Subgroup (SL(2, F) × SL(2, F)))
    (hWU : W ≤ (upperUnipotent F).prod (upperUnipotent F)) (hne : W ≠ ⊥)
    (hn : (rankOneBorel F).prod (rankOneBorel F) ≤ Subgroup.normalizer (W : Set _)) :
    Nat.card F ≤ Nat.card W := by
  have hproj (f : (SL(2, F) × SL(2, F)) →* SL(2, F))
      (hfU : W.map f ≤ upperUnipotent F)
      (hfB : rankOneBorel F ≤ ((rankOneBorel F).prod (rankOneBorel F)).map f)
      (hfne : W.map f ≠ ⊥) : Nat.card F ≤ Nat.card W := by
    have hfn : rankOneBorel F ≤ Subgroup.normalizer (W.map f : Set _) :=
      hfB.trans ((Subgroup.map_mono hn).trans (Subgroup.le_normalizer_map f))
    have he := eq_upperUnipotent_of_normalized (W.map f) hfU hfne hfn
    calc
      Nat.card F = Nat.card (W.map f) := by rw [he, card_upperUnipotent]
      _ ≤ Nat.card W := Nat.card_image_le (Set.toFinite _)
  rcases W.bot_or_exists_ne_one with h | ⟨w, hw, hw1⟩
  · exact (hne h).elim
  by_cases hfirst : w.1 = 1
  · apply hproj (MonoidHom.snd _ _) (Subgroup.le_prod_iff.mp hWU).2
    · intro b hb; exact ⟨(1, b), ⟨(rankOneBorel F).one_mem, hb⟩, rfl⟩
    · intro h
      have hm : w.2 ∈ W.map (MonoidHom.snd _ _) := ⟨w, hw, rfl⟩
      rw [h, Subgroup.mem_bot] at hm
      exact hw1 (Prod.ext hfirst hm)
  · apply hproj (MonoidHom.fst _ _) (Subgroup.le_prod_iff.mp hWU).1
    · intro b hb; exact ⟨(b, 1), ⟨hb, (rankOneBorel F).one_mem⟩, rfl⟩
    · intro h
      have hm : w.1 ∈ W.map (MonoidHom.fst _ _) := ⟨w, hw, rfl⟩
      rw [h, Subgroup.mem_bot] at hm
      exact hfirst hm

end Matrix.SpecialLinearGroup

