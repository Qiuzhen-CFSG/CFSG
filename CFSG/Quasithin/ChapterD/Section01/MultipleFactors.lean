module
public import CFSG.Quasithin.ChapterD.Section01.MultipleFactors.GeneratorEstimates

/-!
# D.1.3: numerical and equality deductions from the actual actions

These conditional assembly lemmas construct the rank estimates from maximal
elementary order, the faithful actions on the literal chief factors, and the
quadratic ratios on invariant generators. They exclude the infinite-ratio case
before applying the real numerical lemmas, and retain equality both on each
noncentral factor and on the actual centralizers in U.

The source theorem still requires construction of the quadratic maximum actor,
the parabolic chief-factor kernel and ratio inputs, and the conjugate-generator
cover with its transported ratio. Those are separate source obligations, not
conclusions supplied by this module's hypotheses under another name.

Source: Aschbacher--Smith, D.1.3, printed pp.173--175. The equality conclusions
are the numerical input to 3.1.9(1)--(3), printed pp.576--577.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterD.MultipleFactors
open Subgroup NoncentralChiefRefinement Representation Representation.BinaryOffender
open scoped ENNReal IsMulCommutative
variable {H : Type*} [Group H] [Finite H]
  (U : Subgroup H) [U.Normal] [IsElementaryAbelian 2 U]

omit [Finite H] in
/-- The denominator in (j) is literally m(B/C_B(U)). -/
theorem actionKernel_quotient_rank (B : Subgroup H) :
    Nat.log 2 (Nat.card (B ⧸ qrcActionKernel U B)) =
      Nat.log 2 ((centralizer (U : Set H)).relIndex B) := by
  rw [qrcActionKernel_eq_centralizer, ← index_eq_card]
  rfl

omit [Finite H] in
private theorem normal_fixedSpace_antitone {A B : Subgroup H} (hBA : B ≤ A) :
    fixedSpace (normalRepresentation U) A ≤ fixedSpace (normalRepresentation U) B := by
  intro v hv b
  exact hv ⟨b, hBA b.property⟩

omit [Finite H] in
private theorem mem_normal_fixedSpace (A : Subgroup H) (v : Additive U) :
    v ∈ fixedSpace (normalRepresentation U) A ↔ (v.toMul : H) ∈ centralizer (A : Set H) := by
  constructor
  · intro hv a ha
    have he := congrArg (fun w : Additive U => (w.toMul : H)) (hv ⟨a, ha⟩)
    change a * (v.toMul : H) * a⁻¹ = v.toMul at he
    exact mul_inv_eq_iff_eq_mul.mp he
  · intro hv a
    apply Additive.toMul.injective
    apply Subtype.ext
    change (a : H) * v.toMul * (a : H)⁻¹ = v.toMul
    rw [hv a a.property, mul_inv_cancel_right]

omit [Finite H] in
/-- Equality of the fixed subspaces is equality of the literal relative centralizers. -/
theorem centralizers_eq_of_fixedSpaces_eq (A B : Subgroup H)
    (he : fixedSpace (normalRepresentation U) A = fixedSpace (normalRepresentation U) B) :
    U ⊓ centralizer (A : Set H) = U ⊓ centralizer (B : Set H) := by
  ext u
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have hf := (mem_normal_fixedSpace U A (Additive.ofMul ⟨u, hu⟩)).mpr hc
    rw [he] at hf
    exact (mem_normal_fixedSpace U B _).mp hf
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    have hf := (mem_normal_fixedSpace U B (Additive.ofMul ⟨u, hu⟩)).mpr hc
    rw [← he] at hf
    exact (mem_normal_fixedSpace U A _).mp hf

private theorem fixedCodim_mono {A B : Subgroup H} (hBA : B ≤ A) :
    fixedCodim (normalRepresentation U) B ≤ fixedCodim (normalRepresentation U) A := by
  have hm := Submodule.finrank_mono (normal_fixedSpace_antitone U hBA)
  have ha := fixedCodim_add_finrank (normalRepresentation U) A
  have hb := fixedCodim_add_finrank (normalRepresentation U) B
  omega

/-- D.1.3(1) after the source's actor, parabolic-action and conjugate-generator
constructions. Every numerical input is derived here from those actual actions. -/
theorem rank_bound_of_action_images (s : SeriesOn U) (S A R₂ : Subgroup H)
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hAR : ¬ A ≤ R₂) (hc : 1 < s.noncentralCount)
    (hquad : IsQuadratic (normalRepresentation U) A)
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂)
    (hfactor : ∀ i, ¬ s.Central i → A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hfactorRatio : ∀ i, ¬ s.Central i →
      1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i)))
    (q : ℝ≥0∞) (hq : 1 < q)
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp (A ⊓ R₂).subtype))
    (n : ℕ)
    (hgen : generatingSpan ((normalRepresentation U).comp (A ⊓ R₂).subtype) W n = ⊤)
    (hgenRatio : ∀ i < n, q ≤ quadraticRatio (imageRepresentation (W i).toRepresentation)) :
    q ≤ 2 := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ R₂ : Subgroup H) :=
    IsElementaryAbelian.of_le (inf_le_left : A ⊓ R₂ ≤ A)
  have hqB : IsQuadratic (normalRepresentation U) (A ⊓ R₂) :=
    fun a ha b hb v => hquad a ha.1 b hb.1 v
  have hn := core_intersection_nontrivial_action U s S A R₂ hUS hA hAR hc
    hquad hkernel hfactor hfactorRatio
  have hf := generator_ratio_ne_top U (A ⊓ R₂) W q n hgen hqB hn hgenRatio
  have hqR : (1 : ℝ) < q.toReal := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal (by simp) hf).mpr hq
  have ha : (0 : ℝ) < Nat.log 2 (R₂.relIndex A) := by
    exact_mod_cast quotient_rank_pos A R₂ hAR
  have hb := generator_rank_bound U (A ⊓ R₂) W q n hf hgen hqB hgenRatio
  rw [actionKernel_quotient_rank] at hb
  have hm : (fixedCodim (normalRepresentation U) (A ⊓ R₂) : ℝ) ≤
      fixedCodim (normalRepresentation U) A := by
    exact_mod_cast fixedCodim_mono U (inf_le_left : A ⊓ R₂ ≤ A)
  have bound := qrc_rank_bound hqR ha (by exact_mod_cast hc)
    (maxElementary_rank_upper U S A R₂ hUS hA hkernel) (hb.trans hm)
    (chief_rank_lower U s A R₂ hquad hfactor hfactorRatio)
  apply (ENNReal.toReal_le_toReal hf (by simp)).mp
  simpa using bound

/-- Equality at ratio two forces both rank equalities, equality of the actual
centralizers inside U, and the exact rank on every noncentral chief quotient. -/
theorem rank_equality_of_action_images (s : SeriesOn U) (S A R₂ : Subgroup H)
    (hUS : U ≤ S) (hA : A ∈ Stellmacher.elementaryAbelianMaxSubgroups S)
    (hAR : ¬ A ≤ R₂) (hc : 1 < s.noncentralCount)
    (hquad : IsQuadratic (normalRepresentation U) A)
    (hkernel : A ⊓ centralizer (U : Set H) ≤ R₂)
    (hfactor : ∀ i, ¬ s.Central i → A ⊓ (s.factorRepresentation i).ker = A ⊓ R₂)
    (hfactorRatio : ∀ i, ¬ s.Central i →
      1 ≤ quadraticRatio (imageRepresentation (s.factorRepresentation i)))
    (W : ℕ → Subrepresentation ((normalRepresentation U).comp (A ⊓ R₂).subtype))
    (n : ℕ)
    (hgen : generatingSpan ((normalRepresentation U).comp (A ⊓ R₂).subtype) W n = ⊤)
    (hgenRatio : ∀ i < n, 2 ≤ quadraticRatio (imageRepresentation (W i).toRepresentation)) :
    s.noncentralCount = 2 ∧
      2 * Nat.log 2 (R₂.relIndex A) = fixedCodim (normalRepresentation U) A ∧
      fixedCodim (normalRepresentation U) A =
        2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ R₂)) ∧
      U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ R₂ : Set H) ∧
      (∀ i, ¬ s.Central i →
        Nat.log 2 (R₂.relIndex A) = fixedCodim (s.factorRepresentation i) A) ∧
      (0 < n → (fixedCodim (W 0).toRepresentation ⊤ : ℝ) = 2 * (Nat.log 2
        (subspaceKernel ((normalRepresentation U).comp (A ⊓ R₂).subtype)
          (W 0).toSubmodule ⊤).index : ℝ)) := by
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 (A ⊓ R₂ : Subgroup H) :=
    IsElementaryAbelian.of_le (inf_le_left : A ⊓ R₂ ≤ A)
  have hqB : IsQuadratic (normalRepresentation U) (A ⊓ R₂) :=
    fun a ha b hb v => hquad a ha.1 b hb.1 v
  have ha : (0 : ℝ) < Nat.log 2 (R₂.relIndex A) := by
    exact_mod_cast quotient_rank_pos A R₂ hAR
  have hb := generator_rank_bound U (A ⊓ R₂) W 2 n (by simp) hgen hqB hgenRatio
  rw [actionKernel_quotient_rank] at hb
  norm_num only [ENNReal.toReal_ofNat] at hb
  have hm : (fixedCodim (normalRepresentation U) (A ⊓ R₂) : ℝ) ≤
      fixedCodim (normalRepresentation U) A := by
    exact_mod_cast fixedCodim_mono U (inf_le_left : A ⊓ R₂ ≤ A)
  obtain ⟨hec, hab, hxa, hyx⟩ := qrc_rank_equality ha (by exact_mod_cast hc)
    (maxElementary_rank_upper U S A R₂ hUS hA hkernel) hb hm
    (chief_rank_lower U s A R₂ hquad hfactor hfactorRatio)
  refine ⟨by exact_mod_cast hec, by exact_mod_cast hxa.symm, ?_, ?_, ?_, ?_⟩
  · have he : (fixedCodim (normalRepresentation U) A : ℝ) =
        2 * (Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ R₂)) : ℝ) := by
      rw [hxa, hab]
    exact_mod_cast he
  · apply centralizers_eq_of_fixedSpaces_eq U A (A ⊓ R₂)
    apply Submodule.eq_of_le_of_finrank_eq
      (normal_fixedSpace_antitone U (inf_le_left : A ⊓ R₂ ≤ A))
    have hd : fixedCodim (normalRepresentation U) (A ⊓ R₂) =
        fixedCodim (normalRepresentation U) A := by exact_mod_cast hyx
    have ha' := fixedCodim_add_finrank (normalRepresentation U) A
    have hb' := fixedCodim_add_finrank (normalRepresentation U) (A ⊓ R₂)
    omega
  · have hf := qrc_chief_factor_equality U s A (Nat.log 2 (R₂.relIndex A))
      (fun i hi => by
        exact_mod_cast (chiefFactor_rank_lower U s A R₂ hquad i
          (hfactor i hi) (hfactorRatio i hi))) (by rw [hec]; exact hxa)
    intro i hi
    exact_mod_cast (hf i hi).symm

  · intro hn
    have heq : (fixedCodim (normalRepresentation U) (A ⊓ R₂) : ℝ) =
        (2 : ℝ≥0∞).toReal * (Nat.log 2 (Nat.card
          ((A ⊓ R₂ : Subgroup H) ⧸ qrcActionKernel U (A ⊓ R₂))) : ℝ) := by
      rw [actionKernel_quotient_rank, hyx, hxa, hab]
      norm_num
    simpa using generator_first_equality U (A ⊓ R₂) W 2 n (by simp) hn
      hgen hqB hgenRatio heq

end CFSG.Quasithin.ChapterD.MultipleFactors
