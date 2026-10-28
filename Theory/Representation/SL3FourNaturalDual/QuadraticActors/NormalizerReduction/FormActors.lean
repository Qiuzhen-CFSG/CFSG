module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.Model
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction.OuterDisplacements
public import Theory.Representation.BinaryOffender.Basic

/-!
# Quadratic offenders among explicit normalizer forms

An outer quadratic actor forces the whole actor subgroup to have order at
most two. For an exchanging actor, quadraticity makes the summand-permutation
choice injective: the difference of two operators with the same permutation
has single-summand images, which the exchanging actor cannot fix. For a
nontrivial field twist, the difference of two operators with the same twist
has an F₄-stable image, which the outer actor cannot fix. The two field
automorphisms are counted explicitly by their values on a generator of F₄.

An exchanging operator has fixed dimension at most six by projection to a
summand. A nontrivial field twist has the same bound by injecting its fixed
space into its quotient using scalar multiplication. These bounds contradict
the offender inequality. Finally, a preserving untwisted involution has
matrix determinant one and dual scalar one, so lies in the specified component.

This proves the conditional operator calculation used in Aschbacher--Smith,
proof of 13.8.20, printed p.955 (PDF p.972), combined manuscript of 1 March
2004. Normalizer coverage by `HasStandardForm` remains the caller's premise.
-/

public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
open BinaryOffender

local instance : Finite (F ≃+* F) :=
  Finite.of_injective (fun σ : F ≃+* F => (σ : F → F)) DFunLike.coe_injective

-- A preserving form maps both coordinate summands into themselves.
private def Preserves (f : BinaryGL) : Prop :=
  (∀ w : W, (f (w, 0)).2 = 0) ∧ (∀ w : W, (f (0, w)).1 = 0)

private def Exchanges (f : BinaryGL) : Prop :=
  (∀ w : W, (f (w, 0)).1 = 0) ∧ (∀ w : W, (f (0, w)).2 = 0)

private def Semilinear (f : BinaryGL) (σ : F ≃+* F) : Prop :=
  ∀ (a : F) (v : V), f (a • v) = σ a • f v

private lemma standardPair_smul (M : Matrix.GeneralLinearGroup (Fin 3) F)
    (c : Fˣ) (σ : F ≃+* F) (a : F) (v : V) :
    standardPair M c σ (a • v) = σ a • standardPair M c σ v := by
  have hm (w : W) : σ ∘ (a • w) = σ a • (σ ∘ w) := by
    funext i
    exact map_mul σ a (w i)
  simp only [standardPair, Prod.smul_fst, Prod.smul_snd, hm, Matrix.mulVec_smul,
    Prod.smul_mk]
  rw [smul_comm (c : F) (σ a)]

private lemma form_properties {f : BinaryGL} (hf : HasStandardForm f) :
    ∃ σ, Semilinear f σ ∧ (Preserves f ∨ Exchanges f) := by
  obtain ⟨M, c, σ, hp | he⟩ := hf
  · refine ⟨σ, ?_, Or.inl ?_⟩
    · intro a v
      rw [hp, hp, standardPair_smul]
    · constructor <;> intro w <;> simp [hp, standardPair, Function.comp_def, ← Pi.zero_def]
  · refine ⟨σ, ?_, Or.inr ?_⟩
    · intro a v
      rw [he, he]
      exact standardPair_smul M c σ a (v.2, v.1)
    · constructor <;> intro w <;> simp [he, standardPair, Function.comp_def, ← Pi.zero_def]

private lemma exchange_fixed_single {f : BinaryGL} (hf : Exchanges f) {v : V}
    (hv : f v = v) (hz : v.1 = 0 ∨ v.2 = 0) : v = 0 := by
  rcases v with ⟨x,y⟩
  rcases hz with hx | hy
  · change x = 0 at hx
    subst x
    have h := congrArg Prod.snd hv
    rw [hf.2] at h
    exact Prod.ext rfl h.symm
  · change y = 0 at hy
    subst y
    have h := congrArg Prod.fst hv
    rw [hf.1] at h
    exact Prod.ext h.symm rfl

private lemma quadratic_fixes_difference (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B) {f b d : BinaryGL}
    (hf : f ∈ B) (hb : b ∈ B) (hd : d ∈ B) (v : V) :
    f (b v - d v) = b v - d v := by
  have h₁ : f (b v - v) = b v - v := hq f hf b hb v
  have h₂ : f (d v - v) = d v - v := hq f hf d hd v
  have he : b v - d v = (b v - v) - (d v - v) := by abel
  rw [he, map_sub, h₁, h₂]

private lemma exchange_same_shape_eq (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B) {f b d : BinaryGL}
    (hf : f ∈ B) (hb : b ∈ B) (hd : d ∈ B) (he : Exchanges f)
    (hs : (Preserves b ∧ Preserves d) ∨ (Exchanges b ∧ Exchanges d)) : b = d := by
  have hw (w : W) : b (w, 0) = d (w, 0) := by
    apply sub_eq_zero.mp
    apply exchange_fixed_single he (quadratic_fixes_difference B hq hf hb hd _)
    rcases hs with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · right; simp only [Prod.snd_sub, h₁.1, h₂.1, sub_self]
    · left; simp only [Prod.fst_sub, h₁.1, h₂.1, sub_self]
  have hw' (w : W) : b (0, w) = d (0, w) := by
    apply sub_eq_zero.mp
    apply exchange_fixed_single he (quadratic_fixes_difference B hq hf hb hd _)
    rcases hs with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · left; simp only [Prod.fst_sub, h₁.2, h₂.2, sub_self]
    · right; simp only [Prod.snd_sub, h₁.2, h₂.2, sub_self]
  apply LinearEquiv.ext
  rintro ⟨x,y⟩
  have heq : (x,y) = (x,0) + (0,y) := by simp
  rw [heq, map_add, map_add, hw, hw']

private lemma card_le_two_of_exchange (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B)
    (hshape : ∀ b ∈ B, Preserves b ∨ Exchanges b)
    {f : BinaryGL} (hf : f ∈ B) (he : Exchanges f) : Nat.card B ≤ 2 := by
  classical
  let key : B → Bool := fun b => decide (Preserves (b : BinaryGL))
  have hi : Function.Injective key := by
    intro b d hbd
    have hp : Preserves (b : BinaryGL) ↔ Preserves (d : BinaryGL) := by
      simpa only [key, decide_eq_decide] using hbd
    apply Subtype.ext
    apply exchange_same_shape_eq B hq hf b.property d.property he
    by_cases hb : Preserves (b : BinaryGL)
    · exact Or.inl ⟨hb, hp.mp hb⟩
    · exact Or.inr ⟨(hshape b b.property).resolve_left hb,
        (hshape d d.property).resolve_left (fun hd => hb (hp.mpr hd))⟩
  simpa using Nat.card_le_card_of_injective key hi

private lemma field_cases (a : F) : a = 0 ∨ a = 1 ∨ a = omega ∨ a = 1 + omega := by
  revert a
  decide +kernel

private lemma field_aut_ext {σ τ : F ≃+* F} (h : σ omega = τ omega) : σ = τ := by
  apply RingEquiv.ext
  intro a
  rcases field_cases a with rfl | rfl | rfl | rfl <;> simp [h]

private lemma field_aut_card : Nat.card (F ≃+* F) ≤ 2 := by
  classical
  let key : (F ≃+* F) → Bool := fun σ => decide (σ omega = omega)
  have himage (σ : F ≃+* F) : σ omega = omega ∨ σ omega = 1 + omega := by
    rcases field_cases (σ omega) with hz | ho | h | h
    · exact False.elim (omega_ne_zero (σ.injective (hz.trans (map_zero σ).symm)))
    · exact False.elim (omega_ne_one (σ.injective (ho.trans (map_one σ).symm)))
    · exact Or.inl h
    · exact Or.inr h
  have hi : Function.Injective key := by
    intro σ τ he
    have hp : σ omega = omega ↔ τ omega = omega := by
      simpa only [key, decide_eq_decide] using he
    apply field_aut_ext
    by_cases hσ : σ omega = omega
    · exact hσ.trans (hp.mp hσ).symm
    · exact ((himage σ).resolve_left hσ).trans
        ((himage τ).resolve_left (fun hτ => hσ (hp.mpr hτ))).symm
  simpa using Nat.card_le_card_of_injective key hi

private lemma field_same_twist_eq (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B) {f b d : BinaryGL}
    (hf : f ∈ B) (hb : b ∈ B) (hd : d ∈ B)
    {σ τ : F ≃+* F} (hσ : σ ≠ RingEquiv.refl F)
    (hfsemi : Semilinear f σ) (hbsemi : Semilinear b τ) (hdsemi : Semilinear d τ) :
    b = d := by
  obtain ⟨a, ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  apply LinearEquiv.ext
  intro v
  have hfix := quadratic_fixes_difference B hq hf hb hd v
  have h := quadratic_fixes_difference B hq hf hb hd ((τ.symm a) • v)
  rw [hbsemi, hdsemi, τ.apply_symm_apply, ← smul_sub, hfsemi, hfix] at h
  have hz : (σ a - a) • (b v - d v) = 0 := by rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha))

private lemma card_le_two_of_field (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B)
    (hsemi : ∀ b ∈ B, ∃ τ, Semilinear b τ)
    {f : BinaryGL} (hf : f ∈ B) {σ : F ≃+* F}
    (hσ : σ ≠ RingEquiv.refl F) (hfsemi : Semilinear f σ) : Nat.card B ≤ 2 := by
  classical
  choose key hk using fun b : B => hsemi b b.property
  have hi : Function.Injective key := by
    intro b d he
    apply Subtype.ext
    apply field_same_twist_eq B hq hf b.property d.property hσ hfsemi (hk b)
    rw [he]
    exact hk d
  exact (Nat.card_le_card_of_injective key hi).trans field_aut_card


private lemma exchange_fixed_finrank_le (f : BinaryGL) (he : Exchanges f)
    (D : Submodule (ZMod 2) V) (hfix : ∀ v ∈ D, f v = v) :
    Module.finrank (ZMod 2) D ≤ 6 := by
  let p : D →ₗ[ZMod 2] W := (LinearMap.fst (ZMod 2) W W).comp D.subtype
  have hi : Function.Injective p := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply exchange_fixed_single he
    · rw [map_sub, hfix x x.property, hfix y y.property]
    · exact Or.inl (sub_eq_zero.mpr hxy)
  simpa only [finrank_natural] using LinearMap.finrank_le_finrank_of_injective hi

private lemma field_fixed_finrank_le (f : BinaryGL) {σ : F ≃+* F}
    (hσ : σ ≠ RingEquiv.refl F) (hsemi : Semilinear f σ)
    (D : Submodule (ZMod 2) V) (hfix : ∀ v ∈ D, f v = v) :
    Module.finrank (ZMod 2) D ≤ 6 := by
  obtain ⟨a, ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra! h
    exact hσ (RingEquiv.ext h)
  let p : D →ₗ[ZMod 2] (V ⧸ D) := D.mkQ.comp
    (((LinearMap.lsmul F V a).restrictScalars (ZMod 2)).comp D.subtype)
  have hi : Function.Injective p := by
    apply (injective_iff_map_eq_zero p).mpr
    intro x hx
    have hax : a • (x : V) ∈ D := (Submodule.Quotient.mk_eq_zero D).mp hx
    have h := hfix _ hax
    rw [hsemi, hfix x x.property] at h
    have hz : (σ a - a) • (x : V) = 0 := by rw [sub_smul, h, sub_self]
    apply Subtype.ext
    exact (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr ha)
  have hd := LinearMap.finrank_le_finrank_of_injective hi
  have ht := D.finrank_quotient_add_finrank
  rw [finrank_space] at ht
  omega

private lemma rank_le_one_of_card_le_two (B : Subgroup BinaryGL) (hB : Nat.card B ≤ 2) :
    rank B ≤ 1 := by
  change Nat.log 2 (Nat.card B) ≤ 1
  exact (Nat.log_mono_right hB).trans (by decide)

private lemma square_one (a : F) (ha : a * a = 1) : a = 1 := by
  revert a
  decide +kernel

/-- An involutory standard form with no field twist and no exchange belongs
 to the actual determinant-one natural-plus-dual component. The independent
 dual scalar is forced to be one. -/
theorem untwisted_involution_mem_component (f : BinaryGL)
    (M : Matrix.GeneralLinearGroup (Fin 3) F) (c : Fˣ)
    (hp : ∀ v, f v = standardPair M c (RingEquiv.refl F) v)
    (h2 : f * f = 1) : f ∈ component := by
  have hff (v : V) : f (f v) = v := LinearEquiv.congr_fun h2 v
  have hM2 : M.val * M.val = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro w
    have h := congrArg Prod.fst (hff (w, 0))
    simpa only [hp, standardPair, RingEquiv.refl_apply, Function.comp_def,
      Matrix.mulVec_mulVec, Matrix.one_mulVec] using h
  have hMi : M⁻¹ = M := inv_eq_of_mul_eq_one_right (Units.ext hM2)
  have hN2 : (M⁻¹).val.transpose * (M⁻¹).val.transpose = 1 := by
    rw [hMi, ← Matrix.transpose_mul, hM2, Matrix.transpose_one]
  have hc2 : (c : F) * c = 1 := by
    have h := congrArg (fun v : V => v.2 0) (hff (0, fun _ => 1))
    simp only [hp] at h
    change ((c : F) • (M⁻¹).val.transpose.mulVec
      ((c : F) • (M⁻¹).val.transpose.mulVec (fun _ => 1))) 0 = 1 at h
    simpa only [Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec, hN2,
      Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, mul_one] using h
  have hc : (c : F) = 1 := square_one _ hc2
  have hdet : M.val.det = 1 := by
    apply square_one
    rw [← Matrix.det_mul, hM2, Matrix.det_one]
  let g : SL := ⟨M.val, hdet⟩
  have hgi : g⁻¹ = g := by
    apply inv_eq_of_mul_eq_one_right
    apply Subtype.ext
    exact hM2
  refine ⟨g, ?_⟩
  apply LinearEquiv.ext
  intro v
  rw [linearAction_apply, representation_apply, hgi, hp]
  simp only [standardPair, RingEquiv.refl_apply, Function.comp_def, hc, one_smul, hMi]
  rfl


private lemma no_exchange_of_offender (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B)
    (hshape : ∀ b ∈ B, Preserves b ∨ Exchanges b)
    (hoff : fixedCodim binaryRepresentation B ≤ 2 * rank B)
    {f : BinaryGL} (hf : f ∈ B) : ¬ Exchanges f := by
  intro he
  have hr := rank_le_one_of_card_le_two B (card_le_two_of_exchange B hq hshape hf he)
  have hd := exchange_fixed_finrank_le f he (fixedSpace binaryRepresentation B)
    (fun v hv => hv ⟨f, hf⟩)
  have ht := fixedCodim_add_finrank binaryRepresentation B
  rw [finrank_space] at ht
  omega

private lemma no_field_of_offender (B : Subgroup BinaryGL)
    (hq : IsQuadratic binaryRepresentation B)
    (hsemi : ∀ b ∈ B, ∃ τ, Semilinear b τ)
    (hoff : fixedCodim binaryRepresentation B ≤ 2 * rank B)
    {f : BinaryGL} (hf : f ∈ B) {σ : F ≃+* F} (hs : Semilinear f σ) :
    σ = RingEquiv.refl F := by
  by_contra hσ
  have hr := rank_le_one_of_card_le_two B (card_le_two_of_field B hq hsemi hf hσ hs)
  have hd := field_fixed_finrank_le f hσ hs (fixedSpace binaryRepresentation B)
    (fun v hv => hv ⟨f, hf⟩)
  have ht := fixedCodim_add_finrank binaryRepresentation B
  rw [finrank_space] at ht
  omega

/-- Every elementary quadratic offender among the explicit standard forms
 belongs to the component. No bound on the actor rank is needed. Coverage of
 the ambient normalizer by these forms is a separate premise. -/
theorem le_component_of_hasStandardForm (B : Subgroup BinaryGL)
    (hform : ∀ b ∈ B, HasStandardForm b)
    (hB : IsElementaryTwo B) (hq : IsQuadratic binaryRepresentation B)
    (hoff : fixedCodim binaryRepresentation B ≤ 2 * rank B) : B ≤ component := by
  have hshape : ∀ b ∈ B, Preserves b ∨ Exchanges b := by
    intro b hb
    obtain ⟨σ, hs, he⟩ := form_properties (hform b hb)
    exact he
  have hsemi : ∀ b ∈ B, ∃ τ, Semilinear b τ := by
    intro b hb
    obtain ⟨σ, hs, he⟩ := form_properties (hform b hb)
    exact ⟨σ, hs⟩
  intro f hf
  obtain ⟨M, c, σ, hp | he⟩ := hform f hf
  · have hs : Semilinear f σ := by
      intro a v
      rw [hp, hp, standardPair_smul]
    have hσ := no_field_of_offender B hq hsemi hoff hf hs
    subst σ
    apply untwisted_involution_mem_component f M c hp
    let : IsElementaryAbelian 2 B := hB.2
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2) f hf
  · exfalso
    apply no_exchange_of_offender B hq hshape hoff hf
    constructor <;> intro w <;>
      simp [he, standardPair, Function.comp_def, ← Pi.zero_def]

end Representation.SL3FourNaturalDual.QuadraticActors.NormalizerReduction
