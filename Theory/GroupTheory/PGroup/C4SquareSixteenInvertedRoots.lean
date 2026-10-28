module

public import Theory.GroupAction.C4SquareSixteenInverted
public import Theory.GroupTheory.PGroup.NormalFourCentralAction

/-!
# Inverted roots in C₄-square extensions with action of order sixteen

Let D be a normal abelian self-centralizing C₄-square with normal omega four
W, and suppose there are no normal elementary eights. Every involution
outside D which centralizes W inverts an element of order four in D, when
the conjugation image has order sixteen.

The action contains a central transvection a. A lift t has square s in D.
If s were binary, the surjective norm of a would correct t to an involution;
the normal-four central-action obstruction forbids this. An involution b
with only binary inverted elements inverts its displacement on t, so that
displacement is binary. Consequently b fixes s. The finite action
certificate forces b to act by a, and the same obstruction finishes.

This is the inverted-element step of Janko–Thompson, Math. Z. 113 (1970),
1.4(c), printed p.386. No splitting or ambient classification is assumed.
-/

open Subgroup
namespace C4SquareExtension

/-- In an order-sixteen faithful action, each outside involution centralizing
the omega four inverts a nonbinary base element. -/
public theorem exists_inverted_root_of_action_card_sixteen
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W D : Subgroup P) [W.Normal] [IsElementaryAbelian 2 W]
    [D.Normal] [IsMulCommutative D]
    (hW : Nat.card W = 4)
    (hDC : centralizer (D : Set P) ≤ D)
    (hO : (omega₁ D (p := 2)).map D.subtype = W)
    (e : D ≃* Model)
    (hc : Nat.card (MulAut.conjNormal : P →* MulAut D).range = 16)
    (b : P) (hb : b ^ 2 = 1) (hbD : b ∉ D)
    (hbW : b ∈ centralizer (W : Set P)) :
    ∃ d ∈ D, b * d * b⁻¹ = d⁻¹ ∧ d ^ 2 ≠ 1 := by
  by_contra! hbad
  let F : P →* MulAut Model :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : P →* MulAut D)
  let τ : Model →* P := D.subtype.comp e.symm.toMonoidHom
  have hτ : Function.Injective τ := D.subtype_injective.comp e.symm.injective
  have hker : F.ker = D := by
    rw [show F = (MulAut.congr e).toMonoidHom.comp
      (MulAut.conjNormal : P →* MulAut D) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
      conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  have hact (g : P) (v : Model) : τ (F g v) = g * τ v * g⁻¹ := by
    change (e.symm (e (MulAut.conjNormal g (e.symm v))) : P) = g * τ v * g⁻¹
    rw [e.symm_apply_apply]
    rfl
  have hFc : Nat.card F.range = 16 := by
    rw [MonoidHom.range_comp, card_map_of_injective (MulAut.congr e).injective]
    exact hc
  obtain ⟨a, ha, hane, ha2, hafix, hacent, hainv, hanorm, hadetect⟩ :=
    SixteenInverted.exists_central_action F.range (IsPGroup.of_card (n := 4) hFc) hFc
  obtain ⟨t, ht⟩ := ha
  have htD : t ^ 2 ∈ D := by
    rw [← hker, MonoidHom.mem_ker, map_pow, ht, ha2]
  let s := e (⟨t ^ 2, htD⟩ : D)
  have hs : τ s = t ^ 2 := by
    change (e.symm (e (⟨t ^ 2, htD⟩ : D)) : P) = t ^ 2
    rw [e.symm_apply_apply]
  have has : a s = s := by
    apply hτ
    rw [← ht, hact, hs]
    simp only [pow_two]
    group
  have forbid (x : P) (hx : x ^ 2 = 1) (hxa : F x = a) : False := by
    apply hno
    apply exists_normal_eight_of_involution_central_action W D hW hDC hO x hx
    · intro hxD
      exact hane (hxa.symm.trans (MonoidHom.mem_ker.mp (hker ▸ hxD)))
    · intro w hw
      have hwD : w ∈ D := map_subtype_le _ (hO ▸ hw)
      let w' : D := ⟨w, hwD⟩
      have hw2 : w' ^ 2 = 1 :=
        Subtype.ext (elemPow_eq_one_of_isElementaryAbelian w hw)
      have hfix : F x (e w') = e w' := by
        rw [hxa]
        exact hafix _ (by rw [← map_pow, hw2, map_one])
      have he := congrArg τ hfix
      rw [hact] at he
      have hwτ : τ (e w') = w := by
        change (e.symm (e w') : P) = w
        rw [e.symm_apply_apply]
      rw [hwτ] at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro g
      apply Commute.of_map (MulAut.congr e).injective
      change Commute (F g) (F x)
      rw [hxa]
      exact hacent _ ⟨g, rfl⟩
    · intro d hd hdi
      let d' : D := ⟨d, hd⟩
      have he : a (e d') = (e d')⁻¹ := by
        apply hτ
        rw [← hxa, hact, map_inv]
        have hdτ : τ (e d') = d := by
          change (e.symm (e d') : P) = d
          rw [e.symm_apply_apply]
        rwa [hdτ]
      have hd2 := hainv (e d') he
      have hd' : d' ^ 2 = 1 := e.injective (by simpa only [map_pow, map_one] using hd2)
      exact congrArg Subtype.val hd'
  have hsne : s ^ 2 ≠ 1 := by
    intro hs2
    obtain ⟨v, hv⟩ := hanorm s⁻¹ (by rw [inv_pow, hs2, inv_one])
    apply forbid (τ v * t)
    · calc
        (τ v * t) ^ 2 = τ (v * a v * s) := by
          rw [map_mul, map_mul, ← ht, hact, hs]
          simp only [pow_two]
          group
        _ = 1 := by rw [hv, inv_mul_cancel, map_one]
    · have hvD : τ v ∈ D := (e.symm v).property
      rw [map_mul, MonoidHom.mem_ker.mp (hker ▸ hvD), one_mul, ht]
  let d := b * t * b⁻¹ * t⁻¹
  have hdD : d ∈ D := by
    rw [← hker, MonoidHom.mem_ker]
    dsimp [d]
    simp only [map_mul, map_inv, ht]
    rw [(hacent _ ⟨b, rfl⟩).eq]
    group
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hb)
  have hdi : b * d * b⁻¹ = d⁻¹ := by
    dsimp [d]
    simp only [mul_inv_rev, inv_inv, hbi]
    have hbb : b * b = 1 := by simpa only [pow_two] using hb
    simp only [← mul_assoc, hbb, one_mul]
  have hd2 : d ^ 2 = 1 := hbad d hdD hdi
  let r := e (⟨d, hdD⟩ : D)
  have hr : τ r = d := by
    change (e.symm (e (⟨d, hdD⟩ : D)) : P) = d
    rw [e.symm_apply_apply]
  have hr2 : r ^ 2 = 1 := by
    apply hτ
    rw [map_pow, hr, hd2, map_one]
  have htr : t * d * t⁻¹ = d := by
    rw [← hr, ← hact, ht, hafix r hr2]
  have hbs : F b s = s := by
    apply hτ
    rw [hact, hs]
    calc
      b * t ^ 2 * b⁻¹ = (d * t) ^ 2 := by
        dsimp [d]
        simp only [pow_two]
        group
      _ = d * (t * d * t⁻¹) * t ^ 2 := by
        simp only [pow_two]
        group
      _ = t ^ 2 := by rw [htr, ← pow_two, hd2, one_mul]
  have hfbne : F b ≠ 1 := by
    intro h
    exact hbD (hker ▸ MonoidHom.mem_ker.mpr h)
  have hfbfix (v : Model) (hv : v ^ 2 = 1) : F b v = v := by
    have hvW : τ v ∈ W := by
      rw [← hO]
      refine ⟨e.symm v, subset_closure ?_, rfl⟩
      change (e.symm v) ^ (2 ^ 1) = 1
      simp only [pow_one, ← map_pow, hv, map_one]
    apply hτ
    rw [hact, ← hbW _ hvW, mul_inv_cancel_right]
  have hfbinv (v : Model) (hv : F b v = v⁻¹) : v ^ 2 = 1 := by
    have he : b * τ v * b⁻¹ = (τ v)⁻¹ := by
      rw [← hact, hv, map_inv]
    have hh := hbad (τ v) (e.symm v).property he
    apply hτ
    simpa only [map_pow, map_one] using hh
  exact forbid b hb (hadetect (F b) hfbne hfbfix hfbinv s hsne has hbs)

end C4SquareExtension
