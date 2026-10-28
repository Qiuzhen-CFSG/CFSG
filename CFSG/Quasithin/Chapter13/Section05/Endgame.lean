module

public import CFSG.Quasithin.ChapterG.Section02.AlternatingFive.Assembly.Chapter13
public import CFSG.Quasithin.Chapter13.Section08.SourceDefs

/-!
# Final subgroup obstructions in Section 13.5

The G.2.4 order formulas give |O₂(L⁻)| ≤ 256 whenever |U_H| = 128.
Consequently an L₁ two-core containing U_H cannot have both a star image
of order 32 and the bound |O₂(L₁)| ≤ 4|O₂(L⁻)|. This proves the order
contradiction in 13.5.23 without separately counting chief factors.
The quotient image is taken in the original H/O₂(H).

For 13.5.25 the actual second layer V(U_H ∩ U_H^g) is elementary abelian
by G.2.4. Thus the order-four element supplied by the G₂(2)′ module case
cannot lie in its claimed cubic fixed subgroup.

These are conditional source deductions. The chapter must construct the
G.2.4 configuration and the component-module cardinality/fixed-point
inputs; the universal G.1.3 recognition input remains explicit. No lemma
here asserts the complete source exclusion or Theorem 13.5.12.
Conjugation in the G.2 setup is right conjugation, as in the source.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
13.5.22–25, printed pp.924–925 (PDF pp.941–942).
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem order_bound (s i a : ℕ)
    (hu : 128 = 2 ^ (2 * s + 5) * i)
    (ha : a = 2 ^ (4 * s + 4) * i) : a ≤ 256 := by
  have hi : 1 ≤ i := by
    by_contra hn
    have : i = 0 := by omega
    simp [this] at hu
  have hp : 2 ^ (2 * s + 5) ≤ (2 : ℕ) ^ 7 := by
    calc
      _ ≤ 2 ^ (2 * s + 5) * i := Nat.le_mul_of_pos_right _ hi
      _ = 128 := hu.symm
      _ = _ := by norm_num
  have hs : s ≤ 1 := by
    have := (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hp
    omega
  interval_cases s <;> norm_num at hu ha <;> omega

/-- The G.2.4 order formulas bound the actual core without a chief-factor count. -/
theorem core_card_le_256
    (V₁ V₃ Lminus T H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hU : Nat.card (conjugateSpanBy V₃ H) = 128) :
    Nat.card ((conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g).pCoreIn 2) ≤
      256 := by
  obtain ⟨s, _, _, _, _, hu, hs⟩ := d.source_natural_layer hrec
  change Nat.card (conjugateSpanBy V₃ H) = _ at hu
  rw [hU] at hu
  exact order_bound s _ _ hu hs

private theorem card_mul_starImage_le
    (H P U : Subgroup G) (hPH : P ≤ H) (hUP : U ≤ P)
    (hUQ : U ≤ H.pCoreIn 2) :
    Nat.card U * Nat.card (Section08.Source.starImage H P) ≤ Nat.card P := by
  let f : P →* Section08.Source.Hstar H :=
    (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hPH)
  have hr : f.range = Section08.Source.starImage H P := by
    ext x
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨⟨p.val, hPH p.property⟩, p.property, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p.val, hp⟩, rfl⟩
  have hk : U.subgroupOf P ≤ f.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff (inclusion hPH x)).mpr
    obtain ⟨y, hy, he⟩ := hUQ hx
    have he' : y = inclusion hPH x := Subtype.ext he
    exact he' ▸ hy
  have hu : Nat.card U ≤ Nat.card f.ker := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv]
    exact card_le_of_le hk
  have he := f.ker.card_mul_index
  rw [index_ker, hr] at he
  exact (Nat.mul_le_mul_right _ hu).trans he.le

/-- The order contradiction in 13.5.23, on the literal H/O₂(H) image. -/
theorem a8_order_contradiction
    (V₁ V₃ Lminus T H L₁ : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hrec : RecognitionInput.{0,u} F4)
    (hU : Nat.card (conjugateSpanBy V₃ H) = 128)
    (hL₁H : L₁ ≤ H) (hUL₁ : conjugateSpanBy V₃ H ≤ L₁)
    (hupper : Nat.card (L₁.pCoreIn 2) ≤ 4 *
      Nat.card ((conjugateSpanBy V₃ H ⊔ conjugate (conjugateSpanBy V₃ H) g).pCoreIn 2))
    (himage : Nat.card (Section08.Source.starImage H (L₁.pCoreIn 2)) = 32) : False := by
  have hbound := core_card_le_256 V₁ V₃ Lminus T H g d hrec hU
  have hUQ : conjugateSpanBy V₃ H ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes d.setup.U_isPGroup d.setup.U_le_H
      (le_normalizer_conjugateSpanBy V₃ H)
  have hUP : conjugateSpanBy V₃ H ≤ L₁.pCoreIn 2 :=
    le_pCoreIn_of_normalizes d.setup.U_isPGroup hUL₁
      (hL₁H.trans (le_normalizer_conjugateSpanBy V₃ H))
  have hlow := card_mul_starImage_le H (L₁.pCoreIn 2) (conjugateSpanBy V₃ H)
    ((pCoreIn_le 2 L₁).trans hL₁H) hUP hUQ
  rw [hU, himage] at hlow
  omega

/-- The order-four obstruction in 13.5.25, with the original second layer. -/
theorem order_four_not_mem_second_layer
    (V₁ V₃ V Lminus T H : Subgroup G) (g j : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V) (hj : orderOf j = 4) :
    j ∉ V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g) := by
  let := chapter13_source_second_elementary V₁ V₃ V Lminus T H
    (conjugateSpanBy V₃ H) g d hspan rfl
  intro hjmem
  have hp := orderOf_dvd_of_pow_eq_one
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) j hjmem)
  rw [hj] at hp
  norm_num at hp

/-- The last contradiction in 13.5.25. The fixed-point calculation must
place the actual order-four central element in the second layer. -/
theorem g2_fixed_point_contradiction
    (V₁ V₃ V Lminus T H L₁ X : Subgroup G) (g j : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hspan : conjugateSpanBy V₁ Lminus = V) (hj : orderOf j = 4)
    (hjcore : j ∈ L₁.pCoreIn 2) (hjfixed : j ∈ centralizer (X : Set G))
    (hfixed : L₁.pCoreIn 2 ⊓ centralizer (X : Set G) ≤
      V ⊔ (conjugateSpanBy V₃ H ⊓ conjugate (conjugateSpanBy V₃ H) g)) : False :=
  order_four_not_mem_second_layer V₁ V₃ V Lminus T H g j d hspan hj
    (hfixed ⟨hjcore, hjfixed⟩)

end CFSG.Quasithin.Chapter13.Section05
end
