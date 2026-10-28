module

public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.PointRigidity
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.RadicalOrientation.Basic

/-!
# Pointwise Sylow stabilizers in binary linear groups

In dimensions four and five, every automorphism fixing a Sylow two-subgroup
pointwise is inner, with a conjugating element in that Sylow subgroup.
A nonzero Sylow-fixed vector gives a point radical contained in the Sylow
subgroup. Fixing that radical preserves the entire conjugacy class of point
radicals, so point-radical rigidity gives innerness. Self-centralization of
the radical places the conjugating element back in the Sylow subgroup.
If the automorphism is nonidentity, this element is a transvection.

This proves the binary higher-linear cases of Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 16.1.6, printed p.1172.
It applies to every automorphism, including arbitrary two-power orders.
-/

public section

namespace BinaryLinear.OuterCyclic
open Subgroup

/-- Pointwise fixation of a Sylow subgroup forces innerness, retaining the
conjugating element in that Sylow subgroup. -/
theorem sylow_fixing_inner {n : ℕ} (hn : n = 4 ∨ n = 5)
    (P : Sylow 2 (LinearGroup n)) (a : MulAut (LinearGroup n))
    (ha : ∀ x ∈ P, a x = x) : ∃ x ∈ P, a = MulAut.conj x := by
  have hV : 2 ∣ Nat.card (Space n) := by
    simp only [Space, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fixedSpace_ne_bot hV P.isPGroup')
  let W := Submodule.span (ZMod 2) {w}
  have hW0 : W ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw0
  have hWt : W ≠ ⊤ := by
    intro he
    have hf : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hw0
    rw [he, finrank_top] at hf
    have hn1 : n = 1 := by simpa [Space] using hf
    omega
  have hPP : (P : Subgroup (LinearGroup n)) ≤ parabolic W := by
    intro x hx v
    constructor
    · intro hv
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hv
      have he : c • w = v := by
        apply x.injective
        simpa only [map_smul, show x w = w from hw x hx] using hc
      exact Submodule.mem_span_singleton.mpr ⟨c, he⟩
    · intro hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, show x w = w from hw x hx]
      exact Submodule.smul_mem W c (Submodule.mem_span_singleton_self w)
  have hRP : radical W ≤ (P : Subgroup (LinearGroup n)) := by
    have he := P.is_maximal' (P.isPGroup'.to_sup_of_normal_right' (radical_two W)
      (hPP.trans (parabolic_le_normalizer W))) le_sup_left
    exact he ▸ le_sup_right
  have hmap : (pointRadical n w).map a.toMonoidHom = pointRadical n w := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      change a y ∈ pointRadical n w
      rwa [ha y (hRP hy)]
    · intro x hx
      exact ⟨x, hx, ha x (hRP hx)⟩
  obtain ⟨g, hg⟩ := eq_conj_of_preservesPointRadicals hn a
    (preservesPointRadicals_of_one a hw0 hw0 hmap)
  refine ⟨g, hRP (centralizer_radical_le hW0 hWt ?_), hg⟩
  apply mem_centralizer_iff.mpr
  intro x hx
  have he := ha x (hRP hx)
  rw [hg] at he
  change g * x * g⁻¹ = x at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Every nonidentity pointwise Sylow stabilizer is conjugation by a
transvection, the long-root involution of this linear model. -/
theorem sylow_fixing_ne_one_transvection {n : ℕ} (hn : n = 4 ∨ n = 5)
    (P : Sylow 2 (LinearGroup n)) (a : MulAut (LinearGroup n))
    (ha : ∀ x ∈ P, a x = x) (ha1 : a ≠ 1) :
    ∃ g ∈ P, a = MulAut.conj g ∧ IsTransvection g := by
  obtain ⟨g, hgP, hg⟩ := sylow_fixing_inner hn P a ha
  have hg1 : g ≠ 1 := by
    intro he
    apply ha1
    simpa only [he, map_one] using hg
  have hc : ∀ x ∈ P, x * g = g * x := by
    intro x hx
    have he := ha x hx
    rw [hg] at he
    change g * x * g⁻¹ = x at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hV : 2 ∣ Nat.card (Space n) := by
    simp only [Space, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    exact dvd_pow_self 2 (by omega)
  obtain ⟨w, f, hw, hf, hfw, he⟩ := central_sylow_eq_transvection hV
    (by simpa [Space] using (show 1 < n by omega)) P hg1 hc
  exact ⟨g, hgP, hg, w, f, hw, hf, hfw, LinearEquiv.ext he⟩

end BinaryLinear.OuterCyclic
