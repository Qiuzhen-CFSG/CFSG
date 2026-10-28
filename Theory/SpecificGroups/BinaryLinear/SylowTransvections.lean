module

public import Theory.SpecificGroups.BinaryLinear.Parabolics
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Central elements of binary Sylow subgroups are transvections

A Sylow two-subgroup fixes a nonzero vector. It normalizes the radical of
that vector's line, so Sylow maximality places the radical inside the Sylow
subgroup. The radical is self-centralizing. Every nonidentity element of the
Sylow centralizer therefore acts by a rank-one transvection along this line.

This is the actual linear-action calculation used for the binary components
in Aschbacher–Smith 2.3.9(7), printed pp.525–526. It needs neither the order
of the linear group nor a classification of its automorphisms.
-/

@[expose] public section

open Subgroup
namespace BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem exists_transvection_of_mem_line_radical {w : V} (hw : w ≠ 0)
    {t : BinaryLinear.GL V} (ht : t ∈ radical (Submodule.span (ZMod 2) {w})) (ht1 : t ≠ 1) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, f ≠ 0 ∧ f w = 0 ∧
      ∀ v, t v = v + f v • w := by
  let d : V →ₗ[ZMod 2] Submodule.span (ZMod 2) {w} :=
    (t.toLinearMap - LinearMap.id).codRestrict _ ht.2
  let f : V →ₗ[ZMod 2] ZMod 2 :=
    (LinearEquiv.coord (ZMod 2) V w hw).toLinearMap.comp d
  have hf (v : V) : f v • w = t v - v :=
    LinearEquiv.coord_apply_smul (ZMod 2) V w hw (d v)
  refine ⟨f, ?_, ?_, ?_⟩
  · intro hf0
    apply ht1
    ext v
    have he := hf v
    rw [hf0, LinearMap.zero_apply, zero_smul] at he
    exact sub_eq_zero.mp he.symm
  · have hd : d w = 0 := by
      apply Subtype.ext
      change t w - w = 0
      rw [ht.1 w (Submodule.mem_span_singleton_self w), sub_self]
    change (LinearEquiv.coord (ZMod 2) V w hw) (d w) = 0
    rw [hd, map_zero]
  · intro v
    rw [hf]
    abel

theorem central_sylow_eq_transvection [Finite V]
    (hV : 2 ∣ Nat.card V) (hdim : 1 < Module.finrank (ZMod 2) V)
    (T : Sylow 2 (BinaryLinear.GL V)) {t : BinaryLinear.GL V} (ht1 : t ≠ 1)
    (hc : ∀ x : BinaryLinear.GL V, x ∈ T → x * t = t * x) :
    ∃ w : V, ∃ f : V →ₗ[ZMod 2] ZMod 2,
      w ≠ 0 ∧ f ≠ 0 ∧ f w = 0 ∧ ∀ v, t v = v + f v • w := by
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (fixedSpace_ne_bot hV T.isPGroup')
  let W := Submodule.span (ZMod 2) {w}
  have hW0 : W ≠ ⊥ := mt Submodule.span_singleton_eq_bot.mp hw0
  have hWt : W ≠ ⊤ := by
    intro he
    have hf : Module.finrank (ZMod 2) W = 1 := finrank_span_singleton hw0
    rw [he, finrank_top] at hf
    omega
  have hTP : (T : Subgroup (BinaryLinear.GL V)) ≤ parabolic W := by
    intro x hx v
    constructor
    · intro hv
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hv
      have he : a • w = v := by
        apply x.injective
        simpa only [map_smul, show x w = w from hw x hx] using ha
      exact Submodule.mem_span_singleton.mpr ⟨a, he⟩
    · intro hv
      obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
      rw [map_smul, show x w = w from hw x hx]
      exact Submodule.smul_mem W a (Submodule.mem_span_singleton_self w)
  have hRT : radical W ≤ (T : Subgroup (BinaryLinear.GL V)) := by
    have he := T.is_maximal' (T.isPGroup'.to_sup_of_normal_right' (radical_two W)
      (hTP.trans (parabolic_le_normalizer W))) le_sup_left
    exact he ▸ le_sup_right
  have htR : t ∈ radical W := centralizer_radical_le hW0 hWt
    (mem_centralizer_iff.mpr (fun x hx => hc x (hRT hx)))
  obtain ⟨f, hf0, hfw, hf⟩ := exists_transvection_of_mem_line_radical hw0 htR ht1
  exact ⟨w, f, hw0, hf0, hfw, hf⟩
end BinaryLinear

end
