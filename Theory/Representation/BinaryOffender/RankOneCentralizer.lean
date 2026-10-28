module

public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# A commuting actor fixes a binary transvection line

Commutation preserves the one-dimensional displacement space. Its unique
nonzero vector is fixed by every invertible binary linear map preserving it.
This is the elementary faithful-centralizer step in the transvection source
argument, Aschbacher–Smith G.6.4, pp.345–346.
-/

public section
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem fixes_displacement_of_commute_rank_one (ρ : Representation (ZMod 2) G V)
    (a b : G) (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hab : Commute a b) (v : V) : ρ b (ρ a v - v) = ρ a v - v := by
  let w := ρ a v - v
  by_cases hw : w = 0
  · change ρ b w = w
    rw [hw, map_zero]
  have hm : w ∈ LinearMap.range (ρ a - LinearMap.id) := ⟨v, rfl⟩
  have hb : ρ b w ∈ LinearMap.range (ρ a - LinearMap.id) := by
    refine ⟨ρ b v, ?_⟩
    change ρ a (ρ b v) - ρ b v = ρ b (ρ a v - v)
    rw [map_sub]
    have he := congrArg (fun g => ρ g v) hab.eq
    simpa only [map_mul, Module.End.mul_apply] using congrArg (fun x => x - ρ b v) he
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hr hm hw
  rw [hspan] at hb
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  have hcne : c ≠ 0 := by
    intro he
    have hz : ρ b w = 0 := by simpa only [he, zero_smul] using hc.symm
    have he' := congrArg (ρ b⁻¹) hz
    apply hw
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply, map_zero] using he'
  have hc1 : c = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) c hcne
  change ρ b w = w
  simpa only [hc1, one_smul] using hc.symm

end Representation.BinaryOffender
