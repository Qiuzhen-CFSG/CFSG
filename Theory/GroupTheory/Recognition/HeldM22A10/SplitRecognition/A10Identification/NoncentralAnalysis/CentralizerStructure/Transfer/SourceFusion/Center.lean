module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Transfer.SourceFusion.Tables
public import Theory.GroupTheory.SylowCentralizerNonfusion
/-!
# Central fusion in the order-32 Sylow subgroup

The unique nonidentity commutator is fixed by every normalizer element.
Sylow fusion control then excludes all other central elements from its class.

Source: Held, Illinois J. Math. 13 (1969), p.233.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
open TransferModel (Model l z t m)
local notation "p₀" => TransferModel.p
universe u
variable {K : Type u} [Group K]

public theorem normalizer_fixes_p (f : Model →* K) (hf : Function.Injective f)
    (g : K) (hg : g ∈ normalizer (f.range : Set K)) :
    g * f p₀ * g⁻¹ = f p₀ := by
  obtain ⟨a, ha⟩ := (mem_normalizer_iff.mp hg (f t)).mp ⟨t, rfl⟩
  obtain ⟨b, hb⟩ := (mem_normalizer_iff.mp hg (f m)).mp ⟨m, rfl⟩
  have hc : g * f p₀ * g⁻¹ = f (a*b*a⁻¹*b⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb,
      ← Local.p_commutator, map_mul, map_mul, map_mul, map_inv, map_inv]
    group
  rcases Local.commutator_cases a b with h | h
  · rw [h, map_one] at hc
    have htriv : f p₀ = 1 := by
      calc
        _ = g⁻¹ * (g * f p₀ * g⁻¹) * g := by group
        _ = 1 := by rw [hc]; group
    have hp : p₀ = 1 := hf (htriv.trans (map_one f).symm)
    have hn : p₀ ≠ 1 := by decide +kernel
    exact (hn hp).elim
  · simpa only [h] using hc

public theorem central_model_isConj_eq [Finite K] (T : Sylow 2 K)
    (f : Model →* K) (hf : Function.Injective f)
    (hT : f.range = (T : Subgroup K)) (x : Model)
    (hx : ∀ y : Model, x*y = y*x) (hc : IsConj (f p₀) (f x)) : x = p₀ := by
  apply hf
  apply T.eq_of_isConj_of_normalizer_le_centralizer (f p₀) (f x) _ _ _ hc
  · apply mem_centralizer_iff.mpr
    intro y hy
    change y ∈ (T : Subgroup K) at hy
    rw [← hT] at hy
    obtain ⟨v, rfl⟩ := hy
    simpa only [map_mul] using congrArg f (Local.central_p v)
  · apply mem_centralizer_iff.mpr
    intro y hy
    change y ∈ (T : Subgroup K) at hy
    rw [← hT] at hy
    obtain ⟨v, rfl⟩ := hy
    simpa only [map_mul] using congrArg f (hx v).symm
  · intro g hg
    change g ∈ normalizer ((T : Subgroup K) : Set K) at hg
    rw [← hT] at hg
    exact mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (normalizer_fixes_p f hf g hg))

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.CentralizerStructure.SourceFusion
