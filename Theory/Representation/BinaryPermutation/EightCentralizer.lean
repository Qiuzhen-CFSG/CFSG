module
public import Theory.Representation.BinaryPermutation.EightCommutant

/-!
# The ambient centralizer of a natural A₈ subgroup

Transport a centralizing group element to the literal deleted eight-point
module. Its invertible commutant is trivial, and faithfulness then makes the
original group element trivial. This retains the subgroup and the intertwiner
needed by the original terminal point-centralizer calculation.

Source: Aschbacher–Smith B.3.1 and 12.8.13(5), printed pp.83,855–856.
-/

public section
open Subgroup Representation
noncomputable section
namespace BinaryPermutation.EightCommutant
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
/-- A faithfully represented natural A₈ subgroup has trivial ambient centralizer. -/
theorem centralizer_eq_bot_of_coordinates (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ) (L : Subgroup D)
    (e : L ≃* alternatingGroup (Fin 8)) (c : V ≃ₗ[ZMod 2] natural (Fin 8))
    (hc : ∀ (l : L) w, c (ρ l w) = alternatingNaturalRepresentation (Fin 8) (e l) (c w)) :
    centralizer (L : Set D) = ⊥ := by
  apply bot_unique
  intro a ha
  let J := c.symm.trans ((LinearEquiv.ofBijective (ρ a) (ρ.apply_bijective a)).trans c)
  have hj (w : natural (Fin 8)) : J w = c (ρ a (c.symm w)) := rfl
  have hJ : J = LinearEquiv.refl _ _ := by
    apply commuting_eq_refl
    intro b w
    obtain ⟨l,rfl⟩ := e.surjective b
    obtain ⟨z,rfl⟩ := c.surjective w
    change J (alternatingNaturalRepresentation (Fin 8) (e l) (c z)) =
      alternatingNaturalRepresentation (Fin 8) (e l) (J (c z))
    rw [← hc,hj,c.symm_apply_apply,hj,c.symm_apply_apply,← hc]
    rw [← Module.End.mul_apply,← map_mul,← Module.End.mul_apply,← map_mul]
    rw [show a*(l:D)=(l:D)*a from (ha l l.property).symm]
  apply mem_bot.mpr
  apply hf
  apply LinearMap.ext
  intro w
  have he := congrArg (fun f : natural (Fin 8) ≃ₗ[ZMod 2] natural (Fin 8) => f (c w)) hJ
  change c (ρ a (c.symm (c w))) = c w at he
  rw [c.symm_apply_apply] at he
  simpa only [map_one,Module.End.one_apply] using c.injective he
end BinaryPermutation.EightCommutant
