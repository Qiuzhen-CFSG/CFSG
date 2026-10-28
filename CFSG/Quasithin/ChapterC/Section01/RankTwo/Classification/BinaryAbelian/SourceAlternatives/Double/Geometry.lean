module

public import Theory.Representation.PSL3Two.DoubledLocalFlag

/-!
# A point fixer moves the doubled-natural offender

The upper triangular Sylow fixes the first coordinate line in each natural
summand. A cubic acting on the last two coordinates fixes both such lines,
but does not normalize the common-axis four-group. Conjugation gives the
same obstruction in every simultaneous marking of the Sylow and offender.
All groups here are literal matrix groups, and the final nonnormalization is
in the actual doubled linear action, not only in the abstract component.

This is the finite-model part of Aschbacher–Smith C.1.34(2), combined
manuscript (1 March 2004), printed p.137. Its original-group consumer is
`MarkedMS.LinearThree.AbelianSourceDouble`; lifting a fixed-space centralizer
to the centralizer of the Sylow omega-center remains a separate source step.
-/

public section

open Subgroup Representation Representation.BinaryOffender Matrix
open BinaryLinearThree Matrix.PSL3Two

namespace BinaryLinearThree.DoubledOffenders

private def pointCycle : Group := ⟨!![1,0,0; 0,0,1; 0,1,1], by decide⟩

private theorem pointCycle_fixes : ∀ v : Vector,
    W (Bruhat.upper 1) v = v → W (Bruhat.upper 4) v = v → W pointCycle v = v := by
  decide +kernel

private theorem pointCycle_not_normalizes : pointCycle ∉ normalizer (R : Set Group) := by
  rw [normalizer_shear_radical]
  decide

private theorem pointCycle_fixes_borel (v : Vector × Vector)
    (hv : v ∈ fixedSpace (W.prod W) borelSL) : (W.prod W) pointCycle v = v := by
  apply Prod.ext
  · exact pointCycle_fixes v.1
      (congrArg Prod.fst (hv ⟨_, Bruhat.upper_mem 1⟩))
      (congrArg Prod.fst (hv ⟨_, Bruhat.upper_mem 4⟩))
  · exact pointCycle_fixes v.2
      (congrArg Prod.snd (hv ⟨_, Bruhat.upper_mem 1⟩))
      (congrArg Prod.snd (hv ⟨_, Bruhat.upper_mem 4⟩))

/-- The common-axis four-group is an offender with this exact conjugate marking. -/
theorem axis_isOffender (g : Group) :
    IsOffender τ ((R.map (MulAut.conj g).toMonoidHom).map δ) := by
  have h : IsOffender (W.prod W) (R.map (MulAut.conj g).toMonoidHom) := by
    refine ⟨DoubledFixedSpace.radical_isOffender.1.map_conj g, ?_⟩
    rw [fixedCodim_map_conj, rank_map_conj]
    exact DoubledFixedSpace.radical_isOffender.2
  exact h.map_equivariant (W.prod W) τ δ δ_injective
    (LinearEquiv.refl _ _) (fun _ _ => rfl)

/-- A component element fixes the entire doubled Sylow fixed space and moves
the common-axis offender. The same conjugator marks both subgroups. -/
theorem exists_point_fixer_moving_axis (g : Group) :
    ∃ c : Group,
      (∀ v ∈ fixedSpace τ ((borelSL.map (MulAut.conj g).toMonoidHom).map δ),
        τ (δ c) v = v) ∧
      δ c ∉ normalizer ((R.map (MulAut.conj g).toMonoidHom).map δ : Set D) := by
  refine ⟨g * pointCycle * g⁻¹, ?_, ?_⟩
  · intro v hv
    have hv' : v ∈ fixedSpace (W.prod W) (borelSL.map (MulAut.conj g).toMonoidHom) := by
      rwa [← fixedSpace_comp_map τ δ] at hv
    let w : Vector × Vector := (W.prod W) g⁻¹ v
    have hinv_all (u : Vector × Vector) : (W.prod W) g⁻¹ ((W.prod W) g u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    have hwb : w ∈ fixedSpace (W.prod W) borelSL := by
      intro b
      have hb := hv' ⟨g * (b : Group) * g⁻¹, ⟨b, b.property, rfl⟩⟩
      change (W.prod W) (g * (b : Group) * g⁻¹) v = v at hb
      have hh := congrArg (fun u => (W.prod W) g⁻¹ u) hb
      rw [map_mul, map_mul] at hh
      simp only [Module.End.mul_apply, hinv_all] at hh
      exact hh
    have hw : (W.prod W) g w = v := by
      change (W.prod W) g ((W.prod W) g⁻¹ v) = v
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    change (W.prod W) (g * pointCycle * g⁻¹) v = v
    rw [← hw, map_mul, map_mul]
    change (W.prod W) g ((W.prod W) pointCycle
      ((W.prod W) g⁻¹ ((W.prod W) g (w : Vector × Vector)))) = _
    have hinv : (W.prod W) g⁻¹ ((W.prod W) g (w : Vector × Vector)) = w := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [hinv, pointCycle_fixes_borel _ hwb]
  · intro hn
    have hng : g * pointCycle * g⁻¹ ∈ normalizer
        (R.map (MulAut.conj g).toMonoidHom : Set Group) := by
      have hh := (Subgroup.le_normalizer_comap δ) hn
      rwa [comap_map_eq_self_of_injective δ_injective] at hh
    rw [normalizer_shear_conjugate] at hng
    have hc : pointCycle ∈ lineParabolicSL := by
      simpa [mem_map_equiv, MulAut.conj_apply, mul_assoc] using hng
    exact pointCycle_not_normalizes (normalizer_shear_radical.symm ▸ hc)

end BinaryLinearThree.DoubledOffenders
