module

public import Theory.AlgebraicGroup.Bor1.WeightSpacePointKernel

universe u v w

namespace Theory.AlgebraicGroup.Bor1

variable {k : Type u} [Field k]
variable {Γ : Type v} [Group Γ]
variable {V : Type w} [AddCommGroup V] [Module k V]

/-- Bor1 §5.6's point-kernel argument starting from Chevalley's line-stabilizer
representation.  The distinguished vector determines one common weight block;
its line inside the common-weight span retains the original stabilizer. -/
public theorem Representation.commonWeightBlock_conjRepresentation_ker_eq_of_vectorLineStabilizer
    [FiniteDimensional k V]
    (ρ : Representation k Γ V) (N : Subgroup Γ) [N.Normal]
    (v : V) (hv : v ≠ 0)
    (hLine : ∀ g : Γ, (ρ g : Module.End k V) v ∈ k ∙ v ↔ g ∈ N)
    (τ : Γ →* LinearMap.GeneralLinearGroup k
      (Representation.commonWeightSpan ρ N))
    (hτ : ∀ g x,
      ((((τ g : LinearMap.GeneralLinearGroup k
        (Representation.commonWeightSpan ρ N)) : Module.End k
          (Representation.commonWeightSpan ρ N)) x :
            Representation.commonWeightSpan ρ N) : V) =
        (ρ g : Module.End k V) (x : V)) :
    (blockDiagonalEnd_conjRepresentation
      (Representation.commonWeightBlock ρ N) τ
      (Representation.normalCommonWeightPermutation ρ N)
      (Representation.commonWeightBlock_map_of_restriction ρ N τ hτ)).ker = N := by
  classical
  have hNLine (n : N) : (ρ n.1 : Module.End k V) v ∈ k ∙ v :=
    (hLine n.1).mpr n.2
  let χ : N → k := fun n => Classical.choose (Submodule.mem_span_singleton.mp (hNLine n))
  have hχ (n : N) : (ρ n.1 : Module.End k V) v = χ n • v :=
    (Classical.choose_spec (Submodule.mem_span_singleton.mp (hNLine n))).symm
  have hvcommon : v ∈ Representation.commonEigenspace ρ N χ := by
    rw [Representation.commonEigenspace, Submodule.mem_iInf]
    intro n
    exact Module.End.mem_eigenspace_iff.mpr (hχ n)
  have hcommonne : Representation.commonEigenspace ρ N χ ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, hvcommon, hv⟩
  let χD : Representation.commonWeightIndex ρ N := ⟨χ, hcommonne⟩
  let F := Representation.commonWeightSpan ρ N
  have hvF : v ∈ F := by
    exact (le_iSup (Representation.commonWeightSpace ρ N) χD) hvcommon
  let vf : F := ⟨v, hvF⟩
  let D : Submodule k F := k ∙ vf
  have hvblock : vf ∈ Representation.commonWeightBlock ρ N χD := hvcommon
  have hD : D ≤ Representation.commonWeightBlock ρ N χD := by
    intro x hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
    rw [← ha]
    exact (Representation.commonWeightBlock ρ N χD).smul_mem a hvblock
  have hStabilizer : ∀ g : Γ,
      Submodule.map (τ g : Module.End k F) D = D ↔ g ∈ N := by
    intro g
    constructor
    · intro hmap
      apply (hLine g).mp
      have himage : (τ g : Module.End k F) vf ∈
          Submodule.map (τ g : Module.End k F) D :=
        Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self vf)
      rw [hmap] at himage
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp himage
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      calc
        c • v = ((c • vf : F) : V) := rfl
        _ = (((τ g : Module.End k F) vf : F) : V) := congrArg Subtype.val hc
        _ = (ρ g : Module.End k V) v := hτ g vf
    · intro hg
      apply Submodule.eq_of_le_of_finrank_eq
      · rintro _ ⟨x, hx, rfl⟩
        have hvimage : (τ g : Module.End k F) vf ∈ D := by
          obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((hLine g).mpr hg)
          apply Submodule.mem_span_singleton.mpr
          refine ⟨c, ?_⟩
          apply Subtype.ext
          calc
            ((c • vf : F) : V) = c • v := rfl
            _ = (ρ g : Module.End k V) v := hc
            _ = (((τ g : Module.End k F) vf : F) : V) := (hτ g vf).symm
        obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hx
        rw [← ha, map_smul]
        exact D.smul_mem a hvimage
      · exact LinearEquiv.finrank_map_eq
          (LinearMap.GeneralLinearGroup.toLinearEquiv (τ g)) D
  exact Representation.commonWeightBlock_conjRepresentation_ker_eq_of_lineStabilizer
    ρ N τ hτ D χD hD hStabilizer

end Theory.AlgebraicGroup.Bor1
