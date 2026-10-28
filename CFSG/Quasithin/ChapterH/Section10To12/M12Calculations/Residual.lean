module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Inner
public import CFSG.Quasithin.ChapterH.Section05To09.AlternatingPair.Parameters

/-!
# Transporting the native heart calculations to the solvable residual

The given group and module equivalences identify the fixed codimension of
any residual subgroup with its native M₁₂ counterpart. Consequently every
residual involution has displacement four and fixed dimension six. The marked
involution and the marked cubic element lift to the ambient group, proving
`m ≤ 4` and providing an odd-order element with displacement six.

The native module has `m = 4`. For the ambient group, the equality is proved
conditionally on the outer-involution displacement calculation, which remains
a separate obligation. No bound for outer actors or absence of offenders is
inferred just from the residual restriction.

Source: Aschbacher–Smith H.11.1(2) and the preceding discussion of β, printed
p.392, combined manuscript of 1 March 2004.
-/

public section
open Representation.BinaryOffender Sporadic.Mathieu
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem fixedCodim_residual_subgroup (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) (A : Subgroup (Subgroup.solvableResidual G)) :
    fixedCodim ρ (A.map (Subgroup.solvableResidual G).subtype) =
      fixedCodim m12HeartRepresentation (A.map h.residualEquiv.toMonoidHom) := by
  have he := fixedCodim_map_equivariant (ρ.comp (Subgroup.solvableResidual G).subtype)
    m12HeartRepresentation h.residualEquiv.toMonoidHom h.moduleEquiv.toLinearEquiv
    (fun a v => LinearMap.congr_fun (h.moduleEquiv.toIntertwiningMap.isIntertwining' a) v) A
  unfold fixedCodim at he ⊢
  rw [fixedSpace_comp_map ρ (Subgroup.solvableResidual G).subtype A] at he
  exact he

theorem fixedCodim_residual_element (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) (t : Subgroup.solvableResidual G) :
    fixedCodim ρ (Subgroup.zpowers (t : G)) =
      fixedCodim m12HeartRepresentation (Subgroup.zpowers (h.residualEquiv t)) := by
  simpa only [MonoidHom.map_zpowers, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom]
    using fixedCodim_residual_subgroup ρ h (Subgroup.zpowers t)

theorem fixedCodim_residual_involution (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) {t : G} (htL : t ∈ Subgroup.solvableResidual G)
    (ht : orderOf t = 2) : fixedCodim ρ (Subgroup.zpowers t) = 4 := by
  rw [fixedCodim_residual_element ρ h ⟨t, htL⟩]
  apply fixedCodim_involution
  rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
  exact ht

theorem finrank_fixedSpace_residual_involution [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) {t : G} (htL : t ∈ Subgroup.solvableResidual G)
    (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) (fixedSpace ρ (Subgroup.zpowers t)) = 6 := by
  have hd := fixedCodim_add_finrank ρ (Subgroup.zpowers t)
  rw [fixedCodim_residual_involution ρ h htL ht, h.finrank_eq_ten ρ] at hd
  omega

theorem exists_residual_involution (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) :
    ∃ t : G, t ∈ Subgroup.solvableResidual G ∧ orderOf t = 2 ∧
      fixedCodim ρ (Subgroup.zpowers t) = 4 := by
  let t := h.residualEquiv.symm M12SmallPair.z
  have ht : orderOf (t : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact h.residualEquiv.symm.orderOf_eq M12SmallPair.z |>.trans M12SmallPair.z_order
  exact ⟨t, t.property, ht, fixedCodim_residual_involution ρ h t.property ht⟩

theorem moduleM_le_four (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) : ChapterE.moduleM ρ ≤ 4 := by
  obtain ⟨t, _, ht, hd⟩ := exists_residual_involution ρ h
  exact hd ▸ ChapterE.moduleM_le_involution ρ ht

theorem moduleM_native : ChapterE.moduleM m12HeartRepresentation = 4 :=
  AlternatingPair.moduleM_eq_of_constant_involution_codim m12HeartRepresentation
    ⟨M12SmallPair.z, M12SmallPair.z_order⟩ fixedCodim_involution

theorem moduleM_eq_four_of_outer_displacement [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (h : M12ModuleInput ρ)
    (hout : ∀ t : G, t ∉ Subgroup.solvableResidual G → orderOf t = 2 →
      fixedCodim ρ (Subgroup.zpowers t) = 5) : ChapterE.moduleM ρ = 4 := by
  obtain ⟨u, _, hu, _⟩ := exists_residual_involution ρ h
  obtain ⟨t, ht, hmin⟩ := ChapterE.moduleM_attained ρ ⟨u, hu⟩
  apply le_antisymm (moduleM_le_four ρ h)
  rw [← hmin]
  by_cases htL : t ∈ Subgroup.solvableResidual G
  · rw [fixedCodim_residual_involution ρ h htL ht]
  · rw [hout t htL ht]
    decide

theorem exists_residual_cubic (ρ : Representation (ZMod 2) G V)
    (h : M12ModuleInput ρ) :
    ∃ x : G, x ∈ Subgroup.solvableResidual G ∧ orderOf x = 3 ∧
      fixedCodim ρ (Subgroup.zpowers x) = 6 := by
  let x := h.residualEquiv.symm M12SmallPair.cubicActor
  refine ⟨x, x.property, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact h.residualEquiv.symm.orderOf_eq M12SmallPair.cubicActor |>.trans M12SmallPair.cubicActor_order
  · rw [fixedCodim_residual_element ρ h x]
    simpa only [x, MulEquiv.apply_symm_apply] using fixedCodim_cubicActor

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
