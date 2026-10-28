module
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.RadicalGeometry.Shears
public import Theory.GroupTheory.SylowKernelCore
public import Theory.Representation.BinaryOffender.SubspaceAction
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.FlagSylow
public import Theory.Representation.SL5ExteriorSquare.LocalGeometry.ParabolicStructure.LeviStructure.Blocks
public import Theory.Representation.BinaryOffender.EquivariantOffender
import Mathlib.Tactic.FinCases

/-!
# The stabilizer of a Sylow-fixed exterior seed

The upper-triangular Sylow fixes only the highest wedge line in Λ²(F₂⁵).
Conjugating an arbitrary Sylow to this flag identifies the pointwise stabilizer
of every nonzero fixed seed with the actual 2+3 parabolic. Its two-core lies
in the hyperplane parabolic but does not contain the full hyperplane shear
radical: the shear from the fifth to the third coordinate acts nontrivially
on the three-dimensional Levi block.

Together with the exterior offender classification, these facts exclude best
offenders from the seed stabilizer's two-core. The classification and its
source application are connected in the Chapter 15 exterior consumer.

Source: Aschbacher--Smith 15.1.28, printed p.1103, and B.4.2(11), p.86.
-/

public section
open Subgroup
namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

private def lowerIndex : Fin 10 → Fin 5 := ![0,1,1,1,0,0,0,0,0,0]
private def upperIndex : Fin 10 → Fin 5 := ![1,2,3,4,1,1,1,2,2,3]
private def outputIndex : Fin 10 → Fin 10 := ![0,0,0,0,1,2,3,2,3,3]

private theorem coordinate_step (v : V) (t : Fin 10) (ht : t ≠ 0) :
    coordinates (exteriorAction 2 (elementary (lowerIndex t) (upperIndex t)) v)
      (outputIndex t) = coordinates v (outputIndex t) + coordinates v t := by
  have row : actionMatrix (elementary (lowerIndex t) (upperIndex t)) (outputIndex t) =
      Pi.single (outputIndex t) 1 + Pi.single t 1 := by
    fin_cases t
    · exact (ht rfl).elim
    all_goals ext j; fin_cases j <;> rfl
  rw [coordinates_action]
  change dotProduct (actionMatrix _ (outputIndex t)) (coordinates v) = _
  rw [row, add_dotProduct]
  simp

private theorem elementary_upper_mem_flag (i j : Fin 5) (hij : i < j) :
    elementary i j ∈ flagGroup := by
  rw [flagGroup, mem_iInf]
  intro k
  rw [mem_parabolic_iff_lowerLeft_zero]
  intro a b ha hb
  have hab : a ≠ b := by intro h; subst b; omega
  have hn : ¬ (a = i ∧ b = j) := by
    rintro ⟨rfl,rfl⟩
    omega
  simp [elementary, ne_of_lt hij, Matrix.SpecialLinearGroup.transvection,
    Matrix.transvection, hab, Matrix.single_apply]
  intro hi hj
  exact hn ⟨hi.symm,hj.symm⟩

theorem fixedSpace_flagGroup_le :
    BinaryOffender.fixedSpace (exteriorAction 2) flagGroup ≤ V₁ := by
  intro v hv
  apply (mem_coordinateSpan {0} v).mpr
  intro t ht
  have ht0 : t ≠ 0 := by simpa using ht
  have hij : lowerIndex t < upperIndex t :=
    (by decide : ∀ t, lowerIndex t < upperIndex t) t
  have he := hv ⟨_,elementary_upper_mem_flag _ _ hij⟩
  change exteriorAction 2 (elementary (lowerIndex t) (upperIndex t)) v = v at he
  have hh := coordinate_step v t ht0
  rw [he] at hh
  exact (add_eq_left.mp hh.symm)

end Representation.SL5ExteriorSquare

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional
open BinaryLinear.OuterCyclic BinaryLinear.FiveFlagGeometry.SylowOvergroups

private theorem flagGroup_isPGroup : IsPGroup 2 flagGroup := by
  rw [flagGroup_eq_standardBorel_comap]
  exact standardBorel_isPGroup.comap_of_injective (slEquivLinear 5).toMonoidHom (slEquivLinear 5).injective

theorem exists_sylow_map_eq_flagGroup (R : Sylow 2 Group) :
    ∃ g : Group, (R : Subgroup Group).map (MulAut.conj g).toMonoidHom = flagGroup := by
  obtain ⟨g,hg⟩ := exists_conjugate_le_flagGroup R R.isPGroup'
  let Q : Sylow 2 Group := R.mapSurjective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).surjective
  exact ⟨g, (Q.is_maximal' flagGroup_isPGroup hg).symm⟩

end Representation.SL5ExteriorSquare

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

theorem seedKernel_V₁ : BinaryOffender.subspaceKernel (exteriorAction 2) V₁ ⊤ = parabolic 2 := by
  have hspan : V₁ = Submodule.span (ZMod 2) {decomposable} := by
    simp [V₁,coordinateSpan,decomposable]
  have hk : BinaryOffender.subspaceKernel (exteriorAction 2) V₁ ⊤ =
      vectorStabilizer decomposable := by
    ext g
    constructor
    · intro h
      exact h.2 _ (hspan ▸ Submodule.subset_span (Set.mem_singleton _))
    · intro h
      change exteriorAction 2 g decomposable = decomposable at h
      refine ⟨mem_top _, ?_⟩
      intro v hv
      rw [hspan] at hv
      induction hv using Submodule.span_induction with
      | mem v hv => simpa only [Set.mem_singleton_iff.mp hv] using h
      | zero => exact map_zero _
      | add x y hx hy hfx hfy => simp only [map_add,hfx,hfy]
      | smul a x hx hfx => simp only [map_smul,hfx]
  rw [hk,vectorStabilizer_eq_exteriorStabilizer_point,← hspan,
    exteriorStabilizer_V₁_eq_parabolic]

theorem twoCore_parabolic_two_le_four : (parabolic 2).pCoreIn 2 ≤ parabolic 4 := by
  rintro g ⟨a,ha,rfl⟩
  rw [mem_parabolic_iff_lowerLeft_zero]
  intro i j hi hj
  have hi4 : i = 4 := Fin.ext (by omega)
  subst i
  by_cases hj2 : j.val < 2
  · exact (mem_parabolic_iff_lowerLeft_zero 2 a.val).mp a.property 4 j (by decide) hj2
  · have hh := ((mem_parabolic_twoCore_iff 2 (by decide) a).mp ha).2
    have hjv : j.val = 2 ∨ j.val = 3 := by omega
    rcases hjv with h2 | h3
    · have he : j = 2 := Fin.ext h2
      subst j
      exact hh 2 0
    · have he : j = 3 := Fin.ext h3
      subst j
      exact hh 2 1

theorem shear_not_le_twoCore_parabolic_two : ¬ shearSubgroup ≤ (parabolic 2).pCoreIn 2 := by
  intro h
  obtain ⟨a,ha,he⟩ := h (shear_mem (Pi.single 2 1))
  have hh := ((mem_parabolic_twoCore_iff 2 (by decide) a).mp ha).2 (0 : Fin 3) 2
  change a.val.val 2 4 = 0 at hh
  change a.val = shear (Pi.single 2 1) at he
  have hm := congrArg (fun x : Group => x.val 2 4) he
  rw [matrix_shear] at hm
  rw [hm] at hh
  change (1 : ZMod 2) = 0 at hh
  exact one_ne_zero hh

end Representation.SL5ExteriorSquare

namespace Representation.SL5ExteriorSquare
open SL5TenDimensional

/-- Conjugating the Sylow to the standard flag identifies the actual seed kernel. -/
theorem seedKernel_conjugate_parabolic_two (R : Sylow 2 Group)
    (P : Submodule (ZMod 2) V) (hn : P ≠ ⊥)
    (hf : P ≤ BinaryOffender.fixedSpace (exteriorAction 2) R) :
    ∃ g : Group, (BinaryOffender.subspaceKernel (exteriorAction 2) P ⊤).map
      (MulAut.conj g).toMonoidHom = parabolic 2 := by
  obtain ⟨g,hg⟩ := exists_sylow_map_eq_flagGroup R
  let e : V ≃ₗ[ZMod 2] V := LinearMap.GeneralLinearGroup.toLinearEquiv ((exteriorAction 2).asGroupHom g)
  have he (a : Group) (v : V) :
      e (exteriorAction 2 a v) = exteriorAction 2 (MulAut.conj g a) (e v) := by
    change exteriorAction 2 g (exteriorAction 2 a v) =
      exteriorAction 2 (g * a * g⁻¹) (exteriorAction 2 g v)
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp only [inv_mul_cancel_right]
  have hp : P.map e.toLinearMap ≤ V₁ := by
    apply le_trans (Submodule.map_mono hf)
    rw [BinaryOffender.fixedSpace_map_equivariant (exteriorAction 2) (exteriorAction 2)
      (MulAut.conj g).toMonoidHom e he, hg]
    exact fixedSpace_flagGroup_le
  have hpn : P.map e.toLinearMap ≠ ⊥ := by
    intro hz
    apply hn
    apply le_bot_iff.mp
    intro v hv
    apply e.injective
    have hm := Submodule.mem_map_of_mem (f := e.toLinearMap) hv
    rw [hz,Submodule.mem_bot] at hm
    exact hm.trans (map_zero e).symm
  have hpEq : P.map e.toLinearMap = V₁ := by
    apply Submodule.eq_of_le_of_finrank_le hp
    rw [standard_dimensions.1]
    have := Submodule.nontrivial_iff_ne_bot.mpr hpn
    exact Module.finrank_pos
  refine ⟨g, ?_⟩
  rw [← seedKernel_V₁, ← hpEq]
  ext a
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨mem_top _, ?_⟩
    rintro _ ⟨v,hv,rfl⟩
    exact (he b v).symm.trans (congrArg e (hb.2 v hv))
  · intro ha
    let b := (MulAut.conj g).symm a
    refine ⟨b, ⟨mem_top _, ?_⟩, (MulAut.conj g).apply_symm_apply a⟩
    intro v hv
    apply e.injective
    rw [he]
    have hb : MulAut.conj g b = a := (MulAut.conj g).apply_symm_apply a
    rw [hb]
    exact ha.2 _ (Submodule.mem_map_of_mem hv)

end Representation.SL5ExteriorSquare
