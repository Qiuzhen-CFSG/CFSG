module
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalAlignedLinear
public import CFSG.Quasithin.ChapterI.Section04To05.G2Recognition.MaximalCoreForm

/-!
# Full core coordinates on both original aligned endpoints

The marked semidirect-product equivalence on the opposite endpoint is
transported by the same Sylow aligner used by the faithful completion.
Both coordinate maps preserve their original core and actor inclusions.
Their linear quotient is the corresponding right coordinate, and the
preimage of the whole common middle is exactly the linear-Borel preimage.

These are actual maps to the original endpoints. Identifying their full
core actions with the Atlas actions, compatibly on the whole middle,
remains the local recognition step in Aschbacher–Smith I.4.5, p.417.
The literal Chapter14 application is Chapter14CoreAction.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
open Chapter14.Section04.DimensionFour
variable {G : Type*} [Group G] [Finite G] {c : G2ThreeConfiguration G}
namespace AlignedCubicPair
variable {t : CubicTorus c} (d : AlignedCubicPair t)
/-- Full coordinates for the original left endpoint. -/
abbrev leftSplitDomain := (cubicOddCore c t.x) ⋊[t.cubicGLCoreAction d.core_order]
  (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
/-- Full coordinates for the opposite core before the already chosen Sylow alignment. -/
abbrev rightSplitDomain := (cubicOddCore (swapFactors c) t.swap.x) ⋊[
  t.swap.cubicGLCoreAction d.right_core_order] (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))

noncomputable def leftSplitEquiv : d.leftSplitDomain ≃* d.leftEndpoint :=
  t.cubicSplitEquiv d.core_order

noncomputable def rightSplitEquiv : d.rightSplitDomain ≃* d.rightEndpoint :=
  (t.swap.cubicSplitEquiv d.right_core_order).trans d.rightEndpointEquiv

@[simp] theorem leftSplitEquiv_inl (v : cubicOddCore c t.x) :
    (d.leftSplitEquiv (SemidirectProduct.inl v):G)=v :=
  t.cubicSplitEquiv_inl d.core_order v

@[simp] theorem rightSplitEquiv_inl (v : cubicOddCore (swapFactors c) t.swap.x) :
    (d.rightSplitEquiv (SemidirectProduct.inl v):G)=MulAut.conj d.aligner (v:G) := by
  change MulAut.conj d.aligner
    (t.swap.cubicSplitEquiv d.right_core_order (SemidirectProduct.inl v):G)=_
  rw [t.swap.cubicSplitEquiv_inl]

@[simp] theorem leftSplitEquiv_inr (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (d.leftSplitEquiv (SemidirectProduct.inr a):G)=
      ((t.cubicLeviLinearEquiv d.core_order).symm a:G) :=
  t.cubicSplitEquiv_inr d.core_order a

@[simp] theorem rightSplitEquiv_inr (a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    (d.rightSplitEquiv (SemidirectProduct.inr a):G)=
      MulAut.conj d.aligner ((t.swap.cubicLeviLinearEquiv d.right_core_order).symm a:G) := by
  change MulAut.conj d.aligner
    (t.swap.cubicSplitEquiv d.right_core_order (SemidirectProduct.inr a):G)=_
  rw [t.swap.cubicSplitEquiv_inr]

theorem leftSplitEquiv_linear (v : d.leftSplitDomain) :
    d.leftLinearAction (d.leftSplitEquiv v)=v.right :=
  t.cubicSplitEquiv_linear d.core_order v

theorem rightSplitEquiv_linear (v : d.rightSplitDomain) :
    d.rightLinearAction (d.rightSplitEquiv v)=v.right := by
  change t.swap.cubicLinearAction d.right_core_order
    (d.rightEndpointEquiv.symm (d.rightEndpointEquiv
      (t.swap.cubicSplitEquiv d.right_core_order v)))=v.right
  rw [MulEquiv.symm_apply_apply,t.swap.cubicSplitEquiv_linear]

/-- The left coordinate map retains the entire original middle. -/
theorem leftSplitEquiv_middle :
    (t.leftCubicBorel.subgroupOf d.leftEndpoint).comap d.leftSplitEquiv.toMonoidHom=
      (normalizer (((t.leftCoreExtension.subgroupOf d.leftEndpoint).map
        d.leftLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))).comap
          SemidirectProduct.rightHom := t.cubicSplitEquiv_borel d.core_order

/-- The same whole middle is the full linear-Borel preimage in the aligned right coordinates. -/
theorem rightSplitEquiv_middle :
    (t.leftCubicBorel.subgroupOf d.rightEndpoint).comap d.rightSplitEquiv.toMonoidHom=
      (normalizer (((t.leftCoreExtension.subgroupOf d.rightEndpoint).map
        d.rightLinearAction):Set (Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)))).comap
          SemidirectProduct.rightHom := by
  rw [←d.rightLinearAction_borel]
  have hRB : d.rightCore≤t.leftCubicBorel := by
    rw [←t.maximal_aligned_borels d.core_order d.aligner d.aligned]
    exact map_mono (le_sup_left.trans le_sup_left)
  have hk : d.rightLinearAction.ker≤t.leftCubicBorel.subgroupOf d.rightEndpoint := by
    rw [d.rightLinearAction_kernel]
    exact fun _ h=>hRB h
  have hh := comap_map_eq_self hk
  ext a
  change d.rightSplitEquiv a∈t.leftCubicBorel.subgroupOf d.rightEndpoint ↔
    a.right∈(t.leftCubicBorel.subgroupOf d.rightEndpoint).map d.rightLinearAction
  rw [←d.rightSplitEquiv_linear a]
  exact (SetLike.ext_iff.mp hh (d.rightSplitEquiv a)).symm

end AlignedCubicPair
end CFSG.Quasithin.ChapterI.Section04To05.G2Recognition
