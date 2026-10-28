module
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.ChiefKernel
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.EssentialChiefActor

/-!
# The essential actor as the reduced whole-span action

The same sharp actor already aligns the literal images of all noncentral
chief factors with the essential source actor. Their kernels are therefore
equal. The flag-kernel calculation identifies the image of this common
kernel on the whole span with exactly the whole-action two-core. The
resulting quotient equivalence to the essential actor intertwines the
original H-action, hence also every original subgroup image.

This supplies kernel transport for the original Cartan argument in
Aschbacher--Smith, 3.1.9(6), printed pp.577--578. The kernel upstairs is
retained; it is not asserted to be O₂(H). The natural-module and cubic
exclusions remain separate steps.
-/

public noncomputable section
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open Chapter3 ChapterB ChapterD Theory.GroupTheory
open NoncentralChiefRefinement Representation Representation.BinaryOffender Subgroup
universe u
variable {G : Type u} [Group G] [Finite G] {H V : Subgroup G}
  [IsElementaryAbelian 2 ((conjugateSpan H V).subgroupOf H)]
  {S : Sylow 2 H} {hVH : V ≤ H}

set_option backward.isDefEq.respectTransparency false in
/-- The essential chief actor is the faithful whole-span actor modulo its
actual two-core, compatibly with every original element and subgroup. -/
theorem essential_span_image_reduction
    (a : EssentialSeedAction H V S hVH)
    (A : Subgroup H) (hA : EssentialChiefActor a A)
    (s : SeriesOn ((conjugateSpan H V).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    Nonempty (MathieuCode.NormalizedShadowRows.ActionImageReduction
      (H := H) (W := Additive ((conjugateSpan H V).subgroupOf H))
      (W' := a.socle.toSubmodule) (normalRepresentation ((conjugateSpan H V).subgroupOf H)) a.representation) := by
  let U := (conjugateSpan H V).subgroupOf H
  let ρ := normalRepresentation U
  have hk (j : Fin s.series.length) (hj : ¬ s.Central j) :
      (s.factorRepresentation j).ker = a.representation.ker := by
    obtain ⟨c⟩ := (hA.chief s j hj).2
    rw [← actionHom_ker_eq,← actionHom_ker_eq]
    ext x
    change actionHom (s.factorRepresentation j) x = 1 ↔ a.projection x = 1
    constructor
    · intro hx
      apply c.equiv.injective
      exact (c.map_action x).trans (hx.trans c.equiv.map_one.symm)
    · intro hx
      exact (c.map_action x).symm.trans ((congrArg c.equiv hx).trans c.equiv.map_one)
  have hcore := MathieuCode.NormalizedShadowRows.common_chief_kernel_image_eq_twoCore
    U s a.representation.ker hk i hi
  obtain ⟨e,he⟩ := MathieuCode.NormalizedShadowRows.exists_span_twoCore_quotient_equiv
    U s a.representation.ker hk i hi
  obtain ⟨c⟩ := (hA.chief s i hi).2
  let f := e.trans c.equiv.symm
  have hf (x : H) : f (QuotientGroup.mk' (pCore 2 (actionImage ρ)) (actionHom ρ x)) =
      a.projection x := by
    change c.equiv.symm (e (QuotientGroup.mk' (pCore 2 (actionImage ρ))
      (actionHom ρ x))) = a.projection x
    exact (congrArg c.equiv.symm (he x)).trans
      ((congrArg c.equiv.symm (c.map_action x)).symm.trans (c.equiv.symm_apply_apply _))
  exact ⟨⟨hcore,f,hf⟩⟩

end CFSG.Quasithin.Chapter8.MathieuShadowRows

