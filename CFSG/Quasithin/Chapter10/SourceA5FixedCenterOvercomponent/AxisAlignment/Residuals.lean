module
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterOvercomponent.AxisAlignment.OriginalMoved
public import CFSG.Quasithin.Chapter10.SourceA5ActionKernel
public import Theory.GroupTheory.PResidual.MapInjectivity

/-!
# The original A₅ block is a paired residual factor

Lift the marked quotient-axis identification through its two-group kernel.
Both the original block and the factor residual are two-perfect and normalized
by that kernel, so equality of their quotient images gives equality in the
original local group. The paired action and its exchanger remain unchanged.

Source: Aschbacher–Smith 10.2.1, printed p.743, using E.2.3.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 ChapterC ChapterE.ThompsonAction
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

@[expose] def SourceOriginalResidualAxes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L) : Prop :=
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let U := D.moduleSubgroup.subgroupOf H
  letI := (source_parabolic_module_reduced D).normal
  letI := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
      (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  letI := offenderSubgroup_normal α
  let A := L.subgroupOf H
  ∃ d : ChapterB.SourceInduction.SourceTwoFactorCase (α.comp Y.subtype),
    ∃ _c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)),
      (∃ t : S.mapSurjective (QuotientGroup.mk'_surjective C),
        d.first.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t : H ⧸ C)).toMonoidHom = d.first) ∧
      Y.comap q ≤ normalizer (A : Set H) ∧
      (A = factorResidual q Y d.first ∨ A = factorResidual q Y d.second)

theorem source_a5_original_residual_axes
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal) :
    SourceOriginalResidualAxes D := by
  let H := localJoin T L
  let U := D.moduleSubgroup.subgroupOf H
  let := (source_parabolic_module_reduced D).normal
  let := (source_parabolic_module_reduced D).elementary
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let α := NormalElementaryQuotient.representation U q
    (QuotientGroup.mk'_surjective C) (QuotientGroup.ker_mk' C)
  let Y := offenderSubgroup α
  let A := L.subgroupOf H
  obtain ⟨d,c,hex,hN,haxes⟩ := source_a5_original_paired_axes D e hn hout
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact source_a5_local_module_kernel_isTwoGroup D e hn
  have hkY : q.ker ≤ Y.comap q := by
    intro x hx
    change q x ∈ Y
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _
  have hpA : IsPPerfect 2 A :=
    (source_a5_original_block_of_baumann_not_controlled D e hn hout).1.short.twoPerfect
  have hf (B : Subgroup Y) [B.Normal] (he : A.map q = (factorResidual q Y B).map q) :
      A = factorResidual q Y B :=
    eq_of_map_eq_map_of_isPPerfect q hpA (isPPerfect_embedded_pResidual 2 _) hk
      (hkY.trans hN) (hkY.trans (factorResidual_normalized q Y B)) he
  let := d.product.first_normal
  let := d.product.second_normal
  exact ⟨d,c,hex,hN,haxes.imp (hf d.first) (hf d.second)⟩

end CFSG.Quasithin.Chapter10
