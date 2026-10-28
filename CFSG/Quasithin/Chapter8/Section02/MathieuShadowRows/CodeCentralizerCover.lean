module
public import CFSG.Quasithin.Chapter8.Section01.MathieuShadowRows.ResidualCover
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleCoreCentralLift

/-!
# Central covering kernels above the M22 hexad residual

The original point stabilizer first maps through the two-core of L,
then through a possibly nontrivial central kernel onto the hexad stabilizer.
Taking perfect residuals and two-core quotients gives a quasisimple group
with the native A₆ projective model. This argument keeps the entire
central kernel; it does not identify the full quotient with A₆.
The actual application is `M22CodeCentralizer`.

Source: the covering step in Aschbacher--Smith 8.2.2(1), printed p.715,
refs/quasithin.pdf, using finite central-cover and prime-core calculus.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
variable {C Y X : Type*} [Group C] [Finite C] [Group Y] [Finite Y]
  [Group X] [Group.IsPerfect X] [IsQuasisimple (X ⧸ pCore 2 X)]

/-- A central cover followed by a two-cover preserves the projective model
of the perfect residual modulo its full two-core. -/
theorem residual_core_central_quotient
    (q : C →* Y) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (f : Y →* X) (hf : Function.Surjective f) (hc : f.ker ≤ center Y) :
    IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) ∧
      Nonempty (((solvableResidual C ⧸ pCore 2 (solvableResidual C)) ⧸
        center (solvableResidual C ⧸ pCore 2 (solvableResidual C))) ≃*
          ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X))) := by
  let : IsSimpleGroup ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) := IsQuasisimple.simple
  let : Nontrivial (X ⧸ pCore 2 X) := (QuotientGroup.mk'_surjective (center (X ⧸ pCore 2 X))).nontrivial
  let R := solvableResidual Y
  let r := f.comp R.subtype
  have hr : Function.Surjective r := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,range_subtype,map_solvableResidual_eq f hf,
      solvableResidual_eq_top]
  have hrc : r.ker ≤ center R := by
    intro x hx
    exact mem_center_iff.mpr (fun y => Subtype.ext
      (mem_center_iff.mp (hc (show f x = 1 from hx)) y))
  let : IsQuasisimple (R ⧸ pCore 2 R) :=
    quasisimple_core_quotient_of_central_kernel r hr hrc
  have hl : pCore 2 R ≤ (pCore 2 X).comap r := by
    rw [←map_le_iff_le_comap]
    exact le_sSup ⟨Normal.map inferInstance r hr,pCore_isPGroup.map r⟩
  let g := QuotientGroup.map (pCore 2 R) (pCore 2 X) r hl
  have hg : Function.Surjective g := QuotientGroup.map_surjective_of_surjective _ _ _
    ((QuotientGroup.mk'_surjective _).comp hr) _
  let e := q.solvableResidualMap.pCoreQuotientEquiv
    (q.solvableResidualMap_surjective hq) (q.solvableResidualMap_ker_isPGroup hk)
  refine ⟨IsQuasisimple.of_mulEquiv e.symm,⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e (FixedElementary.map_center e)).trans
    (IsQuasisimple.centralQuotientEquiv g hg)

/-- The original commuting square may retain an odd central covering
kernel; only the preceding two-kernel is removed. -/
theorem residual_core_central_quotient_of_factorization
    {Z : Type*} [Group Z]
    (q : C →* Y) (hq : IsPGroup 2 q.ker)
    (k : Y →* Z) (hk : k.ker ≤ center Y)
    (f : C →* X) (hf : Function.Surjective f)
    (j : X →* Z) (hj : Function.Injective j)
    (hcomm : ∀ c, k (q c) = j (f c)) :
    IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) ∧
      Nonempty (((solvableResidual C ⧸ pCore 2 (solvableResidual C)) ⧸
        center (solvableResidual C ⧸ pCore 2 (solvableResidual C))) ≃*
          ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X))) := by
  let r := q.rangeRestrict
  have hr : Function.Surjective r := q.rangeRestrict_surjective
  have hker : r.ker ≤ f.ker := by
    intro c hc
    apply hj
    rw [map_one,←hcomm]
    have hq1 : q c = 1 := congrArg Subtype.val hc
    rw [hq1,map_one]
  let g := r.liftOfSurjective hr ⟨f,hker⟩
  have hg (c : C) : g (r c) = f c := r.liftOfRightInverse_comp_apply _ _ _ c
  have hgs : Function.Surjective g := by
    intro x
    obtain ⟨c,rfl⟩ := hf x
    exact ⟨r c,hg c⟩
  have hgc : g.ker ≤ center q.range := by
    intro x hx
    obtain ⟨c,rfl⟩ := hr x
    have hfc : f c = 1 := (hg c).symm.trans hx
    have hqc : q c ∈ center Y := hk (by rw [MonoidHom.mem_ker,hcomm,hfc,map_one])
    exact mem_center_iff.mpr (fun y => Subtype.ext (mem_center_iff.mp hqc y))
  exact residual_core_central_quotient r hr (by
    change IsPGroup 2 q.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hq) g hgs hgc
end CFSG.Quasithin.Chapter8.MathieuShadowRows
