module
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple
public import Theory.GroupTheory.SolvableResidual.Transport
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import Theory.GroupTheory.GeneralizedFitting.TwoCoreImageComparison
public import Theory.GroupTheory.FixedElementaryTransport

/-!
# Point residuals through the full central covering kernel

A point stabilizer in the original component first maps through a two-group
kernel, then through a central kernel onto its simple point model. Its
solvable residual has quasisimple two-core quotient with that same simple
central quotient. No central kernel is deleted from the original group.

This is the covering step in Aschbacher--Smith 8.1.1, printed p.712.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
variable {C Y X : Type*} [Group C] [Finite C] [Group Y] [Finite Y]
  [Group X] [IsQuasisimple X]

/-- The residual above a central cover retains its actual two-core and
has the same projective model as the original point image. -/
theorem residual_central_quotient
    (q : C →* Y) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (f : Y →* X) (hf : Function.Surjective f) (hc : f.ker ≤ center Y) :
    IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) ∧
      Nonempty (((solvableResidual C ⧸ pCore 2 (solvableResidual C)) ⧸
        center (solvableResidual C ⧸ pCore 2 (solvableResidual C))) ≃*
          (X ⧸ center X)) := by
  let : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let : Nontrivial X := (QuotientGroup.mk'_surjective (center X)).nontrivial
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
  let : Nontrivial R := Function.Surjective.nontrivial hr
  let c : PerfectCentralCovering.Cover R X := ⟨r,hr,inferInstance,hrc⟩
  let : IsQuasisimple R := c.isQuasisimple
  let Z := R ⧸ pCore 2 R
  have hproper : pCore 2 R ≠ ⊤ := by
    intro he
    have hp : IsPGroup 2 R := by
      exact pCore_isPGroup.of_equiv ((MulEquiv.subgroupCongr he).trans topEquiv)
    let : Group.IsNilpotent R := hp.isNilpotent
    exact Group.IsPerfect.not_isSolvable R inferInstance
  let : Nontrivial Z := QuotientGroup.nontrivial_iff.mpr hproper
  let : IsQuasisimple Z := IsQuasisimple.of_surjective
    (QuotientGroup.mk' (pCore 2 R)) (QuotientGroup.mk'_surjective _)
  let e := q.solvableResidualMap.pCoreQuotientEquiv
    (q.solvableResidualMap_surjective hq) (q.solvableResidualMap_ker_isPGroup hk)
  let : IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) :=
    IsQuasisimple.of_mulEquiv e.symm
  refine ⟨inferInstance,⟨?_⟩⟩
  exact (QuotientGroup.congr _ _ e (FixedElementary.map_center e)).trans
    ((IsQuasisimple.centralQuotientEquiv (QuotientGroup.mk' (pCore 2 R))
      (QuotientGroup.mk'_surjective _)).symm.trans c.quotientCenterEquiv)

/-- Restrict the original covering map to a point subgroup, keeping the
literal commuting square and the full kernel of the preceding quotient. -/
theorem residual_central_quotient_of_factorization
    {Z : Type*} [Group Z]
    (q : C →* Y) (hq : IsPGroup 2 q.ker)
    (k : Y →* Z) (hk : k.ker ≤ center Y)
    (f : C →* X) (hf : Function.Surjective f)
    (j : X →* Z) (hj : Function.Injective j)
    (hcomm : ∀ c, k (q c) = j (f c)) :
    IsQuasisimple (solvableResidual C ⧸ pCore 2 (solvableResidual C)) ∧
      Nonempty (((solvableResidual C ⧸ pCore 2 (solvableResidual C)) ⧸
        center (solvableResidual C ⧸ pCore 2 (solvableResidual C))) ≃*
          (X ⧸ center X)) := by
  let r := q.rangeRestrict
  have hr : Function.Surjective r := q.rangeRestrict_surjective
  have hker : r.ker ≤ f.ker := by
    intro c hc
    apply hj
    rw [map_one,← hcomm]
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
  exact residual_central_quotient r hr (by
    change IsPGroup 2 q.rangeRestrict.ker
    rw [MonoidHom.ker_rangeRestrict]
    exact hq) g hgs hgc

end CFSG.Quasithin.Chapter8.MathieuShadowRows
