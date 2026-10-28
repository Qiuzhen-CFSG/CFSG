module
public import Theory.SpecificGroups.ClassicalOrthogonal.BinaryGeneration
public import CFSG.Quasithin.ChapterG.Section12.RecognitionQuadraticRadicals
public import CFSG.Quasithin.ChapterG.Section12.ResidualModels
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup.Transport

/-!
# Orthogonal residual recognition in the nontransitive G.12 branch

Each singular Siegel generator is an element of the literal point radical.
Equality of the source and full orthogonal point radicals therefore puts the
whole elementary orthogonal image in the source group. Binary orthogonal
generation puts the full orthogonal solvable residual there as well.
Perfectness of that residual and monotonicity give equality of embedded
residuals, without assuming that the elementary group is perfect.

The nontransitive orbit construction supplies the form and every radical
equality. Thus in dimensions at least five this recognition branch is complete
for the original linear action. The terminal consumer uses degree-four
orthogonal exclusion for the omitted dimension and retains the separate
transitive recognition and orthogonal model exclusions with its existing owner.

Source: Aschbacher--Smith G.12.10, printed p.373, and the G.10.15
central-kernel application, printed p.363.
-/

public noncomputable section
open Subgroup Module Theory.AlgebraicGroup ClassicalOrthogonal
open ClassicalOrthogonal.Quadratic
namespace CFSG.Quasithin.ChapterG.Section12
section CoordinateSpace
variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {D : Subgroup (V ≃ₗ[ZMod 2] V)}

private theorem isometry_preserves_polar (q : QuadraticForm (ZMod 2) V) :
    q.isometrySubgroup ≤ formStabilizer q.polarBilin := by
  intro a ha x y
  have h := (QuadraticMap.mem_isometrySubgroup q a).mp ha
  change q (a x+a y)-q (a x)-q (a y)=q (x+y)-q x-q y
  rw [← map_add,h,h,h]

/-- Every singular Siegel generator belongs to the literal orthogonal point
radical at its original direction. -/
theorem siegel_mem_pointRadical (q : QuadraticForm (ZMod 2) V)
    (u w : V) (hu : q u=0) (huw : q.polarBilin u w=0) :
    (siegelElement q u w hu huw).val ∈ pointRadical q.isometrySubgroup q.polarBilin u := by
  apply (mem_pointRadical_iff (isometry_preserves_polar q)).mpr
  refine ⟨?_,siegel_fix q u w hu huw,?_⟩
  · exact (QuadraticMap.mem_isometrySubgroup q _).mpr (siegel_preserves q u w · hu huw)
  · intro x hx
    have hxu : q.polarBilin x u=0 := (polar_swap q x u).trans hx
    change siegel q u w x-x∈Submodule.span (ZMod 2) {u}
    simp only [siegel,hxu,zero_smul,mul_zero,sub_zero]
    have he : x+q.polarBilin x w • u-x=q.polarBilin x w • u := by abel
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)

/-- Equality of all singular point radicals puts the actual elementary
orthogonal image inside the original linear group. -/
theorem elementary_le_of_pointRadicals
    (q : QuadraticForm (ZMod 2) V)
    (hr : ∀ u : V,u≠0 → q u=0 →
      pointRadical D q.polarBilin u=pointRadical q.isometrySubgroup q.polarBilin u) :
    (elementarySubgroup q).map (quadraticIsometrySubgroup q).subtype ≤ D := by
  apply (Subgroup.map_le_iff_le_comap).mpr
  apply (Subgroup.closure_le _).mpr
  rintro a ⟨u,w,hu,huw,rfl⟩
  change (siegelElement q u w hu huw).val∈D
  by_cases hu0 : u=0
  · have he : (siegelElement q u w hu huw).val=1 := by
      ext x
      change siegel q u w x=x
      simp [siegel,hu0]
    rw [he]
    exact D.one_mem
  · have hm := siegel_mem_pointRadical q u w hu huw
    rw [← hr u hu0 hu] at hm
    exact hm.1

end CoordinateSpace

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable [FiniteDimensional (ZMod 2) V] {D : Subgroup (V ≃ₗ[ZMod 2] V)}

/-- The G.12 quadratic branch identifies solvable residuals as subgroups
of the original linear group. Coordinate transport preserves every original
point radical and removes the universe restriction of the elementary generators. -/
theorem embeddedResidual_eq_orthogonal_of_pointRadicals (q : QuadraticForm (ZMod 2) V) (hnd : q.polarBilin.Nondegenerate)
    (hd : 5 ≤ finrank (ZMod 2) V) (hD : D ≤ q.isometrySubgroup)
    (hr : ∀ u : V, u ≠ 0 → q u = 0 →
      pointRadical D q.polarBilin u = pointRadical q.isometrySubgroup q.polarBilin u) :
    embeddedResidual D = embeddedResidual q.isometrySubgroup := by
  let W := Fin (finrank (ZMod 2) V) → ZMod 2
  let e : W ≃ₗ[ZMod 2] V := (Module.finBasis (ZMod 2) V).equivFun.symm
  let Q : QuadraticForm (ZMod 2) W := q.comp e.toLinearMap
  let eq : Q.IsometryEquiv q := { toLinearEquiv := e, map_app' := fun _ => rfl }
  have hO : quadraticIsometrySubgroup Q = Q.isometrySubgroup := by
    ext a
    exact (mem_quadraticIsometrySubgroup Q a).trans (QuadraticMap.mem_isometrySubgroup Q a).symm
  let j : quadraticIsometrySubgroup Q ≃* q.isometrySubgroup :=
    (MulEquiv.subgroupCongr hO).trans eq.isometrySubgroupCongr
  let f : quadraticIsometrySubgroup Q →* (V ≃ₗ[ZMod 2] V) := q.isometrySubgroup.subtype.comp j.toMonoidHom
  have hf (a : quadraticIsometrySubgroup Q) (x : V) : f a x = e (a.val (e.symm x)) := by
    change (eq.isometrySubgroupCongr ((MulEquiv.subgroupCongr hO) a)).val x = _
    rw [QuadraticMap.IsometryEquiv.isometrySubgroupCongr_apply]
    rfl
  have hp (x y : W) : Q.polarBilin x y = q.polarBilin (e x) (e y) := by
    simp only [Q,QuadraticMap.polarBilin_comp,LinearMap.compl₁₂_apply,LinearEquiv.coe_coe]
  have hn : Q.polarBilin.Nondegenerate := by
    constructor
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply hnd.1
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      exact (hp x y).symm.trans (hx y)
    · intro x hx
      apply e.injective
      rw [map_zero]
      apply hnd.2
      intro y
      obtain ⟨y,rfl⟩ := e.surjective y
      exact (hp y x).symm.trans (hx y)
  have hgen : (elementarySubgroup Q).map f ≤ D := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro a ⟨u,w,hu,huw,rfl⟩
    change f (siegelElement Q u w hu huw) ∈ D
    by_cases hu0 : u = 0
    · have he : siegelElement Q u w hu huw = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change siegel Q u w x = x
        simp [siegel,hu0]
      rw [he,map_one]
      exact D.one_mem
    have heu : e u ≠ 0 := fun he => hu0 (e.injective (he.trans e.map_zero.symm))
    have hqe : q (e u)=0 := hu
    have hm : f (siegelElement Q u w hu huw) ∈ pointRadical q.isometrySubgroup q.polarBilin (e u) := by
      apply (mem_pointRadical_iff (by
        intro a ha x y
        have hh := (QuadraticMap.mem_isometrySubgroup q a).mp ha
        change q (a x+a y)-q (a x)-q (a y)=q (x+y)-q x-q y
        rw [← map_add,hh,hh,hh])).mpr
      refine ⟨(j (siegelElement Q u w hu huw)).property,?_,?_⟩
      · rw [hf,e.symm_apply_apply]
        exact congrArg e (siegel_fix Q u w hu huw)
      · intro x hx
        have hx' : Q.polarBilin u (e.symm x)=0 := by rw [hp,e.apply_symm_apply,hx]
        have hmove := (siegel_mem_pointRadical Q u w hu huw).2.2.2 (e.symm x) hx'
        obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmove
        apply Submodule.mem_span_singleton.mpr
        refine ⟨c,?_⟩
        rw [hf]
        have he := congrArg e hc
        simpa only [map_smul,map_sub,e.apply_symm_apply] using he
    rw [← hr (e u) heu hqe] at hm
    exact hm.1
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun a : V ≃ₗ[ZMod 2] V => (a : V → V)) DFunLike.coe_injective
  let : Finite (quadraticIsometrySubgroup Q) := Finite.of_injective j j.injective
  have hle : embeddedResidual q.isometrySubgroup ≤ D := by
    rw [embeddedResidual,← map_solvableResidual_eq j.toMonoidHom j.surjective,map_map]
    exact (map_mono (ClassicalOrthogonal.BinaryGeneration.solvableResidual_le_elementary
      Q hn (by simpa only [← e.finrank_eq] using hd))).trans hgen
  apply le_antisymm (Subgroup.map_solvableResidual_mono hD)
  let : Group.IsPerfect ((solvableResidual q.isometrySubgroup).map q.isometrySubgroup.subtype) :=
    Group.IsPerfect.map q.isometrySubgroup.subtype
  exact Subgroup.le_map_solvableResidual_of_isPerfect _ _ hle


/-- In degree at least five the nontransitive G.12 branch has exactly the
full orthogonal group's embedded solvable residual, with the original polar form. -/
theorem GoodVector.residual_orthogonal_of_not_transitive
    {B : LinearMap.BilinForm (ZMod 2) V} {hB : B.IsAlt} {v : V}
    (h : GoodVector D B hB v) (hnd : B.Nondegenerate)
    (hD : D≤formStabilizer B) (hirr : Irreducible D)
    (hd : 5≤finrank (ZMod 2) V)
    (hnt : ¬∀ x : V,x≠0 → ∃ a∈D,a v=x) :
    ∃ q : QuadraticForm (ZMod 2) V, q.polarBilin=B ∧
      D≤q.isometrySubgroup ∧ embeddedResidual D=embeddedResidual q.isometrySubgroup := by
  obtain ⟨q,hq,hO,hs⟩ := h.exists_quadratic_of_not_transitive hnd hD hirr hnt
  refine ⟨q,hq,hO,embeddedResidual_eq_orthogonal_of_pointRadicals q (hq.symm ▸ hnd) hd hO ?_⟩
  intro x hx hxq
  obtain ⟨a,ha,hax⟩ := ((hs x).mp hxq).resolve_left hx
  have hg := h.conjugate hD ha
  rw [hax] at hg
  rw [hq]
  exact hg.pointRadical_eq_orthogonal hnd q hq hO hxq (by omega)

end CFSG.Quasithin.ChapterG.Section12
