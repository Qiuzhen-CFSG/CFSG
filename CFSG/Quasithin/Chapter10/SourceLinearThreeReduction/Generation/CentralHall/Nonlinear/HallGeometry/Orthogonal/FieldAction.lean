module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Orthogonal.ScalarAction
public import Theory.Representation.OrthogonalFourMinusRankOne.AmbientActions.FieldLifts
public import Theory.GroupTheory.Hall.OddKernel

/-!
# Innerness of the original orthogonal Hall component action

The actual Hall action on the whole Hermitian moved module is linear over
its defining field. The field-lift calculation then makes its odd-order
component action inner. An odd Hall index extends the same kernel conclusion
to every odd element of H ∩ M normalizing L. In particular it is available
for the conjugate Hall actor associated to the other component.

No innerness or field-triviality premise is added to Context. The paired
quotient transport and norm-one placement remain with the central Hall
assembly owner, qt-d-10-nona5-central-hall-orders.
Source: Aschbacher--Smith 10.2.3, printed p.745.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02 Representation
open Representation.OrthogonalFourMinus.FiniteModel
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
local instance fieldActionBinaryAlgebra (n : ℕ) : Algebra (ZMod 2) (fixedField n) :=
  ZMod.algebra _ 2
local instance fieldActionBinaryModule (n : ℕ) [NeZero n] : Module (ZMod 2) (Space n) :=
  Module.compHom (Space n) (algebraMap (ZMod 2) (fixedField n))

theorem orthogonal_hall_component_inner
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))))) (b : B) :
    componentAction D c b ∈ MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  obtain ⟨η,_hη,hcomp,hlin⟩ := exists_orthogonal_hall_linear_action D c geometry n e d
  let E : Space n ≃ₗ[fixedField n] Space n := LinearEquiv.ofBijective
    { toFun := η b
      map_add' := map_add (η b)
      map_smul' := hlin b }
    (LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom b)).bijective
  let α := ((MulAut.congr e).toMonoidHom.comp (componentAction D c))
  have ho : Odd (orderOf (α b)) := (hall_odd D c).of_dvd_nat
    ((orderOf_map_dvd α b).trans (orderOf_dvd_natCard b))
  obtain ⟨g,hg⟩ := OrthogonalFourMinus.RankOne.AmbientActions.odd_linear_lift_inner n
    (α b) ho E (by
      intro a v
      obtain ⟨l,rfl⟩ := (e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L))) a
      change η b (SL2.BinarySmall.hermitian n (e (QuotientGroup.mk' (pCore 2 L) l)) v) =
        SL2.BinarySmall.hermitian n
          (e (componentAction D c b (e.symm (e (QuotientGroup.mk' (pCore 2 L) l))))) (η b v)
      rw [e.symm_apply_apply]
      exact hcomp b l v)
  refine ⟨e.symm g,?_⟩
  apply (MulAut.congr e).injective
  rw [MulAut.congr_conj,e.apply_symm_apply]
  exact hg.symm
include D c in
/-- The first-component field-kernel result holds for every odd element of
H ∩ M normalizing L, so it also applies to the conjugate of B by a Sylow
exchanger. The Hall index supplies this extension without new module data. -/
theorem orthogonal_odd_component_inner
    (geometry : ModuleGeometry D) (n : ℕ) [NeZero n]
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) (Field n))
    (d : BinaryConjugationSection L ⁅D.fullModule,L⁆ ⊥
      ((SL2.BinarySmall.hermitian n).comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))))
    (x : G) (hxH : x ∈ H) (hxM : x ∈ D.maximalLocal)
    (hxL : x ∈ normalizer (L : Set G)) (hxodd : Odd (orderOf x)) :
    normalizerPCoreQuotientAction L ⟨x,hxL⟩ ∈
      MulAut.innerSubgroup (L ⧸ pCore 2 L) := by
  let C := D.maximalLocal.subgroupOf H
  let j := H.subtype.comp C.subtype
  let J := (normalizer (L : Set G)).comap j
  have hBJ : B.subgroupOf C ≤ J := by
    intro b hb
    exact hall_normalizes_component D c (mem_map_of_mem H.subtype hb)
  let f : J →* normalizer (L : Set G) := (j.comp J.subtype).codRestrict _
    (fun x => x.property)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (L ⧸ pCore 2 L))
  let ψ := q.comp ((normalizerPCoreQuotientAction L).comp f)
  have hk : (B.subgroupOf C).subgroupOf J ≤ ψ.ker := by
    intro b hb
    let b' : B := ⟨b.val.val,hb⟩
    change q (componentAction D c b') = 1
    exact (QuotientGroup.eq_one_iff _).mpr
      (orthogonal_hall_component_inner D c geometry n e d b')
  let a : J := ⟨⟨⟨x,hxH⟩,hxM⟩,hxL⟩
  have ho : Odd (orderOf a) := by
    have he := orderOf_injective (j.comp J.subtype)
      (H.subtype_injective.comp (C.subtype_injective.comp J.subtype_injective)) a
    exact he.symm ▸ hxodd
  have he := Subgroup.OddHall.map_eq_one_of_odd_order_of_hall_le_ker
    ((B.subgroupOf C).subgroupOf J) (c.hall.subgroupOf hBJ) ψ hk a ho
  exact (QuotientGroup.eq_one_iff _).mp he
end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
