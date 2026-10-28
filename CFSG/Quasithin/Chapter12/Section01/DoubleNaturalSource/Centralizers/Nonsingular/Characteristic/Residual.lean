module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Nonsingular.Characteristic.Odd
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.ModelConstruction.Layer
public import Theory.GroupTheory.CComponent.PrimeCoreDichotomy
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceStabilizers
public import Theory.GroupTheory.PCoreActionSplitting

/-!
# The literal nonsingular residual is a local C-component

The residual action has two-group kernel, inherited from the original
component action. Its actual image is H.9's L_(n-1)(2), whose two-core is
trivial. Thus the kernel is exactly O₂(L_w), and the first isomorphism
theorem identifies L_w/O₂(L_w) with that source model. Two-perfectness
and local normality make L_w a C-component of M_w.

The final chosen-module application puts L_w in the genuine Chapter 1
local family at C_T(w). Its nontrivial two-core contains the central
involution w. C_T(w) is only asserted Sylow in M_w and L_w C_T(w).
Source: Aschbacher--Smith H.9.1(4) and 12.1.1, printed pp.389,788.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
open Subgroup Theory.GroupTheory
open BinaryNaturalDual.ModelOrbits.AutomorphismModel BinaryLinear.OuterCyclic
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  {B : DoubledBranch T L V n}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
namespace SourceModel
variable (S : B.SourceModel)

omit [Finite G] [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))] in
private theorem residual_action_kernel_twoGroup (w : componentOrbit V (T : Subgroup G)) :
    IsPGroup 2 (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).ker := by
  let i := inclusion ((B.pointResidual_le w).trans inf_le_left)
  have he : (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).ker =
      (pCore 2 L).comap i := by
    rw [← B.componentToActionQuotient_ker]
    ext r
    rfl
  rw [he]
  exact pCore_isPGroup.comap_of_injective i (inclusion_injective _)

include S

/-- The exact residual action kernel and its original two-core quotient. -/
theorem nonsingular_residual_kernel_and_quotient
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    (B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))).ker =
      pCore 2 (B.pointResidual w) ∧
    Nonempty ((B.pointResidual w ⧸ pCore 2 (B.pointResidual w)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin (n-1)) (ZMod 2)) := by
  let q := B.actionProjection.comp (inclusion (B.pointResidual_le_normalizer w))
  have hwS : S.setup.quadratic (Additive.ofMul w) = 1 := by rwa [S.quadratic_eq]
  obtain ⟨e₀⟩ := (ChapterH.NaturalDual.SourceSetup.nonsingular_structure S.setup hwS).2.1
  let e := (MulEquiv.subgroupCongr (S.pointResidual_action_range w)).trans e₀
  have hn : 3 ≤ n-1 := by have := B.degree; omega
  let eL := e.trans (projectiveEquivLinear (by omega : 0 < n-1))
  let : IsQuasisimple (LinearGroup (n-1)) := IsQuasisimple.of_mulEquiv
    (innerEquiv (by omega : 0 < n-1)).symm (hG := (inner_isComponent hn).2)
  let : Finite (LinearGroup (n-1)) := Finite.of_equiv q.range eL.toEquiv
  have hcore : pCore 2 q.range = ⊥ := by
    apply map_injective (f := eL.toMonoidHom) eL.injective
    rw [pCore_map_iso,Subgroup.map_bot]
    exact bot_unique ((IsQuasisimple.pCore_le_center (G := LinearGroup (n-1)) 2).trans_eq
      (linear_center_eq_bot (by omega : 0 < n-1)))
  have hk : q.ker = pCore 2 (B.pointResidual w) :=
    q.ker_eq_pCore_of_range_core_eq_bot 2 (residual_action_kernel_twoGroup (B := B) w) hcore
  refine ⟨hk,⟨?_⟩⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hk).symm.trans
    (QuotientGroup.quotientKerEquivRange q)).trans e

/-- Relative normality and the actual simple quotient make L_w a C-component of M_w. -/
theorem nonsingular_residual_local_cComponent
    (w : componentOrbit V (T : Subgroup G)) (hw : B.quadratic (Additive.ofMul w) = 1) :
    ((B.pointResidual w).subgroupOf (B.localPointCentralizer w)).IsCComponent := by
  let R := B.pointResidual w
  let M := B.localPointCentralizer w
  have hRM : R ≤ M := le_inf (B.pointResidual_le_normalizer w)
    ((B.pointResidual_le w).trans inf_le_right)
  obtain ⟨e⟩ := (S.nonsingular_residual_kernel_and_quotient w hw).2
  have hn : 3 ≤ n-1 := by have := B.degree; omega
  let : IsQuasisimple (LinearGroup (n-1)) := IsQuasisimple.of_mulEquiv
    (innerEquiv (by omega : 0 < n-1)).symm (hG := (inner_isComponent hn).2)
  let : IsQuasisimple (R ⧸ pCore 2 R) := IsQuasisimple.of_mulEquiv
    (e.trans (projectiveEquivLinear (by omega : 0 < n-1))).symm
  have ht := isCComponent_top_of_isPPerfect_of_quasisimple_quotient
    (pCore 2 R) pCore_isPGroup (B.pointResidual_isPPerfect w)
  let E := R.subgroupOf M
  let eR := (subgroupOfEquivOfLe hRM).symm
  have htE : (⊤ : Subgroup E).IsCComponent := by
    simpa only [map_top_of_surjective eR.toMonoidHom eR.surjective] using ht.map_equiv eR
  have hnE : E.Normal := normal_subgroupOf_of_le_normalizer
    (B.localPointCentralizer_normalizes_residual w)
  have hh := htE.map_subtype hnE.isSubnormal
  simpa only [← MonoidHom.range_eq_map,range_subtype] using hh

end SourceModel
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch

namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The literal nonsingular residual belongs to the Chapter 1 local family
at C_T(w), including the nontrivial-core clause. The Sylow assertion remains
relative to C_M(w); none is asserted for C_G(w). -/
theorem doubleNatural_adapted_residual_mem_localFamily
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    {n : ℕ} (B : DoubledBranch T L V n) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), B.AdaptedPoint S w →
      B.pointResidual w ∈ Chapter1.LIn (B.pointCentralizer w) (B.pointSylow w) := by
  let := D.doubledOrbit_elementary h
  intro S w hw
  let R := B.pointResidual w
  let J := R ⊔ B.pointSylow w
  have hRM : R ≤ B.localPointCentralizer w :=
    le_inf (B.pointResidual_le_normalizer w) ((B.pointResidual_le w).trans inf_le_right)
  have hPM : B.pointSylow w ≤ B.localPointCentralizer w :=
    le_inf (inf_le_left.trans D.sylow_normalizes_component) inf_le_right
  have hJM : J ≤ B.localPointCentralizer w := sup_le hRM hPM
  refine ⟨(B.pointResidual_le w).trans inf_le_right,
    (S.nonsingular_residual_local_cComponent w hw.nonsingular).subgroupOf_of_le
      le_sup_left hJM, hw.local_sylow.restrict le_sup_right hJM, ?_⟩
  have hw2 := D.doubleNatural_point_orderOf_two h B w hw.nonsingular
  have hp : IsPGroup 2 (zpowers (w : G)) :=
    (IsElementaryAbelian.isPGroup 2 (componentOrbit V (T : Subgroup G))).to_le
      (zpowers_le.mpr w.property)
  have hwJ : zpowers (w : G) ≤ J := zpowers_le.mpr (mem_sup_right
    ⟨(D.doubledOrbit_E322 h).le_sylow w.property,mem_centralizer_singleton_iff.mpr rfl⟩)
  have hJN : J ≤ normalizer (zpowers (w : G) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_order_two _ hw2]
    exact hJM.trans inf_le_right
  have hc : zpowers (w : G) ≤ J.pCoreIn 2 := le_pCoreIn_of_normalizes hp hwJ hJN
  intro he
  have hw1 : (w : G) = 1 := mem_bot.mp (he ▸ hc (mem_zpowers _))
  rw [hw1,orderOf_one] at hw2
  omega

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
