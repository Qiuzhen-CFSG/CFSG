module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.TorusModels.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import Theory.GroupTheory.PCoreAbelianQuotient

/-!
# Abelian Borel quotients for all higher-field models

For each of the seven actual carriers in `TorusModels.Assembly.Model`,
we prove [R,R] ≤ O₂(R), where R = O²(N_D(S)) for the specified Sylow
2-subgroup S. The concrete quotient equivalences identify R/O₂(R) with
field units, a product of two unit groups, or the appropriate scalar
quotient. The special and projective linear and unitary carriers remain
distinct. In the unitary cases the matrix field has order (2ⁿ)², with
fixed-field order 2ⁿ.

The local Borel B maps to the embedded intrinsic residual by
`borel_star_intrinsic`. Its commutator containment lifts through the
restriction of H → H/O₂(H), whose kernel is a two-group. This does not
identify K* with K/O₂(K), and uses only normality of K* in H*.

The result discharges the abelian-containment input of
`CentralizingCalculation.markedActor_commutatorOrder_le_three_of_index`.
The remaining index and local action calculations belong to that source
assembly. Source: Aschbacher–Smith, proof of 13.8.20, printed p.954
(PDF p.971).
-/

public section

open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.ModelBorel
open TorusModels TorusModels.Assembly
universe u v
variable {D : Type u} [Group D]

private theorem commutator_le_of_quotientEquiv (B : Subgroup D)
    {A : Type*} [Group A] [IsMulCommutative A] (e : (B ⧸ pCore 2 B) ≃* A) :
    ⁅B, B⁆ ≤ B.pCoreIn 2 := by
  apply (commutator_self_le_pCoreIn_iff 2 B).mpr
  exact ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm'])⟩⟩

private theorem residual_commutator_transport [Finite D] {E : Type*} [Group E]
    (e : D ≃* E)
    (h : ∀ S : Sylow 2 E, ⁅residualAt S, residualAt S⁆ ≤ (residualAt S).pCoreIn 2)
    (S : Sylow 2 D) : ⁅residualAt S, residualAt S⁆ ≤ (residualAt S).pCoreIn 2 := by
  apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
  rw [map_commutator, map_pCoreIn_of_injective 2 _ e.toMonoidHom e.injective,
    residualAt_map]
  exact h _

/-- Every actual higher-field Borel residual has abelian quotient by its two-core. -/
theorem model_residual_commutator_le_twoCore [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model.{u,v} D n unitary four) (hn : 1 < n) (S : Sylow 2 D) :
    ⁅residualAt S, residualAt S⁆ ≤ (residualAt S).pCoreIn 2 := by
  cases model with
  | linearTwo F hF e _ =>
    apply residual_commutator_transport e (fun S => ?_) S
    rw [residualAt, LinearTwo.borelResidual_eq hn hF]
    let eB := Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.sylowNormalizerEquiv F S
    exact commutator_le_of_quotientEquiv _
      ((QuotientGroup.congr _ _ eB (pCore_map_iso 2 eB)).trans
        (Matrix.ProjectiveSpecialLinearGroup.EvenBorelResidual.quotientTorusEquiv F hF))
  | specialLinearThree F hF e _ =>
    exact residual_commutator_transport e (fun S => commutator_le_of_quotientEquiv _
      (LinearThree.special_residual_quotientEquiv hF hn S)) S
  | projectiveLinearThree F hF e _ =>
    let : IsMulCommutative ((Fˣ × Fˣ) ⧸ Matrix.PSL3.CartanActions.BorelQuotient.cubicScalars F) :=
      ⟨⟨fun x y => Quotient.inductionOn₂' x y
        fun a b => congrArg QuotientGroup.mk (mul_comm a b)⟩⟩
    exact residual_commutator_transport e (fun S => commutator_le_of_quotientEquiv _
      (LinearThree.projective_residual_quotientEquiv hF hn S)) S
  | specialUnitaryThree E J hE hconj e _ =>
    apply residual_commutator_transport e (fun S => ?_) S
    rw [residualAt, UnitaryThree.su_borelResidual_eq J n hn hE hconj]
    obtain ⟨_, _, _, q, _⟩ := UnitaryThree.su_borel_quotient J n (by omega) hE hconj S
    exact commutator_le_of_quotientEquiv _ q
  | projectiveUnitaryThree E J hE hconj e _ =>
    apply residual_commutator_transport e (fun S => ?_) S
    rw [residualAt, UnitaryThree.psu_borelResidual_eq J n hn hE hconj]
    obtain ⟨_, _, _, q, _⟩ := UnitaryThree.psu_borel_quotient J n (by omega) hE hconj S
    exact commutator_le_of_quotientEquiv _ q
  | symplecticFour F hF e _ =>
    exact residual_commutator_transport e (fun S => commutator_le_of_quotientEquiv _
      (Theory.SpecificGroups.SymplecticFour.EvenBorelTorus.residualAtQuotientEquiv
        hF (by omega) S)) S
  | g2 F hF e _ =>
    exact residual_commutator_transport e (fun S => commutator_le_of_quotientEquiv _
      (G2.residualBorelAtQuotientEquiv hF hn S)) S

/-- The intrinsic quotient formulation of the uniform model calculation. -/
theorem model_residual_quotient_abelian [Finite D] {n : ℕ} {unitary four : Bool}
    (model : Model.{u,v} D n unitary four) (hn : 1 < n) (S : Sylow 2 D) :
    IsMulCommutative (residualAt S ⧸ pCore 2 (residualAt S)) :=
  (commutator_self_le_pCoreIn_iff 2 _).mp
    (model_residual_commutator_le_twoCore model hn S)

variable {G : Type u} [Group G] [Finite G]

/-- The source lift B has abelian quotient by its intrinsic two-core, using
its actual image in H/O₂(H) and the two-group kernel of the restricted map. -/
theorem borel_commutator_le_twoCore
    (H K T : Subgroup G) [(Source.starImage H K).Normal]
    (hKH : K ≤ H) (hT : Chapter1.IsSylowIn 2 T H)
    {n : ℕ} {unitary four : Bool}
    (model : Model.{u,v} (Source.starImage H K) n unitary four) (hn : 1 < n) :
    ⁅borel H K T hKH hT, borel H K T hKH hT⁆ ≤ (borel H K T hKH hT).pCoreIn 2 := by
  let B := borel H K T hKH hT
  have hBH : B ≤ H := (borel_le_component H K T hKH hT).trans hKH
  have hR := model_residual_commutator_le_twoCore model hn (sourceSylow H K T hT)
  have hstar : ⁅Source.starImage H B, Source.starImage H B⁆ ≤
      (Source.starImage H B).pCoreIn 2 := by
    rw [borel_star_intrinsic H K T hKH hT, ← map_commutator,
      ← map_pCoreIn_of_injective 2 _ _ (Source.starImage H K).subtype_injective]
    exact map_mono hR
  have hker : IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have h := commutator_self_le_pCoreIn_of_map
    (QuotientGroup.mk' (pCore 2 H)) hker (B.subgroupOf H) hstar
  have hm := map_mono (f := H.subtype) h
  rwa [map_commutator, map_pCoreIn_of_injective 2 _ H.subtype H.subtype_injective,
    map_subgroupOf_eq_of_le hBH] at hm

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.ModelBorel
