module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource.FourLift.LocalComponent
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.Levi.FourComponent
public import Theory.GroupTheory.CComponent.MarkedTwoCoreImage

/-!
# The marked degree-four component in the source family

Enlarge the marked single-node parabolic by its adjacent node and take
its full preimage Y in H. The local component construction proves
Y = K₁T with L₁ ≤ K₁ ≤ K and Y in the literal source family Hz.
The solvable-kernel component correspondence identifies the image of K₁
with the component selected by four_single_node_component. The final
formula retains the fixed modelLiftMap, the enlarged parabolic quotient,
and its geometric PSL₃(2) equivalence on every K₁ representative.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.8.25,
printed p.959 (PDF p.976), the local construction in the T_K = T case.
This is a conditional lifting theorem: the source assembly still supplies
the three flag/residual markings, two-perfectness, the cubic quotient,
and the genuine theta identity. No placement of these markings is asserted
here, and no equality H ∩ M = L₁T or containment T ≤ K is assumed.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource
variable {G : Type*} [Group G] [Finite G]

/-- Lift the selected degree-four Levi component into the actual source family,
retaining its image and the geometric quotient map on every representative. -/
theorem four_source_local_component
    (H K L₁ T G₁ M : Subgroup G)
    (hH : H ∈ Source.Hz L₁ T G₁ M)
    (hKH : K ≤ H) (_hKcomponent : (K.subgroupOf H).IsCComponent)
    (hKn : (K.subgroupOf H).Normal) (hgen : H = K ⊔ T) (_hLK : L₁ ≤ K)
    (hSyl : Chapter1.IsSylowIn 2 T H)
    (hL : IsPPerfect 2 L₁) (hcard : Nat.card (L₁ ⧸ pCore 2 L₁) = 3)
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (eH : Source.Hstar H ≃* LinearGroup 4) (b : Basis 3) (i : Fin 3)
    (hbase : (Source.starImage H (L₁ ⊔ T)).map eH.toMonoidHom = fourParabolic b {i})
    (hresidual : (Source.starImage H L₁).map eH.toMonoidHom = fourNodeResidual b i)
    (hflag : (Source.starImage H T).map eH.toMonoidHom = cutStabilizer b Set.univ) :
    let P := fourParabolic b {i, fourAdjacentNode i}
    let Y := modelLift H eH P
    ∃ (D : Subgroup (LinearGroup 4)) (_hDP : D ≤ P),
      fourNodeResidual b i ≤ D ∧ (D.subgroupOf P).IsCComponent ∧
      (Source.starImage H T).map eH.toMonoidHom ≤ normalizer (D : Set (LinearGroup 4)) ∧
      (Source.starImage H L₁).map eH.toMonoidHom ≤ D ∧
      ∃ (K₁ : Subgroup G) (hK₁Y : K₁ ≤ Y),
        K₁ ≤ K ∧ L₁ ≤ K₁ ∧ T ≤ normalizer (K₁ : Set G) ∧
        Y = K₁ ⊔ T ∧ (K₁.subgroupOf (K₁ ⊔ T)).IsCComponent ∧
        K₁ ⊔ T ∈ Source.Hz L₁ T G₁ M ∧
        (K₁.subgroupOf Y).map (modelLiftMap H eH P) = D.subgroupOf P ∧
        ∃ eK : (K₁ ⧸ pCore 2 K₁) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2),
          ∀ k : K₁, eK (QuotientGroup.mk' _ k) = fourEnlargedQuotientEquiv b i
            (QuotientGroup.mk' _ (modelLiftMap H eH P (⟨k.val, hK₁Y k.property⟩ : Y))) := by
  let : Finite (LinearGroup 4) := Finite.of_injective
    (fun g : LinearGroup 4 => (g : Space 4 → Space 4)) DFunLike.coe_injective
  let P := fourParabolic b {i, fourAdjacentNode i}
  let Y := modelLift H eH P
  obtain ⟨_, hsmall, D, hDP, hDR, hDcomp, hDT, eD, heD⟩ := four_single_node_component b i
  have hbaseY : L₁ ⊔ T ≤ Y := by
    apply (le_modelLift_iff H (L₁ ⊔ T) hH.1.2 eH P).mpr
    rw [hbase]
    exact hsmall.le
  have hcoreY : Source.QH H ≤ Y := twoCore_le_liftStar H _
  let eY := (modelLiftQuotientEquiv H eH P).trans (fourEnlargedQuotientEquiv b i)
  obtain ⟨K₁, hK₁Y, hK₁K, hLK₁, hn, hjoin, hC, hHz, eK, heK⟩ :=
    source_component_of_linear_three_quotient H K L₁ T G₁ M Y hH hKH hKn hgen hSyl
      (modelLift_le H eH P) hbaseY hcoreY hL hcard htheta eY
  have himage : (K₁.subgroupOf Y).map (modelLiftMap H eH P) = D.subgroupOf P := by
    let a := subgroupOfEquivOfLe hK₁Y
    let d := subgroupOfEquivOfLe hDP
    let qa := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
    let qd := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
    apply cComponent_map_eq_of_twoCore_formulas (modelLiftMap H eH P)
      (modelLiftMap_surjective H eH P) (modelLiftMap_kernel_isTwoGroup H eH P)
      (K₁.subgroupOf Y) (D.subgroupOf P) hC hDcomp
      (qa.trans eK) (qd.trans eD) (fourEnlargedQuotientEquiv b i)
    · intro c
      exact heK (a c)
    · intro c
      exact heD (d c)
  refine ⟨D, hDP, hDR, hDcomp, ?_, ?_, K₁, hK₁Y, hK₁K, hLK₁,
    (le_sup_right.trans hbaseY).trans hn, hjoin, ?_, ?_, himage, eK, ?_⟩
  · rw [hflag]
    simpa only [fourFlagSylow_coe] using hDT
  · rw [hresidual]
    exact hDR
  · rw [← hjoin]
    exact hC
  · rw [← hjoin]
    exact hHz
  · intro k
    exact heK k
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OrdinarySource

end
