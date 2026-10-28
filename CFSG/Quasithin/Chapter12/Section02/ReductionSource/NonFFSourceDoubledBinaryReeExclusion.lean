module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryReePlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryTrialityExclusion

/-!
# Excluding the final ordinary component on the chosen paired plane

For a remaining Ree component, the faithful canonical inner image of order
sixteen centralizes the original component Sylow. Its odd center lets this
centralization lift, placing that same Sylow in the full core Q. The actual
split torus makes the component relatively normal. The core then acts by
inner automorphisms, so the original Sylow normalizer normalizes Q and hence
normalizes the doubled orbit. Its Cartan centralizer index is at least seven,
contradicting the literal paired-plane S₃ quotient, whose order is six.

Together with the earlier component exclusions this eliminates every ordinary
component in each local-base overgroup on this same plane. The companion
characteristic-two module combines this with odd-core elimination. Ambient
containment and the final non-FF contradiction remain with this task.
Source: Aschbacher–Smith 7.7.6, printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryReePlacement
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Every local-base overgroup on this actual paired plane is component-free. -/
theorem sourceOrbit_binary_pairedPlane_no_components_with_marking
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          DoubledBinaryOmega.HasMarking D.sourceOrbit L E ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, ¬ IsComponentIn K H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_ree_components_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let A := ⁅D.sourceOrbit,localResidual L U⁆
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hQne : Q ≠ ⊥ := by
    intro hh
    have hUQ : U ≤ Q := hUW.trans (D.sourceOrbit_core_normalizer h).1
    exact hU (le_bot_iff.mp (hh ▸ hUQ))
  have hNQ : normalizer (Q : Set G) ≤ normalizer (D.sourceOrbit : Set G) := by
    rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
    exact (normalizer_le_characteristicNormalizerClosure_self Q hQne).trans hctl
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,m,hm,hree⟩ :=
    hcomp H hBH hHC K hK
  let := hK.quasisimple
  have ho := ree_center_odd hm hree
  have hz := DoubledBinaryClassicalExclusion.component_centerless H K hK hodd ho
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  have hnormal := ree_component_normal H K hK
    hSQ.stronglyQuasithin hz hm hree
  have hPC := DoubledBinaryCoverPlacement.centralizes_original_sylow K A ho hAN j hjact P
    (ree_centralizes hm hree _ j.range hQj hC)
  have hPQ := DoubledBinaryCoverPlacement.original_sylow_le_core K A U D.sourceOrbit
    (T : Subgroup G) Q hgen hQ (hK.1.trans hHC) P (hPS.trans inf_le_left) hPC
  have hQH : Q ≤ H := by
    rw [←hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
  have hQN : Q ≤ normalizer (K : Set G) := hQH.trans
    ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnormal)
  have hsmall := (ree_normalizer_le_core_normalizer K Q (isPGroup_pCoreIn 2 _)
    hQN P hPQ hm hree).trans hNQ
  have hjne : j.range ≠ ⊥ := by
    intro he
    rw [he,Subgroup.card_bot] at hjcard
    omega
  exact DoubledBinaryCartan.normalizer_escape D.sourceOrbit U K A hAW (hK.1.trans hHC)
    hAN hquot j hjact P ((by decide : 6 < 7).trans_le
      (ree_normalizer_index hm hree _ j.range hjne hQj hC)) hsmall

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_no_components
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (hnon : ¬ IsFFModule D.sourceOrbitNormalizerRepresentation)
    (F : BinaryField) (hF : F.degree = 1)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (linearNatural F 3))) :
    ∃ t : G, t ∈ (T : Subgroup G) ∧ t ∉ normalizer (V : Set G) ∧
      ∃ E : Additive D.sourceOrbit ≃ₗ[ZMod 2] NaturalDual.Space,
        (∀ w, (E w).2 = 0 ↔ (w.toMul : G) ∈ V) ∧
        (∀ w, (E w).1 = 0 ↔ (w.toMul : G) ∈ V.map (MulAut.conj t).toMonoidHom) ∧
        ∃ v : Vector, ∃ f : Module.Dual (ZMod 2) Vector, f v = 1 ∧
          let U := ambientPlane D.sourceOrbit E v f
          let B := localBase L (T : Subgroup G) U
          let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, ¬ IsComponentIn K H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_no_components_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
