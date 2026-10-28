module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTrialityPlacement
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryG2Exclusion

/-!
# The triality component on the original binary paired plane

The canonical inner image has order sixteen and centralizer index at most
two in the image of the original component Sylow. The triality root calculation
makes this image central and forces the original field degree to be at
least four. The original component is centerless and relatively normal.
Centralization lifts to its actual Sylow, placing that Sylow in the full
core Q and making Q Sylow in KQ. The scalar Cartan action forces the original
Sylow normalizer to escape M = N_G(L).

This discharges the triality centralization, covering and placement premises of
7.7.6. Exclusion of the surviving exceptional components and final ambient
containment remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 7.7.6, printed p.706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryTrialityPlacement DoubledBinaryCoverPlacement
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- Triality root and Cartan facts on the same chosen plane and canonical inner map. -/
theorem sourceOrbit_binary_pairedPlane_triality_placement_with_marking
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
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              pPrimeCore 2 H = ⊥ ∧ D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧ Nat.card (inducedAutomizer K A) = 16 ∧
                ∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let R := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (R : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (R : Subgroup _)).index ≤ 2 ∧
                    (∀ n : ℕ, 2 ≤ n → Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K) →
                      4 ≤ n ∧ center K = ⊥ ∧ (K.subgroupOf H).Normal ∧
                      A ≤ centralizer ((P : Subgroup K).map K.subtype : Set G) ∧
                      (P : Subgroup K).map K.subtype ≤ Q ∧
                      (∃ S : Sylow 2 (K ⊔ Q : Subgroup G),
                        (S : Subgroup _).map (K ⊔ Q).subtype = Q) ∧
                      ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G)) ∧
              ((∃ n : ℕ, 2 ≤ n ∧
                Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K)) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_twisted_components_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let A := ⁅D.sourceOrbit,localResidual L U⁆
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,?_⟩
  intro H hBH hHC K hK
  obtain ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,hmodels⟩ :=
    hcomp H hBH hHC K hK
  refine ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,?_,hmodels⟩
  intro n hn hm
  let := hK.quasisimple
  have hn4 := triality_degree_ge_four hn hm _ j.range hjcard hQj hC
  have ho := triality_center_odd hn hm
  have hz := DoubledBinaryClassicalExclusion.component_centerless H K hK hodd ho
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro he
    have hh := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hh
    rw [he,Subgroup.card_bot] at hh
    omega
  have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
  have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
    ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
  have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
  have hnormal := triality_component_normal H K hK (hSQ.stronglyQuasithin 3 Nat.prime_three (by decide)) hz hn hm
  have hPC := centralizes_original_sylow K A ho hAN j hjact P
    (triality_centralizes hn hm _ j.range hQj hC)
  have hPQ := original_sylow_le_core K A U D.sourceOrbit (T : Subgroup G) Q hgen hQ
    (hK.1.trans hHC) P (hPS.trans inf_le_left) hPC
  have hQH : Q ≤ H := by
    rw [←hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
  have hout := DoubledBinaryCartan.normalizer_escape D.sourceOrbit U K A hAW (hK.1.trans hHC)
    hAN hquot j hjact P ((by decide : 6 < 15).trans_le
      (triality_normalizer_index hn hm _ j.range hjcard hQj hC))
  refine ⟨hn4,hz,hnormal,le_centralizer_iff.mp hPC,hPQ,
    core_sylow_join H K Q hK hQH (isPGroup_pCoreIn 2 _) P hPQ,?_⟩
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hout

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_triality_placement
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
          let S₀ := (T : Subgroup G) ⊓ centralizer (U : Set G)
          let A := ⁅D.sourceOrbit,localResidual L U⁆
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype =
              (T : Subgroup G) ⊓ centralizer (U : Set G)) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = Q ∧
          U ⊔ ⁅D.sourceOrbit,localResidual L U⁆ = D.sourceOrbit ∧
          Q.characteristicNormalizerClosure ≤ normalizer (L : Set G) ∧
          Nonempty (inducedAutomizer D.sourceOrbit (centralizer (U : Set G)) ≃* Equiv.Perm (Fin 3)) ∧
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              pPrimeCore 2 H = ⊥ ∧ D.sourceOrbit ⊓ centralizer (K : Set G) = U ∧
              ∃ hAN : A ≤ normalizer (K : Set G),
                A ⊓ centralizer (K : Set G) = ⊥ ∧ Nat.card (inducedAutomizer K A) = 16 ∧
                ∃ j : A →* K ⧸ center K, Function.Injective j ∧
                  (∀ a : A, (innerEquivCentralQuotient.symm (j a) : MulAut K) =
                    K.normalizerMonoidHom (inclusion hAN a)) ∧
                  Nat.card j.range = 16 ∧ IsElementaryAbelian 2 j.range ∧
                  ∃ P : Sylow 2 K, (P : Subgroup K).map K.subtype ≤ S₀ ∧
                    let R := P.mapSurjective (QuotientGroup.mk'_surjective (center K))
                    j.range ≤ (R : Subgroup _) ∧
                    ((centralizer (j.range : Set (K ⧸ center K))).subgroupOf
                      (R : Subgroup _)).index ≤ 2 ∧
                    (∀ n : ℕ, 2 ≤ n → Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K) →
                      4 ≤ n ∧ center K = ⊥ ∧ (K.subgroupOf H).Normal ∧
                      A ≤ centralizer ((P : Subgroup K).map K.subtype : Set G) ∧
                      (P : Subgroup K).map K.subtype ≤ Q ∧
                      (∃ S : Sylow 2 (K ⊔ Q : Subgroup G),
                        (S : Subgroup _).map (K ⊔ Q).subtype = Q) ∧
                      ¬ (normalizer (P : Set K)).map K.subtype ≤ normalizer (L : Set G)) ∧
              ((∃ n : ℕ, 2 ≤ n ∧
                Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K)) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_triality_placement_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
