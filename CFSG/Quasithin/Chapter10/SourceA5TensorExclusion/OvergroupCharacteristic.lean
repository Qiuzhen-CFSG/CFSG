module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.OvergroupSylow
public import CFSG.Quasithin.Chapter1.Section02.ComponentDichotomy.Characteristic
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Characteristic two in the original tensor overgroup

The source line V₁ lies in O₂(H), so its L-orbit V₂ also lies there.
The bound C_T(V₂)≤T₁ therefore bounds the centralizer of O₂(H). A
Sylow-central involution in V₁ passes ambient even characteristic to H.
Consequently F*(H)=O₂(H), on the literal intrinsic subgroup H.

The source 9.2.2 geometry producing V₁, its central involution, and the
centralizer bound is kept explicit, as is the source 9.3.6 containment
V₁≤O₂(H). The Sylow premise is discharged by source 9.3.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
9.3.6, printed pp.733–734, using 1.1.4.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original tensor orbit and central involution give characteristic two. -/
theorem source_a5_outside_characteristicTwo_of_tensor_core
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H U : Subgroup G) (hcore : pCore 2 H ≠ ⊥)
    (hLH : L ≤ H)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hout : ¬ H ≤ D.maximalLocal)
    (hU : U ≤ H.pCoreIn 2)
    (hCT : (T : Subgroup G) ⊓ centralizer (componentOrbit U L : Set G) ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G))
    (z : G) (hz : orderOf z = 2) (hzU : z ∈ U)
    (hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t) :
    H ∈ Chapter1.He G ∧ generalizedFitting H = pCore 2 H := by
  have hs := source_a5_local_outside_overgroup_sylow D e hn hcore hLH hRH hout
  have hTH : (T : Subgroup G) ⊓ H =
      (T : Subgroup G) ⊓ normalizer (L : Set G) :=
    (Chapter1.isSylowIn_iff.mp hs).2.2 _ (T.isPGroup'.to_le inf_le_left)
      (le_inf inf_le_left hRH) inf_le_right
  have horbit : componentOrbit U L ≤ H.pCoreIn 2 :=
    iSup_conjugates_le_of_le_normalizer U L _ hU
      (hLH.trans (H.le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))
  have hHe : H ∈ Chapter1.He G := by
    apply Chapter1.he_of_central_involution_in_core T (D.simpleQTKE.evenCharacteristic T)
      H z (hTH ▸ hs) hz (hU hzU) hzc
    rw [hTH]
    exact (inf_le_inf_left _ (centralizer_le horbit)).trans hCT
  exact ⟨hHe, generalizedFitting_eq_pCore_of_selfCentralizing 2 (Chapter1.mem_He_iff.mp hHe)⟩

end CFSG.Quasithin.Chapter10
