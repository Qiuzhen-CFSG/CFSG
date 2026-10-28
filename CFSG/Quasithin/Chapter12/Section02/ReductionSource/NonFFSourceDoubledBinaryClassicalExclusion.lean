module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryClassicalExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoverPlacement

/-!
# Classical component exclusions on the original binary paired plane

The original residual supplement eliminates O(H). The known odd covering
centers are therefore trivial. Odd-prime rank makes the linear-three and
symplectic components normal in H. Their actual matrix Thompson products
place the original Sylow Borels in N_G(J(Q)), hence in M; the previously
proved Cartan escape gives the contradiction. The linear-two and Suzuki
exclusions are retained on this same plane and the original field parameters.

The unitary and exceptional component cases and the final ambient containment
remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 7.7.6, printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryBenderExclusion DoubledBinaryClassicalExclusion DoubledBinaryOddCore
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- On one original Sylow-placed plane, all linear-two, linear-three,
symplectic and Suzuki ordinary components are excluded. The proof retains
the actual Q, its Thompson normalizer, and the centerless component maps. -/
theorem sourceOrbit_binary_pairedPlane_no_linear_symplectic_suzuki
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
          (∀ H : Subgroup G, B ≤ H → H ≤ centralizer (U : Set G) →
            ∀ K : Subgroup G, IsComponentIn K H →
              (¬ ∃ n : ℕ, 2 ≤ n ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 2 (2 ^ n) ∨
                ClassicalGroup.IsPSL (K ⧸ center K) 3 (2 ^ n) ∨
                ClassicalGroup.IsPSp (K ⧸ center K) 2 (2 ^ n))) ∧
              (¬ ∃ m : ℕ, 1 ≤ m ∧ Nonempty ((K ⧸ center K) ≃*
                BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hgen,hctl,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_coverPlacement h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  have hJQ : elementaryAbelianMaxJ (T : Subgroup G) ≤ Q := by
    rw [←hQ]
    exact le_inf (sSup_le fun _ hA => hA.1)
      (D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon)
  have hJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).2 Q
    (isPGroup_pCoreIn 2 _) hJQ
  have hNJ : normalizer (elementaryAbelianMaxJ Q : Set G) ≤ normalizer (L : Set G) := by
    rw [hJ.1]
    exact (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hS,hbase,hcore,hgen,hctl,?_⟩
  intro H hBH hHC K hK
  have hQH : Q ≤ H := by
    rw [←hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans (le_sup_right.trans hBH)
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
  have hi := component_normalizer_index H K Q hSQ.stronglyQuasithin hK hQH
  have hodd : pPrimeCore 2 H = ⊥ := by
    let M := normalizer (L : Set G)
    have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
    have hWQ := (D.sourceOrbit_core_normalizer h).1
    have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
    have hUB : U ≤ B := hUW.trans (hWQ.trans (hcore ▸ pCoreIn_le 2 B))
    have hMQ : M.pCoreIn 2 ≤ Q := DoubledBinarySylow.core_le_of_sylow_base (T.subtype hTM)
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
      (sup_le L.le_normalizer hTM)
    have hMHne : H ⊓ M ≠ ⊥ := by
      intro hz
      have hUM : U ≤ M := (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans hTM
      exact hU (le_bot_iff.mp (hz ▸ le_inf (hUB.trans hBH) hUM))
    have hMH : H ⊓ M ∈ Chapter1.He G := Chapter1.lemma_1_1_4_5 T
      (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM hMHne inf_le_right
      (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M)))
    exact oddCore_eq_bot_of_residual_supplement D.sourceOrbit U (localResidual L U) H M
      (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
      ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
      (hWQ.trans hQH) (le_sup_left.trans hBH) hgen hHC h61.centralizer_le
      hSQ.stronglyQuasithin (Chapter1.mem_He_iff.mp hMH)
  constructor
  · rintro ⟨n,hn,hm | hm | hm⟩
    · obtain ⟨_,hdegree,_,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
        (Or.inl (ClassificationModels.IsBenderModel.linear n hn hm))
      exact hout ((DoubledBinaryBenderExclusion.linearTwo_normalizer_thompson H K Q hK hQH
        (isPGroup_pCoreIn 2 _) hi P hPQ (hdegree n hn hm) hm).trans hNJ)
    · obtain ⟨ho,_,_,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
        (Or.inr ⟨n,hn,Or.inl hm⟩)
      have hz := component_centerless H K hK hodd ho
      exact hout ((linear_normalizer_thompson H K Q hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hz P hPQ hn hm).trans hNJ)
    · obtain ⟨ho,_,_,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
        (Or.inr ⟨n,hn,Or.inr hm⟩)
      have hz := component_centerless H K hK hodd ho
      exact hout ((symplectic_normalizer_thompson H K Q hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hz P hPQ hn hm).trans hNJ)
  · rintro ⟨m,hm,he⟩
    obtain ⟨_,_,hparameter,⟨P,hPQ,hout⟩,_⟩ := hcomp H hBH hHC K hK
      (Or.inl (ClassificationModels.IsBenderModel.suzuki m hm he))
    exact hout ((suzuki_normalizer_thompson H K Q hK hQH
      (isPGroup_pCoreIn 2 _) hi P hPQ (hparameter m hm he) he).trans hNJ)
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
