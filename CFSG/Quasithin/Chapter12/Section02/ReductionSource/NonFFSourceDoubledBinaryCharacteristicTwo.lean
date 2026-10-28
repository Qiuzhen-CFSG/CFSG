module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryReeExclusion
public import Theory.GroupTheory.GeneralizedFitting.NoComponentInverter
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Characteristic two for the original paired-plane overgroups

All ordinary components have now been excluded on one chosen paired plane.
The original local residual centralizes the odd core on its moving subgroup;
together with the plane it generates the doubled orbit, so odd-core elimination
applies on this same plane. The generalized Fitting centralizer theorem then
gives characteristic two for every local-base overgroup in its centralizer.

If the ambient centralizer escapes M, choose the original minimal escaping H.
The existing Sylow and Thompson arguments give T₀ Sylow in H and H=J(H)L₀T₀;
the new conclusion supplies F*(H)=O₂(H). Thus all three clauses of 7.7.6 hold
with the original full core Q and original doubled orbit, retaining both seed
axes. This prepares Thompson factorization; it does not assert C_G(V₀)≤M.
The ambient-containment argument and final non-FF assembly remain with
qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 7.7.6, printed pp.705–707, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore DoubledBinarySylow
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The actual plane has characteristic-two local-base overgroups. -/
theorem sourceOrbit_binary_pairedPlane_characteristicTwo_with_marking
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
            HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,hnc⟩ :=
    D.sourceOrbit_binary_pairedPlane_no_components_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hWQ : D.sourceOrbit ≤ Q := (D.sourceOrbit_core_normalizer h).1
  have hQB : Q ≤ B := hcore.symm.le.trans (pCoreIn_le 2 B)
  have hUB : U ≤ B := hUW.trans (hWQ.trans hQB)
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro hz
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [hz,Subgroup.card_bot] at hc
    omega
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,?_⟩
  intro H hBH hHC
  have hodd : pPrimeCore 2 H = ⊥ := by
    have hQH : Q ≤ H := hQB.trans hBH
    have hMQ : M.pCoreIn 2 ≤ Q := core_le_of_sylow_base (T.subtype hTM)
      (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
      (sup_le L.le_normalizer hTM)
    have hMHne : H ⊓ M ≠ ⊥ := by
      intro hz
      have hUM : U ≤ M := (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans hTM
      exact hU (le_bot_iff.mp (hz ▸ le_inf (hUB.trans hBH) hUM))
    have hMH : H ⊓ M ∈ Chapter1.He G := Chapter1.lemma_1_1_4_5 T
      (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM hMHne inf_le_right
      (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M)))
    have hHN : H ≤ normalizer (U : Set G) := hHC.trans (Subgroup.centralizer_le_normalizer _)
    have hs := (h.simpleQTKE.twoLocal_sqtk (show IsTwoLocal (normalizer (U : Set G)) from
      ⟨U,hU,hp,rfl⟩)).subgroup (H.subgroupOf (normalizer (U : Set G)))
    have hSQ : IsSQTK KnownSimple.IsKnownSimple H :=
      (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp hs
    exact DoubledBinaryOddCore.oddCore_eq_bot_of_residual_supplement D.sourceOrbit U (localResidual L U) H M
      (isPPerfect_embedded_pResidual 2 (L ⊓ centralizer (U : Set G)))
      ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
      (hWQ.trans hQH) (le_sup_left.trans hBH) hgen hHC h61.centralizer_le
      hSQ.stronglyQuasithin (Chapter1.mem_He_iff.mp hMH)
  have hnone : ∀ K : Subgroup H, ¬ IsComponent H K := by
    intro K hK
    apply hnc H hBH hHC (K.map H.subtype)
    refine ⟨map_subtype_le K, ?_⟩
    change IsComponent H ((K.map H.subtype).comap H.subtype)
    rwa [comap_map_eq_self_of_injective H.subtype_injective]
  have hc : HasCharacteristicTwo H := by
    change centralizer (pCore 2 H : Set H) ≤ pCore 2 H
    have hh := centralizer_core_product_le_of_no_components 2 hnone
    simpa only [hodd,sup_bot_eq] using hh
  exact ⟨hc,generalizedFitting_eq_pCore_of_selfCentralizing 2 hc⟩

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_characteristicTwo
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
            HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_characteristicTwo_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


/-- All three clauses of source 7.7.6 for the actual minimal escaping group. -/
theorem sourceOrbit_binary_pairedPlane_constrained_escape_with_marking
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
          let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype = R) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = R) ∧
              H.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              H = elementaryAbelianMaxJ H ⊔ B ∧
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G ∧
              HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,⟨S,hS⟩,hbase,hcore,_,_,_,hchar⟩ :=
    D.sourceOrbit_binary_pairedPlane_characteristicTwo_with_marking h hd hnon F hF hmodel
  let M := normalizer (L : Set G)
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  let U := ambientPlane D.sourceOrbit E v f
  let B := localBase L (T : Subgroup G) U
  let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
  have hTM : (T : Subgroup G) ≤ M := D.sylow_normalizes_component
  have hJ := D.sourceOrbit_thompson_centralizes h.toHypothesis1221 hnon
  have hNJ := (D.sourceOrbit_nonFF_thompson_normalizers h hnon).1
  have hQ : (T : Subgroup G) ⊓ centralizer (D.sourceOrbit : Set G) = Q := by
    simpa only [D.sourceOrbit_eq] using D.doubledOrbit_sylow_centralizer h
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,⟨S,hS⟩,hbase,hcore,?_⟩
  intro hout
  have hUW : U ≤ D.sourceOrbit := ambientPlane_le_orbit D.sourceOrbit E v f
  have hp : IsPGroup 2 U := (IsElementaryAbelian.isPGroup 2 D.sourceOrbit).to_le hUW
  have hU : U ≠ ⊥ := by
    intro hz
    have hc := DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv
    change Nat.card U = 4 at hc
    rw [hz,Subgroup.card_bot] at hc
    omega
  have hUC : U ≤ centralizer (U : Set G) :=
    (hUW.trans (le_centralizer D.sourceOrbit)).trans (centralizer_le hUW)
  have hUB : U ≤ B :=
    (le_inf (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow) hUC).trans le_sup_right
  have hBC : B ≤ centralizer (U : Set G) := hbase.trans_le inf_le_right
  obtain ⟨H,hH,hHC,hUH,hSQ⟩ := minimal_escape h.simpleQTKE U B M hp hU hUB hBC hout
  have hBH : B ≤ H := hH.1.1.2
  have hRH : R ≤ H := (show R ≤ B from le_sup_right).trans hBH
  obtain ⟨P,hP⟩ := sylow_between hHC S (hS.trans_le hRH)
  have hPR : (P : Subgroup H).map H.subtype = R := hP.trans hS
  have hHQ : H.pCoreIn 2 ≤ Q :=
    (core_le_of_sylow_base P (hPR.trans_le le_sup_right) hBH).trans_eq hcore
  have hHQne : H.pCoreIn 2 ≠ Q := by
    intro heq
    apply hH.1.2
    apply le_trans _ (D.sourceOrbit_core_normalizer h).2
    change H ≤ normalizer (Q : Set G)
    rw [← heq]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hJR : elementaryAbelianMaxJ (T : Subgroup G) ≤ R :=
    le_inf (sSup_le fun _ hA => hA.1) (hJ.trans (centralizer_le hUW))
  have hgen : H = elementaryAbelianMaxJ H ⊔ B := minimal_escape_generation T U B M H
    hH hHC hp hU hUB P (hPR.trans_le inf_le_left) (hPR.symm ▸ hJR) hNJ
  have hQM : Q ≤ M := (pCoreIn_le 2 _).trans (sup_le L.le_normalizer hTM)
  have hQH : Q ≤ H := by
    rw [← hQ]
    exact (inf_le_inf_left _ (centralizer_le hUW)).trans hRH
  have hMQ : M.pCoreIn 2 ≤ Q := core_le_of_sylow_base (T.subtype hTM)
    (by rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTM]; exact le_sup_right)
    (sup_le L.le_normalizer hTM)
  have hMHne : H ⊓ M ≠ ⊥ := by
    intro hz
    have hUM : U ≤ M := (hUW.trans D.sourceOrbit_weakClosure_setup.le_sylow).trans hTM
    exact hU (le_bot_iff.mp (hz ▸ le_inf (hUB.trans hBH) hUM))
  have h61 := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  have hMH : H ⊓ M ∈ Chapter1.He G := Chapter1.lemma_1_1_4_5 T
    (h.simpleQTKE.evenCharacteristic T) h61.maximalTwoLocal hTM hMHne inf_le_right
    (inf_le_left.trans (le_inf (hMQ.trans hQH) (pCoreIn_le 2 M)))
  exact ⟨H,hH,hHC,hUH,hSQ,⟨P,hPR⟩,lt_of_le_of_ne hHQ hHQne,hgen,hMH,
    hchar H hBH hHC⟩

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_constrained_escape
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
          let R := (T : Subgroup G) ⊓ centralizer (U : Set G)
          (∃ S : Sylow 2 (centralizer (U : Set G)),
            (S : Subgroup _).map (centralizer (U : Set G)).subtype = R) ∧
          B = (L ⊔ (T : Subgroup G)) ⊓ centralizer (U : Set G) ∧
          B.pCoreIn 2 = (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
          (¬ centralizer (U : Set G) ≤ normalizer (L : Set G) →
            ∃ H : Subgroup G,
              H ∈ Chapter3.HStar B (normalizer (L : Set G)) ∧
              H ≤ centralizer (U : Set G) ∧ U ≤ H.pCoreIn 2 ∧
              IsSQTK KnownSimple.IsKnownSimple H ∧
              (∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = R) ∧
              H.pCoreIn 2 < (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
              H = elementaryAbelianMaxJ H ⊔ B ∧
              H ⊓ normalizer (L : Set G) ∈ Chapter1.He G ∧
              HasCharacteristicTwo H ∧ generalizedFitting H = pCore 2 H) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_constrained_escape_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
