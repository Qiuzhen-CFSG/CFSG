module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryUnitaryExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryCoverPlacement

/-!
# Only exceptional components remain on the original binary paired plane

All Bender and classical components are excluded on one original Sylow-placed
plane. The unitary case uses its actual fixed-field torus: it normalizes
J(Q), hence preserves W, and acts freely on each nonidentity root element.
Faithfulness of the moving sixteen then embeds that torus in the literal S₃
plane-centralizer action, contradicting its order at least fifteen.

The full Theorem C sieve consequently leaves only G₂, graph-field triality,
and Ree F₄, with the original field parameters and actual model isomorphisms.
Those exceptional components, ambient containment and the final doubled
contradiction remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith 7.7.6, printed pp.705–706, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE BinaryLinearThree
open DoubledBinaryPlanes DoubledBinaryLocalCore DoubledBinaryResidualCore
open DoubledBinaryBenderExclusion DoubledBinaryClassicalExclusion DoubledBinaryOddCore
open DoubledBinaryCoverPlacement DoubledBinaryUnitaryExclusion
universe u
variable {G : Type u} [_root_.Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The full component catalogue on one original paired plane reduces to
actual exceptional Lie groups; all Bender, linear and symplectic rows are excluded. -/
theorem sourceOrbit_binary_pairedPlane_exceptional_components_with_marking
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
              ((∃ n : ℕ, 2 ≤ n ∧
                (ClassificationModels.IsG2At (K ⧸ center K) (2^n) ∨
                  Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K))) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hdis,hcard,hquot,hn,hi,hfixed,hcomp⟩ :=
    D.sourceOrbit_binary_pairedPlane_cartan_with_marking h hd hnon F hF hmodel
  let U := ambientPlane D.sourceOrbit E v f
  let R := localResidual L U
  let A := ⁅D.sourceOrbit,R⁆
  let B := localBase L (T : Subgroup G) U
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hAW : A ≤ D.sourceOrbit := le_normalizer_iff_commutator_le_left.mp
    ((map_subtype_le _).trans (inf_le_left.trans D.sourceOrbit_component_normalizes))
  have hUW := ambientPlane_le_orbit D.sourceOrbit E v f
  have hgen : U ⊔ A = D.sourceOrbit := by
    apply eq_of_le_of_card_ge (sup_le hUW hAW)
    have hnorm : A ≤ normalizer (U : Set G) := hAW.trans
      (((le_centralizer D.sourceOrbit).trans (centralizer_le hUW)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hW : Nat.card D.sourceOrbit = 64 := by
      change Nat.card (Additive D.sourceOrbit) = 64
      rw [Nat.card_congr E.toEquiv,Module.natCard_eq_pow_finrank (K := ZMod 2)]
      norm_num [NaturalDual.Space,Module.finrank_prod,BinaryLinearThree.Vector,Matrix.PSL3Two.Fano.Vector]
    rw [card_sup_eq_mul_of_normalizes_of_disjoint U A hnorm hdis,hcard,hW,
      DoubledBinaryPlaneQuotient.ambientPlane_card D.sourceOrbit E v f hfv]
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
  have hctl := D.sourceOrbit_core_characteristic_control h
  refine ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hmark,hS,hbase,hcore,hgen,hctl,hquot,?_⟩
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
  let := hK.quasisimple
  obtain ⟨hfix,hAN,hker,horder,hinner,
    ⟨j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,hb,hl,hsp,hltwo,hu,hsz,he⟩,
    hr,hcenter,hmodels⟩ := hcomp H hBH hHC K hK
  have hclassFalse (hclass : ClassificationModels.IsBenderModel (K ⧸ center K) ∨
      ∃ n : ℕ, 2 ≤ n ∧ (ClassicalGroup.IsPSL (K ⧸ center K) 3 (2^n) ∨
        ClassicalGroup.IsPSp (K ⧸ center K) 2 (2^n))) : False := by
    have ho : Odd (Nat.card (center K)) := by
      rcases hclass with hclass | ⟨n,hn,hm | hm⟩
      · cases hclass with
        | linear n hn hm => exact linearTwo_odd_center (hltwo n hn hm) hm
        | unitary n hn hm => exact unitary_odd_center hn hm
        | suzuki m hm he => exact suzuki_odd_center (hsz m hm he) he
      · exact linearThree_odd_center (hl n hn hm).2 hm
      · exact symplectic_odd_center hn hm
    have hcentral : j.range ≤ (center (P.mapSurjective
        (QuotientGroup.mk'_surjective (center K)))).map
        (P.mapSurjective (QuotientGroup.mk'_surjective (center K)) : Subgroup _).subtype := by
      rcases hclass with hclass | ⟨n,hn,hm | hm⟩
      · exact hb hclass
      · exact (hl n hn hm).1
      · exact hsp n hn hm
    have hPC := centralizes_original_sylow K A ho hAN j hjact P hcentral
    have hPQ : (P : Subgroup K).map K.subtype ≤ Q :=
      original_sylow_le_core K A U D.sourceOrbit (T : Subgroup G) Q hgen hQ
        (hK.1.trans hHC) P (hPS.trans inf_le_left) hPC
    have hz := component_centerless H K hK hodd ho
    have hout := (he hclass).2
    rcases hclass with hclass | ⟨n,hn,hm | hm⟩
    · cases hclass with
      | linear n hn hm =>
        exact hout ((DoubledBinaryBenderExclusion.linearTwo_normalizer_thompson H K Q hK hQH
          (isPGroup_pCoreIn 2 _) hi P hPQ (hltwo n hn hm) hm).trans hNJ)
      | unitary n hn hm =>
        have hnK := unitary_normal H K hK hSQ.stronglyQuasithin hz hn hm
        have hQN := hQH.trans ((normal_subgroupOf_iff_le_normalizer hK.1).mp hnK)
        have hNW : normalizer (elementaryAbelianMaxJ Q : Set G) ≤
            normalizer (D.sourceOrbit : Set G) := by
          rw [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd]
          exact hNJ
        exact unitary_exclusion D.sourceOrbit U K A Q hAW (hK.1.trans hHC) hAN hz
          (isPGroup_pCoreIn 2 _) hQN hNW hquot j hjcard hjact P hPQ hQj (hu n hn hm) hm
      | suzuki m hm hem =>
        exact hout ((suzuki_normalizer_thompson H K Q hK hQH
          (isPGroup_pCoreIn 2 _) hi P hPQ (hsz m hm hem) hem).trans hNJ)
    · exact hout ((linear_normalizer_thompson H K Q hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hz P hPQ hn hm).trans hNJ)
    · exact hout ((symplectic_normalizer_thompson H K Q hK hQH (isPGroup_pCoreIn 2 _)
        hSQ.stronglyQuasithin hz P hPQ hn hm).trans hNJ)
  refine ⟨hodd,hfix,hAN,hker,horder,j,hj,hjact,hjcard,hje,P,hPS,hQj,hC,?_⟩
  rcases hmodels with hm | ⟨n,hn,hm | hm | hm | hm⟩ | hm
  · exact (hclassFalse (Or.inl hm)).elim
  · exact (hclassFalse (Or.inr ⟨n,hn,Or.inl hm⟩)).elim
  · exact (hclassFalse (Or.inr ⟨n,hn,Or.inr hm⟩)).elim
  · exact Or.inl ⟨n,hn,Or.inl hm⟩
  · exact Or.inl ⟨n,hn,Or.inr hm⟩
  · exact Or.inr hm

/-- Original interface, retaining all mathematical conclusions. -/
theorem sourceOrbit_binary_pairedPlane_exceptional_components
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
              ((∃ n : ℕ, 2 ≤ n ∧
                (ClassificationModels.IsG2At (K ⧸ center K) (2^n) ∨
                  Triality.Standard.IsTrialityGroupAt (2^n) (K ⧸ center K))) ∨
              ∃ m : ℕ, 1 ≤ m ∧ Chapter1.Section02.LocalModels.IsReeF4At (K ⧸ center K) m)) := by
  obtain ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,_,hrest⟩ :=
    D.sourceOrbit_binary_pairedPlane_exceptional_components_with_marking h hd hnon F hF hmodel
  exact ⟨t,ht,hnt,E,hV,hVt,v,f,hfv,hrest⟩


end CFSG.Quasithin.Chapter12.Section02.ChosenModule
