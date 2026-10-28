module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Baumann.Inheritance
public import CFSG.Quasithin.Chapter15.Section04.LocalIdentification.SourceData
public import CFSG.Quasithin.Chapter1.Section01Overgroups
public import Theory.GroupTheory.NonsolvableTwoLocal

/-!
# Source transfer and the local inputs after the Sylow theorem

The earlier characteristic-two inheritance theorems discharge every universal
premise of 15.4.17. After 15.4.20, restrict one Sylow subgroup of the literal
normalizer of O₂(I) to I. Equality of its ambient image identifies it with any
prescribed Sylow subgroup of I. Thus the same Sylow witness works for every
nonidentity element of Ω₁(Z(T)), as required by `Source.LocalData`.

The final application constructs these fields simultaneously for all four
actual factor pairs. It assumes the original 15.4.19 membership and 15.4.20
Sylow conclusions, whose producers remain separate; it does not use
`Source.LocalData` to construct its own inputs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, Lemma 15.4.17,
printed p.1162, and its application after Lemma 15.4.20, pp.1164–1165.
-/

@[expose] public section

open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

variable {G : Type*} [Group G] [Finite G] {K : GroupClass}

/-- Source 15.4.17(2), with 1.1.3(2) and 1.1.4(3),(4) discharged. -/
theorem source_lemma_15_4_17_two (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) {B H I : Subgroup G}
    (hBne : B ≠ ⊥) (hBT : B ≤ (T : Subgroup G))
    (hBH : B ≤ H) (hCH : centralizer (B : Set G) ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (S : Sylow 2 H)
    (hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H)
    (hTI : (T : Subgroup G) ⊓ H ≤ I) (hIH : I ≤ H)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥) :
    Theory.GroupTheory.generalizedFitting I = pCore 2 I := by
  apply lemma_15_4_17_two hG
    (fun _ _ _ _ hM hX hXM hXC hLN =>
      Chapter1.lemma_1_1_3_2 hM hX hXM hXC hLN)
    (fun h T _ hU hp hc =>
      Chapter1.lemma_1_1_4_3 T (h.evenCharacteristic T) hU hp hc)
    (fun _ _ _ hN hNM hM hR => Chapter1.lemma_1_1_4_4 hN hNM hM hR)
    T hBne hBT hBH hCH hHN S hST hTI hIH hZ

/-- Both clauses of source 15.4.17 without additional earlier-theorem inputs. -/
theorem source_lemma_15_4_17 (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) {B H I : Subgroup G}
    (hBne : B ≠ ⊥) (hBT : B ≤ (T : Subgroup G))
    (hBH : B ≤ H) (hCH : centralizer (B : Set G) ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (S : Sylow 2 H)
    (hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H)
    (hTI : (T : Subgroup G) ⊓ H ≤ I) (hIH : I ≤ H)
    {z : G} {M : Subgroup G}
    (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hzne : z ≠ 1)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    ∃ P : Sylow 2 I,
      (P : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ H ∧
      Chapter1.Lemma115Hypotheses I P M z ∧
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥ →
        Theory.GroupTheory.generalizedFitting I = pCore 2 I) := by
  obtain ⟨P, hP, hlocal⟩ := lemma_15_4_17_one hG.toIsQTKE T hBne hBT hBH hCH hHN
    S hST hTI hIH hz hzne hM hCM
  exact ⟨P, hP, hlocal,
    source_lemma_15_4_17_two hG T hBne hBT hBH hCH hHN S hST hTI hIH⟩

/-- The prescribed Sylow subgroup works for every central involution and every
maximal two-local over its centralizer. The normalizer Sylow has exactly its
ambient image, so no fresh choice depending on the involution is needed. -/
theorem local115_of_coreNormalizer_sylow (T : Sylow 2 G)
    (hEven : IsEvenCharacteristicAt T) {I : Subgroup G} (hI : I ∈ Chapter1.H G)
    (P : Sylow 2 I) (hPT : (P : Subgroup I).map I.subtype ≤ (T : Subgroup G))
    (S : Sylow 2 (normalizer (I.pCoreIn 2 : Set G)))
    (hS : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype = (P : Subgroup I).map I.subtype)
    {z : G} {M : Subgroup G}
    (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hzne : z ≠ 1)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    Chapter1.Lemma115Hypotheses I P M z := by
  have hIN : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    (core_normalizer_mem_HOver hI).2
  have hSI : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype ≤ I := hS ▸ map_subtype_le _
  have hrestrict : restrictSylow S hIN hSI = P := by
    apply Sylow.ext
    apply Subgroup.map_injective I.subtype_injective
    exact (restrictSylow_image S hIN hSI).trans hS
  obtain ⟨hzT, hzpow, hzcentral⟩ :=
    (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hlocal := local115_of_intermediate T hEven hI
    ((pCoreIn_le_sylow I P).trans hPT) ((pCoreIn_le 2 I).trans hIN)
    (Subgroup.centralizer_le_normalizer _) le_rfl S (hS ▸ hPT) hSI hIN
    (orderOf_eq_prime_iff.mpr ⟨hzpow, hzne⟩) hzT hzcentral hM hCM
  simpa only [hrestrict] using hlocal

/-- The fitting field after 15.4.20 follows from the proved full source
15.4.17, with `B = O₂(I)` and `H = N_G(O₂(I))`. -/
theorem fitting_of_coreNormalizer_sylow (hG : IsSimpleQTKE K G)
    (T : Sylow 2 G) {I : Subgroup G} (hI : I ∈ Chapter1.H G)
    (P : Sylow 2 I) (hPT : (P : Subgroup I).map I.subtype ≤ (T : Subgroup G))
    (S : Sylow 2 (normalizer (I.pCoreIn 2 : Set G)))
    (hS : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype = (P : Subgroup I).map I.subtype)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥) :
    Theory.GroupTheory.generalizedFitting I = pCore 2 I := by
  have hIN : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    (core_normalizer_mem_HOver hI).2
  have hST : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype ≤ (T : Subgroup G) := hS ▸ hPT
  have hTI : (T : Subgroup G) ⊓ normalizer (I.pCoreIn 2 : Set G) ≤ I := by
    rw [inf_eq_sylow_map S T.isPGroup' hST, hS]
    exact map_subtype_le _
  exact source_lemma_15_4_17_two hG T hI ((pCoreIn_le_sylow I P).trans hPT)
    ((pCoreIn_le 2 I).trans hIN) (Subgroup.centralizer_le_normalizer _) le_rfl S
    (inf_eq_sylow_map S T.isPGroup' hST).symm hTI hIN hZ

/-- A single chosen normalizer Sylow produces a single Sylow of I, all
central-involution hypotheses, and the fitting implication. -/
theorem postSylow_local_inputs (hG : IsSimpleQTKE K G) (T : Sylow 2 G)
    {I U : Subgroup G} (hI : I ∈ Chapter1.H G)
    (hUT : U ≤ (T : Subgroup G)) (hUI : U ≤ I)
    (S : Sylow 2 (normalizer (I.pCoreIn 2 : Set G)))
    (hS : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype = U) :
    ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = U ∧
      (∀ z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G), z ≠ 1 →
        ∃ M : Subgroup G, Chapter1.Lemma115Hypotheses I P M z) ∧
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥ →
        Theory.GroupTheory.generalizedFitting I = pCore 2 I) := by
  have hIN : I ≤ normalizer (I.pCoreIn 2 : Set G) :=
    (core_normalizer_mem_HOver hI).2
  have hSI : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype ≤ I := hS ▸ hUI
  let P := restrictSylow S hIN hSI
  have hP : (P : Subgroup I).map I.subtype = U :=
    (restrictSylow_image S hIN hSI).trans hS
  have hSP : (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
      (normalizer (I.pCoreIn 2 : Set G)).subtype = (P : Subgroup I).map I.subtype :=
    hS.trans hP.symm
  refine ⟨P, hP, ?_, fitting_of_coreNormalizer_sylow hG T hI P (hP ▸ hUT) S hSP⟩
  intro z hz hzne
  have hzorder : orderOf z = 2 := orderOf_eq_prime_iff.mpr
    ⟨((Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz).2.1, hzne⟩
  obtain ⟨M, hCM, hM⟩ := Finite.exists_le_maximal
    (Theory.GroupTheory.isTwoLocal_involution_centralizer hzorder)
  exact ⟨M, local115_of_coreNormalizer_sylow T (hG.evenCharacteristic T) hI P
    (hP ▸ hUT) S hSP hz hzne hM hCM⟩

/-- The actual four-pair application fills the Sylow, core-normalizer,
`local115`, and fitting fields of `Source.LocalData` from source 15.4.19–20.
The single family of Sylow choices is shared by every involution. -/
theorem source_geometry_postSylow_inputs (hG : IsSimpleQTKE K G)
    (d : Source.Geometry G)
    (hZ : d.Z = Stellmacher.omegaOneCenterAmbient (d.T : Subgroup G))
    (hI : ∀ i j, d.I i j ∈ Chapter1.H G)
    (hSylow : ∀ i j, ∀ H ∈ Chapter1.HOver G (d.I i j : Set G),
      ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = d.T₀) :
    ∃ sylow : ∀ i j, Sylow 2 (d.I i j),
      (∀ i j, (sylow i j : Subgroup (d.I i j)).map (d.I i j).subtype = d.T₀) ∧
      (∀ i j, ∃ S : Sylow 2 (normalizer ((d.I i j).pCoreIn 2 : Set G)),
        (S : Subgroup (normalizer ((d.I i j).pCoreIn 2 : Set G))).map
          (normalizer ((d.I i j).pCoreIn 2 : Set G)).subtype = d.T₀) ∧
      (∀ i j z, z ∈ d.Z → z ≠ 1 → ∃ M : Subgroup G,
        Chapter1.Lemma115Hypotheses (d.I i j) (sylow i j) M z) ∧
      (∀ i j, d.Z ⊓ (d.I i j).pCoreIn 2 ≠ ⊥ →
        Theory.GroupTheory.generalizedFitting (d.I i j) = pCore 2 (d.I i j)) := by
  have hN := fun i j => sylow_core_normalizer_of_HOver (hI i j) (hSylow i j)
  choose S hS using hN
  have hlocal := fun i j => postSylow_local_inputs hG d.T (hI i j) d.T₀_le_T
    (d.T₀_le_I i j) (S i j) (hS i j)
  choose P hP h115 hfit using hlocal
  refine ⟨P, hP, fun i j => ⟨S i j, hS i j⟩, ?_, ?_⟩
  · intro i j z hz hzne
    exact h115 i j z (hZ ▸ hz) hzne
  · intro i j hz
    exact hfit i j (hZ ▸ hz)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
