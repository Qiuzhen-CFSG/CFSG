module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.Transfer
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# Generalized Fitting inheritance in 15.4.17(2)

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed p.1162.
The three earlier lemmas are universal implications with all their source
hypotheses. Their applications here construct `N = N_G(O₂(I))`, show that
`H ∩ N` belongs to `He`, and place its two-core in the common Sylow subgroup
inside `I`. The final bridge uses the intrinsic component definition of `F*`:
each component lies in or centralizes the two-core, while the odd core is
trivial. No ordinary-Fitting substitution is made.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_twoCore (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
    range_subtype] using (pCore 2 H).le_normalizer_map H.subtype

/-- The intrinsic generalized Fitting subgroup equals the two-core for members of `He`. -/
theorem generalizedFitting_eq_twoCore_of_mem_He {I : Subgroup G}
    (hI : I ∈ Chapter1.He G) :
    Theory.GroupTheory.generalizedFitting I = pCore 2 I := by
  have hc := Chapter1.mem_He_iff.mp hI
  apply le_antisymm
  · apply sup_le
    · exact (Fitting_eq_pcore I 2
        (Theory.GroupTheory.pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)).le
    · apply sSup_le
      intro L hL
      rcases hL.normal_dichotomy (pCore 2 I) with h | h
      · exact h
      · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hc
  · exact (pCore_le_fitting I 2).trans
      (Theory.GroupTheory.fitting_le_generalizedFitting I)

/-- Source 15.4.17(2), conditional only on the stated universal versions of
1.1.3(2) and 1.1.4(3),(4). All intermediate local premises are constructed. -/
theorem lemma_15_4_17_two {K : GroupClass} (hG : IsSimpleQTKE K G)
    (earlier1132 : ∀ (_ : IsSimpleQTKE K G) (M X L : Subgroup G),
      M ∈ Chapter1.He G → IsPGroup 2 X → X ≤ M →
      X ⊔ (M ⊓ centralizer (X : Set G)) ≤ L →
      L ≤ M ⊓ normalizer (X : Set G) →
      L ∈ Chapter1.He G ∧ M ⊓ centralizer (X : Set G) ∈ Chapter1.He G)
    (earlier1143 : ∀ (_ : IsSimpleQTKE K G) (T : Sylow 2 G) (U : Subgroup G),
      U ≠ ⊥ → IsPGroup 2 U →
      (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ U ≠ ⊥ →
      U ∈ Chapter1.S2e G)
    (earlier1144 : ∀ (_ : IsSimpleQTKE K G) (N M : Subgroup G),
      N ≠ ⊥ → N ≤ M → M ∈ Chapter1.He G →
      M.pCoreIn 2 ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N → N ∈ Chapter1.He G)
    (T : Sylow 2 G) {B H I : Subgroup G}
    (hBne : B ≠ ⊥) (hBT : B ≤ (T : Subgroup G))
    (hBH : B ≤ H) (hCH : centralizer (B : Set G) ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (S : Sylow 2 H)
    (hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H)
    (hTI : (T : Subgroup G) ⊓ H ≤ I) (hIH : I ≤ H)
    (hZ : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥) :
    Theory.GroupTheory.generalizedFitting I = pCore 2 I := by
  let N := normalizer (I.pCoreIn 2 : Set G)
  have hIN : I ≤ N := normalizes_twoCore I
  have hB : IsPGroup 2 B := T.isPGroup'.of_injective (inclusion hBT) (inclusion_injective hBT)
  have hBI : B ≤ I :=
    ((le_pCoreIn_of_normalizes hB hBH hHN).trans (pCoreIn_le_sylow H S)).trans
      (hST ▸ hTI)
  have hIne : I ≠ ⊥ := fun he => hBne (le_bot_iff.mp (he ▸ hBI))
  have hcore : I.pCoreIn 2 ≠ ⊥ := by
    intro he
    exact hZ (by rw [he, inf_bot_eq])
  have hcenter : (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓
      I.pCoreIn 2 ≠ ⊥ := by
    intro he
    apply hZ
    apply le_bot_iff.mp
    rw [← he]
    apply inf_le_inf_right
    intro z hz
    obtain ⟨hzT, _, hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
    exact ⟨⟨z, hzT⟩, mem_center_iff.mpr (fun t => Subtype.ext (hzc t t.property)), rfl⟩
  have hNe : N ∈ Chapter1.He G :=
    (earlier1143 hG T (I.pCoreIn 2) hcore (isPGroup_pCoreIn 2 I) hcenter).2.2
  have hHNe : H ⊓ N ∈ Chapter1.He G := (earlier1132 hG N B (H ⊓ N)
    hNe hB (hBI.trans hIN)
    (sup_le (le_inf hBH (hBI.trans hIN)) (le_inf (inf_le_right.trans hCH) inf_le_left))
    (le_inf inf_le_right (inf_le_left.trans hHN))).1
  have hSIN : (S : Subgroup H).map H.subtype ≤ H ⊓ N :=
    le_inf (map_subtype_le _) (((hST ▸ hTI)).trans hIN)
  have hcoreI : (H ⊓ N).pCoreIn 2 ≤ I := by
    have hc := pCoreIn_le_sylow (H ⊓ N) (restrictSylow S inf_le_left hSIN)
    rw [restrictSylow_image] at hc
    exact hc.trans (hST ▸ hTI)
  exact generalizedFitting_eq_twoCore_of_mem_He (earlier1144 hG I (H ⊓ N)
    hIne (le_inf hIH hIN) hHNe (inf_le_left.trans hcoreI))
/-- Both assertions of source 15.4.17, reusing the already proved transfer
statement for (1) and the normalizer-inheritance argument for (2). -/
theorem lemma_15_4_17 {K : GroupClass} (hG : IsSimpleQTKE K G)
    (earlier1132 : ∀ (_ : IsSimpleQTKE K G) (M X L : Subgroup G),
      M ∈ Chapter1.He G → IsPGroup 2 X → X ≤ M →
      X ⊔ (M ⊓ centralizer (X : Set G)) ≤ L →
      L ≤ M ⊓ normalizer (X : Set G) →
      L ∈ Chapter1.He G ∧ M ⊓ centralizer (X : Set G) ∈ Chapter1.He G)
    (earlier1143 : ∀ (_ : IsSimpleQTKE K G) (T : Sylow 2 G) (U : Subgroup G),
      U ≠ ⊥ → IsPGroup 2 U →
      (center (T : Subgroup G)).map (T : Subgroup G).subtype ⊓ U ≠ ⊥ →
      U ∈ Chapter1.S2e G)
    (earlier1144 : ∀ (_ : IsSimpleQTKE K G) (N M : Subgroup G),
      N ≠ ⊥ → N ≤ M → M ∈ Chapter1.He G →
      M.pCoreIn 2 ⊓ centralizer (N.pCoreIn 2 : Set G) ≤ N → N ∈ Chapter1.He G)
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
    ∃ S_I : Sylow 2 I,
      (S_I : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ H ∧
      Chapter1.Lemma115Hypotheses I S_I M z ∧
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ I.pCoreIn 2 ≠ ⊥ →
        Theory.GroupTheory.generalizedFitting I = pCore 2 I) := by
  obtain ⟨S_I, hSI, hlocal⟩ := lemma_15_4_17_one hG.toIsQTKE T hBne hBT hBH hCH hHN
    S hST hTI hIH hz hzne hM hCM
  exact ⟨S_I, hSI, hlocal, fun hZ => lemma_15_4_17_two hG earlier1132 earlier1143
    earlier1144 T hBne hBT hBH hCH hHN S hST hTI hIH hZ⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
