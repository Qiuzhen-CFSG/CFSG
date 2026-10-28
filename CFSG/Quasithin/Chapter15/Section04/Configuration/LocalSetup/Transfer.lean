module

public import CFSG.Quasithin.Chapter1.Section01
public import CFSG.Quasithin.Defs
public import Stellmacher.OmegaOneCenterMap

/-!
# Transfer to intermediate local subgroups in Section 15.4

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 15.4.17(1), printed p.1162. The ambient subgroup `B` is
normal only in `H`, and `I` contains the specified Sylow subgroup of `H`.

Restrict that Sylow subgroup to `I`. The core of `H ∩ M` lies in this common
Sylow subgroup and hence in the core of `I ∩ M`. Lemma 1.1.6 gives the required
centralizer bound inside `H`; the two-core of `M` lies in `T`, which tightens
the bound to `T ∩ H ≤ I`. This constructs every hypothesis of 1.1.5.

The last two lemmas justify the core-normalizer specialization only AFTER
15.4.20 has been proved. The printed `T₀` in its contrary-case argument on
pp.1163–1164 must be `T_I`; it cannot serve as a premise for this specialization.
No assertion about the generalized Fitting subgroup in 15.4.17(2) is assumed
or proved here.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

variable {G : Type*} [Group G] {p : ℕ} {H I : Subgroup G}

def restrictSylow (S : Sylow p H) (hIH : I ≤ H)
    (hSI : (S : Subgroup H).map H.subtype ≤ I) : Sylow p I :=
  S.comapOfInjective (inclusion hIH) (inclusion_injective hIH) (by
    intro x hx
    exact ⟨⟨x, hSI (mem_map.mpr ⟨x, hx, rfl⟩)⟩, rfl⟩)

theorem restrictSylow_image (S : Sylow p H) (hIH : I ≤ H)
    (hSI : (S : Subgroup H).map H.subtype ≤ I) :
    ((restrictSylow S hIH hSI : Subgroup I).map I.subtype) =
      (S : Subgroup H).map H.subtype := by
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨inclusion hIH y, hy, rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    refine ⟨⟨y, hSI ⟨y, hy, rfl⟩⟩, ?_, rfl⟩
    exact hy

private theorem normalizes_core (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn p : Set G) := by
  simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map,
    range_subtype] using (pCore p H).le_normalizer_map H.subtype

private theorem core_le_sylow_image (S : Sylow p H) (hIH : I ≤ H)
    (hSI : (S : Subgroup H).map H.subtype ≤ I) :
    I.pCoreIn p ≤ (S : Subgroup H).map H.subtype := by
  simpa only [restrictSylow_image] using pCoreIn_le_sylow I (restrictSylow S hIH hSI)

/-- The first assertion of 15.4.17, with the subgroup `I` carrying the restriction
of the actual Sylow subgroup of `H`. -/
theorem local115_of_intermediate [Finite G]
    (T : Sylow 2 G) (hEven : IsEvenCharacteristicAt T)
    {B M : Subgroup G} (hBne : B ≠ ⊥) (hBT : B ≤ (T : Subgroup G))
    (hBH : B ≤ H) (hCH : centralizer (B : Set G) ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (S : Sylow 2 H) (hST : (S : Subgroup H).map H.subtype ≤ (T : Subgroup G))
    (hSI : (S : Subgroup H).map H.subtype ≤ I) (hIH : I ≤ H)
    {z : G} (hz : orderOf z = 2) (hzT : z ∈ (T : Subgroup G))
    (hzcentral : ∀ t ∈ (T : Subgroup G), t * z = z * t)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    Chapter1.Lemma115Hypotheses I (restrictSylow S hIH hSI) M z := by
  have hB : IsPGroup 2 B := T.isPGroup'.of_injective (inclusion hBT) (inclusion_injective hBT)
  have hHe : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      (T : Subgroup G) ≤ N → N ∈ Chapter1.He G := by
    intro N hN hTN
    exact Chapter1.mem_He_iff.mpr (hEven N hN hTN)
  have hlocal := Chapter1.lemma_1_1_6 hBne hB hBH hCH hHN S T hST
    hz hzT hzcentral hM hCM hHe
  have hTM : (T : Subgroup G) ≤ M := by
    intro t ht
    exact hCM (mem_centralizer_singleton_iff.mpr (hzcentral t ht))
  have hSHM : (S : Subgroup H).map H.subtype ≤ H ⊓ M :=
    le_inf (map_subtype_le _) (hST.trans hTM)
  have hcoreSH : (H ⊓ M).pCoreIn 2 ≤ (S : Subgroup H).map H.subtype :=
    core_le_sylow_image S inf_le_left hSHM
  have hcores : (H ⊓ M).pCoreIn 2 ≤ (I ⊓ M).pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (H ⊓ M))
    · exact le_inf (hcoreSH.trans hSI) ((pCoreIn_le 2 _).trans inf_le_right)
    · exact (inf_le_inf_right M hIH).trans (normalizes_core (H ⊓ M))
  have hMT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, subgroupOf_map_subtype, inf_of_le_left hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hBI : B ≤ I :=
    ((le_pCoreIn_of_normalizes hB hBH hHN).trans (pCoreIn_le_sylow H S)).trans hSI
  refine ⟨?_, ?_, ?_, hz, ?_, ?_, hCM⟩
  · intro hbot
    exact hBne (le_bot_iff.mp (hbot ▸ le_pCoreIn_of_normalizes hB hBI (hIH.trans hHN)))
  · simpa only [restrictSylow_image] using hlocal.mem_HeOver
  · intro x hx
    have hxH : x ∈ H := hlocal.core_centralizer_le
      ⟨hx.1, centralizer_le hcores hx.2⟩
    have hxS : x ∈ (S : Subgroup H).map H.subtype := by
      rw [← inf_eq_sylow_map S T.isPGroup' hST]
      exact ⟨hMT hx.1, hxH⟩
    exact hSI hxS
  · simpa only [restrictSylow_image] using hlocal.mem_sylow
  · simpa only [restrictSylow_image] using hlocal.central

/-- Source specialization to nonidentity elements of `Ω₁(Z(T))`. -/
theorem lemma_15_4_17_one [Finite G] {K : GroupClass}
    (hG : IsQTKE K G) (T : Sylow 2 G)
    {B M : Subgroup G} (hBne : B ≠ ⊥) (hBT : B ≤ (T : Subgroup G))
    (hBH : B ≤ H) (hCH : centralizer (B : Set G) ≤ H)
    (hHN : H ≤ normalizer (B : Set G))
    (S : Sylow 2 H) (hST : (S : Subgroup H).map H.subtype = (T : Subgroup G) ⊓ H)
    (hSI : (T : Subgroup G) ⊓ H ≤ I) (hIH : I ≤ H)
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hzne : z ≠ 1)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    ∃ S_I : Sylow 2 I,
      (S_I : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ H ∧
      Chapter1.Lemma115Hypotheses I S_I M z := by
  obtain ⟨hzT, hzpow, hzc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz
  have hzorder : orderOf z = 2 := orderOf_eq_prime_iff.mpr ⟨hzpow, hzne⟩
  have hSI' : (S : Subgroup H).map H.subtype ≤ I := hST ▸ hSI
  refine ⟨restrictSylow S hIH hSI', (restrictSylow_image S hIH hSI').trans hST, ?_⟩
  exact local115_of_intermediate T (hG.evenCharacteristic T) hBne hBT hBH hCH hHN
    S (hST ▸ inf_le_left) hSI' hIH hzorder hzT hzc hM hCM

/-- The normalizer used after 15.4.20 really is in the source family `H(I)`. -/
theorem core_normalizer_mem_HOver {I : Subgroup G} (hI : I ∈ Chapter1.H G) :
    normalizer (I.pCoreIn 2 : Set G) ∈ Chapter1.HOver G (I : Set G) := by
  refine ⟨Chapter1.mem_H_of_isTwoLocal ⟨I.pCoreIn 2, hI, isPGroup_pCoreIn 2 I, rfl⟩,
    normalizes_core I⟩

/-- The core-normalizer Sylow conclusion is a consequence of the completed
15.4.20, not an input to its contradiction argument. -/
theorem sylow_core_normalizer_of_HOver {I T₀ : Subgroup G}
    (hI : I ∈ Chapter1.H G)
    (hSylow : ∀ H ∈ Chapter1.HOver G (I : Set G),
      ∃ S : Sylow 2 H, (S : Subgroup H).map H.subtype = T₀) :
    ∃ S : Sylow 2 (normalizer (I.pCoreIn 2 : Set G)),
      (S : Subgroup (normalizer (I.pCoreIn 2 : Set G))).map
        (normalizer (I.pCoreIn 2 : Set G)).subtype = T₀ :=
  hSylow _ (core_normalizer_mem_HOver hI)

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
