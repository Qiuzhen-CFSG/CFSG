module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.Conjugation
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Theory.GroupTheory.PCoreImage
public import Mathlib.GroupTheory.IndexNormal

/-!
# The contrary core and its characteristic normalizers

In the contradiction argument of 15.4.20, `U=T_I` has index two in `T`.
Thus `XU` is normal in `XT`, and `R=O₂(XU)` is normalized by `XT`.
The uniqueness of the maximal two-local overgroup of `XT` then controls
all normalizers of nontrivial subgroups characteristic inside `R`.

The core of a subgroup containing a Sylow subgroup of `H` is radical in
`H`: the core of its normalizer lies in that same Sylow subgroup, is
normalized by `XU`, and hence lies back in `R`. Finally the maximal-choice
Sylow theorem for `N_G(O₂(H))` gives the genuine local 1.1.5 hypotheses via
15.4.17. Every Sylow group used here is the larger contrary `U`, as required
by the corrected argument. These are preliminary steps, not the embedding
alternatives or either generalized-Fitting case elimination.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed pp.1163–1164, proof of Lemma 15.4.20.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem normalizes_core (H : Subgroup G) :
    H ≤ normalizer (H.pCoreIn 2 : Set G) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

omit [Finite G] in
/-- The index-two contrary Sylow subgroup makes its join with `X` normal
inside `XT`, hence `XT` normalizes its intrinsic two-core. -/
theorem normalizes_contrary_core {X T U : Subgroup G}
    (hUT : U ≤ T) (hindex : U.relIndex T = 2)
    (hTX : T ≤ normalizer (X : Set G)) :
    X ⊔ T ≤ normalizer ((X ⊔ U : Subgroup G).pCoreIn 2 : Set G) := by
  have hnU : T ≤ normalizer (U : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hUT).mp (normal_of_index_eq_two hindex)
  have hn : X ⊔ T ≤ normalizer ((X ⊔ U : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans le_normalizer)
      ((le_inf hTX hnU).trans (normalizer_inf_normalizer_le_normalizer_sup X U))
  exact hn.trans (normalizer_le_normalizer_characteristic_image (X ⊔ U) (pCore 2 (X ⊔ U : Subgroup G)))

/-- The characteristic normalizers of `R=O₂(XT_I)` lie in the unique
maximal two-local overgroup of `XT`. Characteristicness is intrinsic in `R`. -/
theorem contrary_core_characteristic_control {X T U M : Subgroup G}
    (hUT : U ≤ T) (hindex : U.relIndex T = 2)
    (hTX : T ≤ normalizer (X : Set G))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ T ≤ N → N = M) :
    characteristicNormalizerClosure ((X ⊔ U : Subgroup G).pCoreIn 2) ≤ M :=
  characteristicNormalizerClosure_le_of_unique_twoLocal (isPGroup_pCoreIn 2 _)
    (normalizes_contrary_core hUT hindex hTX) hunique

/-- The raw factor's nontrivial two-core is contained in the contrary core.
Thus the normalizer itself is also controlled by uniqueness. -/
theorem contrary_core_normalizer_control {X T U M : Subgroup G}
    (hUT : U ≤ T) (hindex : U.relIndex T = 2)
    (hTX : T ≤ normalizer (X : Set G)) (hXcore : X.pCoreIn 2 ≠ ⊥)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ T ≤ N → N = M) :
    (X ⊔ U : Subgroup G).pCoreIn 2 ≠ ⊥ ∧
    normalizer ((X ⊔ U : Subgroup G).pCoreIn 2 : Set G) ≤ M := by
  have hle : X.pCoreIn 2 ≤ (X ⊔ U : Subgroup G).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left (sup_le X.le_normalizer (hUT.trans hTX))
  have hne : (X ⊔ U : Subgroup G).pCoreIn 2 ≠ ⊥ :=
    fun h => hXcore (le_bot_iff.mp (h ▸ hle))
  exact ⟨hne, (normalizer_le_characteristicNormalizerClosure_self _ hne).trans
    (contrary_core_characteristic_control hUT hindex hTX hunique)⟩

omit [Finite G] in
/-- A subgroup containing the Sylow subgroup of `H` has radical two-core in `H`.
The Sylow subgroup here is the constructed larger subgroup `U`. -/
theorem contrary_core_radical {X U H : Subgroup G}
    (hXH : X ≤ H)
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U) :
    (H ⊓ normalizer ((X ⊔ U : Subgroup G).pCoreIn 2 : Set G) : Subgroup G).pCoreIn 2 =
      (X ⊔ U : Subgroup G).pCoreIn 2 := by
  let R := (X ⊔ U : Subgroup G).pCoreIn 2
  let N := H ⊓ normalizer (R : Set G)
  have hUH : U ≤ H := hP ▸ map_subtype_le (P : Subgroup H)
  have hXUN : X ⊔ U ≤ N := le_inf (sup_le hXH hUH) (normalizes_core _)
  have hUN : U ≤ N := le_sup_right.trans hXUN
  have hQN : N.pCoreIn 2 ≤ U := by
    have h := pCoreIn_le_sylow N (restrictSylow P inf_le_left (hP ▸ hUN))
    rwa [restrictSylow_image, hP] at h
  apply le_antisymm
  · apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 N) (hQN.trans le_sup_right)
    exact hXUN.trans (normalizes_core N)
  · exact le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 (X ⊔ U))
      ((pCoreIn_le 2 (X ⊔ U)).trans hXUN) inf_le_right

/-- The corrected normalizer Sylow statement constructs all hypotheses of
1.1.5 for every nonidentity central omega element. No Sylow assertion for
`T₀` is used in this contradiction step. -/
theorem contrary_core_local115 {K : GroupClass} (hG : IsQTKE K G)
    (T : Sylow 2 G) {H U M : Subgroup G} (hH : H ∈ Chapter1.H G)
    (hUT : U ≤ (T : Subgroup G)) (hUH : U ≤ H)
    (P : Sylow 2 (normalizer (H.pCoreIn 2 : Set G)))
    (hP : (P : Subgroup (normalizer (H.pCoreIn 2 : Set G))).map
      (normalizer (H.pCoreIn 2 : Set G)).subtype = U)
    {z : G} (hz : z ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) (hzne : z ≠ 1)
    (hM : IsMaximalTwoLocal M) (hCM : centralizer ({z} : Set G) ≤ M) :
    ∃ Q : Sylow 2 H, (Q : Subgroup H).map H.subtype = U ∧
      Chapter1.Lemma115Hypotheses H Q M z := by
  let N := normalizer (H.pCoreIn 2 : Set G)
  have hHN : H ≤ N := normalizes_core H
  have hcoreN : H.pCoreIn 2 ≤ N := (pCoreIn_le 2 H).trans hHN
  have hcoreU : H.pCoreIn 2 ≤ U := by
    have h := (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) hcoreN le_rfl).trans
      (pCoreIn_le_sylow N P)
    rwa [hP] at h
  have hinf : (T : Subgroup G) ⊓ N = U :=
    (inf_eq_sylow_map P T.isPGroup' (hP ▸ hUT)).trans hP
  obtain ⟨Q, hQ, hlocal⟩ := lemma_15_4_17_one hG T hH (hcoreU.trans hUT)
    hcoreN (Subgroup.centralizer_le_normalizer _) le_rfl P (hP.trans hinf.symm)
    (hinf ▸ hUH) hHN hz hzne hM hCM
  exact ⟨Q, hQ.trans hinf, hlocal⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
