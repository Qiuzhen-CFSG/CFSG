module
public import Theory.GroupTheory.ConjugateSpanSupplement
public import Theory.GroupTheory.SylowFixedConjugateSpanSplitting
public import Theory.GroupTheory.Commutator.SylowFixedSeed
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup

/-!
# Splitting the omega-center orbit under a Sylow-normalized subgroup

Let T normalize K, and suppose KT has characteristic two. The original
omega-center Z has a reduced, hence elementary, orbit in KT. Adjoining T
does not change its K-orbit. Odd-index averaging splits that orbit into
its moved subgroup and its KT-fixed subgroup. The latter is exactly
C_Z(K), since the elementary orbit lies in T and T centralizes Z.

This proves the literal splitting used in Aschbacher–Smith B.2.14 and
13.4.10, printed pp.78 and907–909, without assuming a module complement.
-/

public section
open Subgroup Stellmacher
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

theorem omegaCenter_component_span_split (T : Sylow 2 G) (K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hchar : centralizer (pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G) :
      Set (K ⊔ (T : Subgroup G) : Subgroup G)) ≤ pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) :
    conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K =
      ⁅conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) K,K⁆ ⊔
        (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let H := K ⊔ (T : Subgroup G)
  let W := conjugateSpanBy Z H
  have hZTle : Z ≤ (T : Subgroup G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZH : Z ≤ H := hZTle.trans le_sup_right
  have hZT : Z ≤ centralizer (T : Set G) :=
    fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hHK : H ≤ normalizer (K : Set G) := sup_le K.le_normalizer hTK
  have hspan : W = conjugateSpanBy Z K :=
    conjugateSpanBy_sup_of_normalizes_seed Z K (T : Subgroup G)
      ((le_centralizer_iff.mp hZT).trans (Subgroup.centralizer_le_normalizer _)) hTK
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hred := reduced_conjugateSpan_of_sylow_central T H Z hTH
    hZTle hZT hchar
  have hWH : W ≤ H := conjugateSpanBy_le_self hZH
  let : IsElementaryAbelian 2 (W.subgroupOf H) := hred.elementary
  let : IsElementaryAbelian 2 W := by
    have hh : IsElementaryAbelian 2 ((W.subgroupOf H).map H.subtype) :=
      IsElementaryAbelian.map H.subtype
    rwa [map_subgroupOf_eq_of_le hWH] at hh
  have hWT : W ≤ (T : Subgroup G) := by
    intro w hw
    have hh : (⟨w,hWH hw⟩ : H) ∈ pCore 2 H := hred.le_pCore hw
    exact pCore_isPGroup.le_sylow_of_normal (T.subtype hTH) hh
  have hs := conjugateSpan_split_of_sylow_fixed (T.subtype hTH)
    (show Z ≤ centralizer (((T.subtype hTH : Sylow 2 H) : Subgroup H).map H.subtype : Set G)
      by rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]; exact hZT)
  have hmove : ⁅W,H⁆ = ⁅W,K⁆ :=
    commutator_conjugateSpan_eq_of_fixed_supplement Z H H K (T : Subgroup G)
      hZH le_sup_left le_sup_right H.le_normalizer hHK le_sup_left le_rfl hZT
  have hfixed : W ⊓ centralizer (H : Set G) = Z ⊓ centralizer (K : Set G) := by
    apply le_antisymm
    · intro w hw
      refine ⟨(mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨hWT hw.1, elemPow_eq_one_of_isElementaryAbelian w hw.1, ?_⟩, ?_⟩
      · exact centralizer_le hTH hw.2
      · exact centralizer_le (show K ≤ H from le_sup_left) hw.2
    · intro z hz
      refine ⟨le_conjugateSpanBy Z H hz.1, ?_⟩
      have hh : H ≤ centralizer ({z} : Set G) := sup_le
        (fun k hk => mem_centralizer_singleton_iff.mpr (hz.2 k hk))
        (fun t ht => mem_centralizer_singleton_iff.mpr (hZT hz.1 t ht))
      exact fun a ha => mem_centralizer_singleton_iff.mp (hh ha)
  change W = ⁅W,H⁆ ⊔ (W ⊓ centralizer (H : Set G)) at hs
  rw [hmove,hfixed,hspan] at hs
  exact hs
end Theory.GroupTheory
