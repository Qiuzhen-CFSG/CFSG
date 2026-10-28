module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Definitions
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.GroupTheory.SelfCentralizingCore

/-!
# The actual Borel intersection in the rank-one branch

Proper-overgroup uniqueness in the concrete PSL₂ and PSU₃ models puts M ∩ L
inside N_L(S ∩ L). Its two-core is S ∩ L, so relative normality of L in I
makes M ∩ I normalize that Borel. Source 15.3.33(1) then gives the reverse
containment, once the model's characteristic-two property is established.
The unitary field parameter is the fixed-field order throughout.

These are conditional steps, not an assertion of 15.3.40. In particular
`intersection_eq_borel` displays its characteristic-two model premise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.3.33(1) and the proof of 15.3.40, printed pp.1134 and 1138.
-/

public section

open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterF.Source
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane

private theorem normalizer_normalizer {G : Type*} [Group G] (H : Subgroup G) :
    normalizer (H : Set G) ≤ normalizer (normalizer (H : Set G) : Set G) :=
  (normalizer (H : Set G)).le_normalizer

private theorem fstar_eq_twoCore {H : Type*} [Group H] [Finite H]
    (hc : centralizer (pCore 2 H : Set H) ≤ pCore 2 H) :
    generalizedFitting H = pCore 2 H := by
  apply le_antisymm
  · apply sup_le
    · exact (Fitting_eq_pcore H 2 (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hc)).le
    · apply sSup_le
      intro K hK
      rcases hK.normal_dichotomy (pCore 2 H) with h | h
      · exact h
      · exact (commutator_eq_bot_iff_le_centralizer.mp h).trans hc
  · exact (pCore_le_fitting H 2).trans (fitting_le_generalizedFitting H)

/-- Self-centralization of the local Sylow makes the concrete Borel
characteristic two. Both the centralizer and normalizer are relative to L. -/
theorem borel_characteristic_of_centralizer {G : Type*} [Group G] [Finite G]
    {L S : Subgroup G} (hf : RankOneBorelFacts L S)
    (hc : L ⊓ centralizer ((S ⊓ L : Subgroup G) : Set G) ≤ S ⊓ L) :
    generalizedFitting (borel L S) = pCore 2 (borel L S) := by
  apply fstar_eq_twoCore
  intro x hx
  have hcore : (pCore 2 (borel L S)).map (borel L S).subtype = S ⊓ L := hf.twoCore_eq
  have hxc : (x : G) ∈ centralizer ((S ⊓ L : Subgroup G) : Set G) := by
    intro y hy
    obtain ⟨z, hz, he⟩ := hcore.symm ▸ hy
    subst y
    exact congrArg Subtype.val (hx z hz)
  have hxp : (x : G) ∈ S ⊓ L := hc ⟨x.property.1, hxc⟩
  obtain ⟨z, hz, he⟩ := hcore.symm ▸ hxp
  have he' : z = x := Subtype.ext he
  exact he' ▸ hz

/-- A proper Sylow overgroup has that Sylow as its two-core, since it
lies in the rank-one Borel. -/
theorem intersection_core {G : Type*} [Group G] [Finite G]
    {L S M : Subgroup G} (hSM : S ≤ M) (hLM : ¬ L ≤ M)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hf : RankOneBorelFacts L S) : (M ⊓ L).pCoreIn 2 = S ⊓ L := by
  have hSLM : S ⊓ L ≤ M ⊓ L := inf_le_inf_right L hSM
  have hML : M ⊓ L < L := lt_of_le_of_ne inf_le_right (by
    intro h; exact hLM (h.symm.le.trans inf_le_left))
  have hB : M ⊓ L ≤ borel L S := hf.unique_maximal _ hSLM hML
  have hP' : (S ⊓ L).subgroupOf L = (P : Subgroup L) := by
    rw [← hP]
    exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
  apply le_antisymm
  · let K := ((M ⊓ L).pCoreIn 2).subgroupOf L
    have hp : IsPGroup 2 K := (isPGroup_pCoreIn 2 (M ⊓ L)).comap_subtype
    have hn : K ≤ normalizer (P : Set L) := by
      change K ≤ normalizer ((P : Subgroup L) : Set L)
      rw [← hP', ← subgroupOf_normalizer_eq inf_le_right]
      exact subgroupOf_mono L ((pCoreIn_le 2 _).trans (hB.trans inf_le_right))
    have hk : K ≤ (P : Subgroup L) := by
      have hh := hp.inf_normalizer_sylow P
      rw [inf_eq_left.mpr hn] at hh
      exact hh.le.trans inf_le_right
    have hh := Subgroup.map_mono (f := L.subtype) hk
    rwa [map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans inf_le_right), hP] at hh
  · have hp : IsPGroup 2 (S ⊓ L : Subgroup G) := hP ▸ P.isPGroup'.map L.subtype
    exact le_pCoreIn_of_normalizes hp hSLM (hB.trans inf_le_right)

/-- Relative component normality and uniqueness of the proper Sylow
overgroup make the actual Borel invariant under M ∩ I. -/
theorem local_normalizes_borel {G : Type*} [Group G] [Finite G]
    {L S M I : Subgroup G} (hLI : L ≤ I) [(L.subgroupOf I).Normal]
    (hSM : S ≤ M) (hLM : ¬ L ≤ M)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hf : RankOneBorelFacts L S) : M ⊓ I ≤ normalizer (borel L S : Set G) := by
  have hLn : I ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLI
  have hHn : M ⊓ I ≤ normalizer ((M ⊓ L : Subgroup G) : Set G) :=
    le_normalizer_inf (inf_le_left.trans M.le_normalizer) (inf_le_right.trans hLn)
  have hPn : M ⊓ I ≤ normalizer ((S ⊓ L : Subgroup G) : Set G) := by
    rw [← intersection_core hSM hLM P hP hf]
    exact hHn.trans (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  exact le_normalizer_inf (inf_le_right.trans hLn)
    (hPn.trans (normalizer_normalizer _))

/-- Applying the genuine 15.3.33(1) containment input identifies M ∩ L
with the Borel. Characteristic two of that concrete Borel is the only
additional model premise; its invariance is proved above. -/
theorem intersection_eq_borel {G : Type*} [Group G] [Finite G]
    {L S M I Yplus : Subgroup G} (hLI : L ≤ I) [(L.subgroupOf I).Normal]
    (hSM : S ≤ M) (hYS : Yplus ⊔ S ≤ M ⊓ I) (hLM : ¬ L ≤ M)
    (P : Sylow 2 L) (hP : (P : Subgroup L).map L.subtype = S ⊓ L)
    (hf : RankOneBorelFacts L S)
    (h33 : ∀ K : Subgroup G, K ≤ L → Yplus ⊔ S ≤ normalizer (K : Set G) →
      generalizedFitting K = pCore 2 K → K ≤ M ⊓ I)
    (hchar : generalizedFitting (borel L S) = pCore 2 (borel L S)) :
    M ⊓ L = borel L S := by
  apply le_antisymm
  · apply hf.unique_maximal _ (inf_le_inf_right L hSM)
    exact lt_of_le_of_ne inf_le_right (by intro h; exact hLM (h.symm.le.trans inf_le_left))
  · exact le_inf ((h33 _ inf_le_left
      (hYS.trans (local_normalizes_borel hLI hSM hLM P hP hf)) hchar).trans inf_le_left)
      inf_le_left
end CFSG.Quasithin.Chapter15.Section03.RankTwo.RankOnePlane
