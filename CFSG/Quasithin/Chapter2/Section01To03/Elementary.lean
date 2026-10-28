module

public import CFSG.Quasithin.Chapter2.Defs
public import Theory.GroupTheory.PGroup.NormalizerBarrier
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Elementary normalizer and selection arguments for Chapter 2

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), pp. 520–526. This module proves Lemma 2.3.2(1–2),
the finite maximality assertions in Notations 2.2.4 and 2.3.5, and Lemma
2.3.6. It also supplies the centralizer inclusion used in Lemma 2.3.9(8).

The main group-theoretic step is the p-group normalizer condition applied
to `V ∩ M`. Sylow containment then gives equality of 2-parts. The two
maximality constructions use maximum cardinalities of finite sets of
subgroups, preserving the distinction between the two starred families.
The characteristic-2 collection `E` is an explicit parameter here; no
recognition or QTKE structure theorem is assumed or asserted.
-/

namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] {M U V H : Subgroup G}

/-- The conditions defining β pass to 2-overgroups inside `M` (Notation 2.3.1). -/
public theorem beta_mono_inside (hU : U ∈ beta M) (hUV : U ≤ V)
    (hVM : V ≤ M) (hV : IsPGroup 2 V) : V ∈ beta M := by
  refine ⟨⟨?_, hV⟩, hVM, ?_, ?_⟩
  · intro hbot
    exact hU.1.1 (bot_unique (hbot ▸ hUV))
  · intro W hW hVW hWM
    exact hU.2.2.1 W hW (hUV.trans hVW) hWM
  · exact (inf_le_inf_left _ (centralizer_le hUV)).trans (hU.2.2.2.trans hUV)

/-- Every finite 2-overgroup of a member of β lies in `M` (Lemma 2.3.2(1)). -/
public theorem beta_overgroup_le [Finite V] (hU : U ∈ beta M) (hUV : U ≤ V)
    (hV : IsPGroup 2 V) : V ≤ M := by
  apply p_overgroup_le_of_normalizers_le hV hUV hU.2.1
  intro W hW hUW hWM
  apply hU.2.2.1 W ⟨?_, hW⟩ hUW hWM
  intro hbot
  exact hU.1.1 (bot_unique (hbot ▸ hUW))

/-- β is closed under finite 2-overgroups in the ambient group (Lemma 2.3.2(1)). -/
public theorem beta_mono [Finite V] (hU : U ∈ beta M) (hUV : U ≤ V)
    (hV : IsPGroup 2 V) : V ∈ beta M :=
  beta_mono_inside hU hUV (beta_overgroup_le hU hUV hV) hV

/-- A β-subgroup extends to a Sylow subgroup of `H` whose ambient image is still in β. -/
public theorem beta_exists_sylow (hU : U ∈ beta M) (hUH : U ≤ H) [Finite G] :
    ∃ S : Sylow 2 H, U ≤ (S : Subgroup H).map H.subtype ∧
      (S : Subgroup H).map H.subtype ∈ beta M := by
  have hUp : IsPGroup 2 (U.subgroupOf H) :=
    hU.1.2.comap_of_injective H.subtype H.subtype_injective
  obtain ⟨S, hUS⟩ := hUp.exists_le_sylow
  have hUS' : U ≤ (S : Subgroup H).map H.subtype := by
    have hm := map_mono hUS (f := H.subtype)
    simpa only [subgroupOf_map_subtype, inf_eq_left.mpr hUH] using hm
  exact ⟨S, hUS', beta_mono hU hUS' (S.isPGroup'.map H.subtype)⟩

/-- Lemma 2.3.2(2): `H` and `H ∩ M` have the same 2-part of their orders. -/
public theorem beta_twoPart_inf [Finite G] (hU : U ∈ beta M) (hUH : U ≤ H) :
    twoPart H = twoPart (H ⊓ M) := by
  obtain ⟨S, _, hS⟩ := beta_exists_sylow hU hUH
  let K := M.subgroupOf H
  have hSK : (S : Subgroup H) ≤ K := by
    intro s hs
    exact hS.2.1 (mem_map.mpr ⟨s, hs, rfl⟩)
  have hcard : Nat.card ((S.subtype hSK : Sylow 2 K) : Subgroup K) =
      Nat.card (S : Subgroup H) :=
    Nat.card_congr (subgroupOfEquivOfLe hSK).toEquiv
  have hKcard : Nat.card K = Nat.card ↥(H ⊓ M) := by
    have hc := card_map_of_injective (K := K) H.subtype_injective
    rw [subgroupOf_map_subtype, inf_comm] at hc
    exact hc.symm
  unfold twoPart
  rw [← S.card_eq_multiplicity, ← hcard, (S.subtype hSK).card_eq_multiplicity, hKcard]

end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] {M U H : Subgroup G}

/-- The order of a β-subgroup of `H` is bounded by the order of a Sylow 2-subgroup of `H`. -/
public theorem beta_card_le_twoPart [Finite G] (hU : U ∈ beta M) (hUH : U ≤ H) :
    Nat.card U ≤ twoPart H := by
  obtain ⟨S, hUS, _⟩ := beta_exists_sylow hU hUH
  calc
    Nat.card U ≤ Nat.card ((S : Subgroup H).map H.subtype) := card_le_of_le hUS
    _ = Nat.card (S : Subgroup H) := card_map_of_injective H.subtype_injective
    _ = twoPart H := S.card_eq_multiplicity

/-- The centralizer inclusion used in Lemma 2.3.9(8), from part (2) and `C_S(R) ≤ R`. -/
public theorem centralizer_core_le_of_le (Q R S : Subgroup G)
    (hQ : twoCore M ⊓ centralizer (Q : Set G) ≤ S) (hQR : Q ≤ R)
    (hR : S ⊓ centralizer (R : Set G) ≤ R) :
    twoCore M ⊓ centralizer (R : Set G) ≤ R := by
  apply le_trans _ hR
  exact le_inf ((inf_le_inf_left _ (centralizer_le hQR)).trans hQ) inf_le_right

variable {E : Set (Subgroup G)}

/-- The local pairs in `H` also lie in each overgroup (Notation 2.3.4). -/
public theorem localPairsIn_mono {H K : Subgroup G} (hHK : H ≤ K) :
    localPairsIn E M H ⊆ localPairsIn E M K :=
  fun _ hP => ⟨hP.1, hP.2.trans hHK⟩

/-- The second coordinate of a local pair is in Γ. -/
public theorem localPair_snd_mem_gamma {P : Subgroup G × Subgroup G}
    (hP : P ∈ localPairs E M) : P.2 ∈ gamma E M :=
  ⟨hP.2.2.1, P, hP, le_rfl⟩

/-- A member of Γ cannot lie in `M`, since it contains a local subgroup outside `M`. -/
public theorem gamma_not_le (hH : H ∈ gamma E M) : ¬ H ≤ M := by
  obtain ⟨P, hP, hPH⟩ := hH.2
  exact fun hHM => hP.2.2.2.2 (hPH.trans hHM)

/-- The equality of 2-parts following Notation 2.3.5. -/
public theorem gamma_twoPart_inf [Finite G] (hH : H ∈ gamma E M) :
    twoPart H = twoPart (H ⊓ M) := by
  obtain ⟨P, hP, hPH⟩ := hH.2
  exact beta_twoPart_inf hP.1 (hP.2.2.2.1.trans hPH)

/-- Lemma 2.3.6: every member of Γ₀ bounds the orders of all local bases. -/
public theorem gammaZero_card_bound [Finite G] (hH : H ∈ gammaZero E M)
    (hU : U ∈ localBases E M) : Nat.card U ≤ twoPart H := by
  rcases hH with hH | hH
  · obtain ⟨P, hP, hmax⟩ := hH.1.2
    exact (hmax U hU).trans (beta_card_le_twoPart hP.1.1
      (hP.1.2.2.2.1.trans hP.2))
  · obtain ⟨K, hK⟩ := hU
    exact (beta_card_le_twoPart hK.1 hK.2.2.2.1).trans
      (hH.2 K (localPair_snd_mem_gamma hK))

end CFSG.Quasithin.Chapter2

namespace CFSG.Quasithin.Chapter2
open Subgroup
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G} {E : Set (Subgroup G)}

/-- A nonempty δ has an inclusion-maximal member (Notation 2.2.4). -/
public theorem deltaStar_nonempty (hdelta : (delta E M).Nonempty) :
    (deltaStar E M).Nonempty := by
  obtain ⟨D, hD, hmax⟩ := Set.exists_max_image (delta E M)
    (fun K => Nat.card K) (Set.toFinite _) hdelta
  refine ⟨D, hD, ?_⟩
  intro K hK hDK
  exact (eq_of_le_of_card_ge hDK (hmax K hK)).ge

/-- A local base of globally maximal order occurs in some member of Γ. -/
public theorem gammaWithLargestBase_nonempty (hbase : (localBases E M).Nonempty) :
    (gammaWithLargestBase E M).Nonempty := by
  obtain ⟨U, hU, hmax⟩ := Set.exists_max_image (localBases E M)
    (fun K => Nat.card K) (Set.toFinite _) hbase
  obtain ⟨K, hK⟩ := hU
  exact ⟨K, localPair_snd_mem_gamma hK, (U, K), ⟨hK, le_rfl⟩, hmax⟩

/-- The superscript-star family is nonempty whenever local bases exist. -/
public theorem gammaStar_nonempty (hbase : (localBases E M).Nonempty) :
    (gammaStar E M).Nonempty := by
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image (gammaWithLargestBase E M)
    twoPart (Set.toFinite _) (gammaWithLargestBase_nonempty hbase)
  exact ⟨H, hH, hmax⟩

/-- The subscript-star family is nonempty whenever Γ is nonempty. -/
public theorem gammaMax_nonempty (hgamma : (gamma E M).Nonempty) :
    (gammaMax E M).Nonempty := by
  obtain ⟨H, hH, hmax⟩ := Set.exists_max_image (gamma E M)
    twoPart (Set.toFinite _) hgamma
  exact ⟨H, hH, hmax⟩

end CFSG.Quasithin.Chapter2
