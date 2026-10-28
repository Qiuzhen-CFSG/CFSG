module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.Construction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.BlockReduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.BorelPlacement.Containment.A3Exclusion

/-!
# Marked PSL₃ Borel containment

The intrinsic model and component-orbit calculations construct a solvable
characteristic-two overgroup B ⊔ Q and apply the complete E.6.7 input.
Solvability reduces containment to exclusion of relatively subnormal A₃
blocks. For odd n the actual PSL₃(2ⁿ) Borel has order prime to three;
this persists in the component-orbit overgroup and excludes those blocks.
For positive even n, the matrix Borel excludes subnormal two-perfect groups
of order twelve. The central component-orbit argument transfers this to
the actual A₃ blocks of B ⊔ Q, including when Q permutes components.

`ordinary_markedBorel_le` assembles both parities; `cover_markedBorel_le`
handles the two-group central covers of PSL₃(4), with trivial centers allowed.
Both retain the complete universally quantified E.6.7 input and discharge
all intrinsic Borel and block-exclusion premises. No additional use of
Hypothesis E.6.1 or the earlier local facts is needed for containment once
this input and the component and Sylow data are supplied.

Source: Aschbacher–Smith E.6.7–8, printed pp.246–248 (PDF pp.257–259),
combined manuscript of 1 March 2004, especially the Borel paragraph on p.248.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
open Matrix.PSL3.LinearThree.BorelStructure
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- Conditional assembly: intrinsic A₃ exclusion remains an explicit obligation. -/
theorem markedBorel_le_of_no_alternatingThree
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hc : HasCharacteristicTwo (markedBorel L S))
    (hs : Group.IsSolvable (markedBorel L S))
    (hno : ∀ B : Subgroup G,
      B ≤ markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V →
      (B.subgroupOf (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V)).IsSubnormal →
      ¬ ChapterC.IsAlternatingBlock B 3) : markedBorel L S ≤ M := by
  obtain ⟨d⟩ := markedBorel_adjoin_decomposition h67 hU hL S hS hc
  exact le_sup_left.trans (le_of_solvable_decomposition_no_alternatingThree d
    (markedBorel_adjoin_solvable hU hL S hS hs) hno)

/-- The binary branch closes directly because the marked Sylow is self-normalizing. -/
theorem binary_markedBorel_le (h : HypothesisE61 K T M V)
    (iso : ClassicalGroup.IsPSL L 3 2) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    markedBorel L S ≤ M := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  have he : normalizer (S : Set L) = (S : Subgroup L) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [S.normalizer_map_surjective e.toMonoidHom e.surjective]
    exact normalizer_eq_self_of_card_two F hF (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  change (normalizer (S : Set L)).map L.subtype ≤ M
  rw [he, hS]
  exact inf_le_right.trans (inf_le_left.trans h.sylow_le)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
open Matrix.PSL3.LinearThree.BorelStructure
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

/-- An odd field exponent gives a marked Borel of order prime to three. -/
theorem ordinary_markedBorel_three_free {n : ℕ} (hn : Odd n)
    (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) (S : Sylow 2 L) :
    ¬ 3 ∣ Nat.card (markedBorel L S) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := iso
  have hc := three_not_dvd_card_sylowNormalizer_of_odd F hn hF
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  change ¬ 3 ∣ Nat.card (normalizer (S.map e.toMonoidHom : Set PSL(3,F))) at hc
  rw [← S.normalizer_map_surjective e.toMonoidHom e.surjective,
    card_map_of_injective e.injective] at hc
  change ¬ 3 ∣ Nat.card ((normalizer (S : Set L)).map L.subtype)
  rwa [card_map_of_injective L.subtype_injective]

/-- A missing prime persists in the component-orbit overgroup. -/
theorem markedBorel_adjoin_three_free (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : ¬ 3 ∣ Nat.card (markedBorel L S)) :
    ¬ 3 ∣ Nat.card (markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) := by
  let H := centralizer (U : Set G)
  let B := markedBorel L S
  let Q := sylowCentralizer (T : Subgroup G) V
  have hBH : B ≤ H := (map_subtype_le _).trans hL.1
  have hQH : Q ≤ H := inf_le_right.trans (Subgroup.centralizer_le hU.1)
  have hinv : Q.subgroupOf H ⊓ normalizer (L.subgroupOf H : Set H) ≤
      normalizer (B.subgroupOf H : Set H) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBH]
    intro x hx
    exact markedBorel_stable S hS hx
  have hcB : ¬ 3 ∣ Nat.card (B.subgroupOf H) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hBH).toEquiv]
  have hcQ : ¬ 3 ∣ Nat.card (Q.subgroupOf H) := by
    have hp : IsPGroup 2 (Q.subgroupOf H) :=
      (T.isPGroup'.to_le (show Q ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk]
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hd := hL.2.not_dvd_card_local_adjoin Nat.prime_three
    (subgroupOf_mono H (show B ≤ L from map_subtype_le _)) hinv hcB hcQ
  let e : (B.subgroupOf H ⊔ Q.subgroupOf H : Subgroup H) ≃* (B ⊔ Q : Subgroup G) :=
    (MulEquiv.subgroupCongr (subgroupOf_sup hBH hQH).symm).trans
      (subgroupOfEquivOfLe (sup_le hBH hQH))
  rwa [Nat.card_congr e.toEquiv] at hd

/-- E.6.7 closes every ordinary odd-exponent branch without further model premises. -/
theorem ordinary_odd_markedBorel_le
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : Odd n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    markedBorel L S ≤ M := by
  obtain ⟨hc,hs⟩ := ordinary_markedBorel_properties hn.pos iso S
  have hthree := markedBorel_adjoin_three_free hU hL S hS
    (ordinary_markedBorel_three_free hn iso S)
  apply markedBorel_le_of_no_alternatingThree h67 hU hL S hS hc hs
  intro B hBK _ hB
  let X := markedBorel L S ⊔ sylowCentralizer (T : Subgroup G) V
  let : Group.IsSolvable X := markedBorel_adjoin_solvable hU hL S hS hs
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := inclusion hBK) (inclusion_injective hBK)
  have hcB := short_quotient_card_three hB.2.1
  have hd : 3 ∣ Nat.card B := hcB ▸ (pCore 2 B).card_quotient_dvd_card
  have hi := (B.subgroupOf X).card_subgroup_dvd_card
  rw [Nat.card_congr (subgroupOfEquivOfLe hBK).toEquiv] at hi
  exact hthree (hd.trans hi)

/-- The matrix and component-orbit exclusion closes every positive even exponent. -/
theorem ordinary_even_markedBorel_le
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (heven : Even n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    markedBorel L S ≤ M := by
  obtain ⟨hc, hs⟩ := ordinary_markedBorel_properties hn iso S
  exact markedBorel_le_of_no_alternatingThree h67 hU hL S hS hc hs
    (fun _ hDX hsub =>
      A3Exclusion.ordinary_even_not_alternatingThree hU hL S hS hn heven iso hDX hsub)

/-- The marked Borel of an ordinary PSL₃(2ⁿ) component lies in M for every n ≥ 1. -/
theorem ordinary_markedBorel_le
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    {n : ℕ} (hn : 1 ≤ n) (iso : ClassicalGroup.IsPSL L 3 (2 ^ n)) :
    markedBorel L S ≤ M := by
  rcases Nat.even_or_odd n with heven | hodd
  · exact ordinary_even_markedBorel_le h67 hU hL S hS hn heven iso
  · exact ordinary_odd_markedBorel_le h67 hU hL S hS hodd iso

/-- The marked Borel of a two-group central cover of PSL₃(4) lies in M.
The covering center is permitted to be trivial. -/
theorem cover_markedBorel_le
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hz : IsPGroup 2 (center L)) (iso : ClassicalGroup.IsPSL (L ⧸ center L) 3 4) :
    markedBorel L S ≤ M := by
  obtain ⟨hc, hs⟩ := cover_markedBorel_properties hz iso S
  exact markedBorel_le_of_no_alternatingThree h67 hU hL S hS hc hs
    (fun _ hDX hsub => A3Exclusion.cover_not_alternatingThree hU hL S hS hz iso hDX hsub)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.BorelPlacement.Containment
