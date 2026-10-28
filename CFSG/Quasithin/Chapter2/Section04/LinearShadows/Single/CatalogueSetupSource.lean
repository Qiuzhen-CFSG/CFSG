module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.OvercomponentSource
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.MathieuCovers.Source
public import Theory.GroupTheory.PCoreImage
/-!
# The literal catalogue context for a bad centralizer

The original central involution centralizer supplies a proper ordinary
component. Its actual subgroup in G has even center and two-core contained
in the original block center. Source Sylow selection then constructs the
literal MathieuSourceSetup used by the completed component catalogue.

Source: Aschbacher–Smith, 2.4.11, printed pp.531–532.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_center_centralizer_catalogue_setup
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (z : G) (hz : z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype)
    (hz1 : z ≠ 1)
    (hnot : ¬ centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G)) :
    let L := d.block.map d.H.subtype
    ∃ (X K : Subgroup G) (P : Sylow 2 X) (w : G),
      L < K ∧ IsQuasisimple K ∧
      twoCore K ≤ (center L).map L.subtype ∧ 2 ∣ Nat.card (center K) ∧
      Nonempty (ComponentRefinement.MathieuSourceSetup X K M P w) := by
  let L := d.block.map d.H.subtype
  obtain ⟨u,hu,huo,hHX,hX,hnot⟩ :=
    source_center_centralizer_counterexample_choice d hG T hST hsingle hL hM hTM hunique z hz hz1 hnot
  let X := centralizer ({u} : Set G)
  obtain ⟨hgam,hcore,P,hP,J,hJ,hJn,hLJ,_⟩ :=
    source_proper_quasisimple_overcomponent d hG T hST hsingle hL hM hTM hunique X hX hHX hnot
  let K := J.map X.subtype
  have hKX : K ≤ X := map_subtype_le _
  let : J.Normal := hJn
  have hXK : X ≤ normalizer (K : Set G) := by
    have hh := J.le_normalizer_map X.subtype
    rwa [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  have hcK : twoCore K ≤ (center L).map L.subtype :=
    (pCoreIn_mono_of_normalizes hKX hXK).trans hcore
  have hqui : IsQuasisimple K := by
    let := hJ.2
    exact IsQuasisimple.of_mulEquiv (equivMapOfInjective J X.subtype X.subtype_injective)
  have huK : u ∈ K := hLJ.le (map_subtype_le _ hu)
  let uK : K := ⟨u,huK⟩
  have huZ : uK ∈ center K := by
    apply mem_center_iff.mpr
    intro k
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (hKX k.property)
  have huc : orderOf (⟨uK,huZ⟩ : center K)=2 := by
    exact (orderOf_injective (center K).subtype (center K).subtype_injective _).symm.trans
      ((orderOf_injective K.subtype K.subtype_injective _).symm.trans huo)
  have heven : 2 ∣ Nat.card (center K) := huc ▸ orderOf_dvd_natCard (⟨uK,huZ⟩ : center K)
  have hcomp : IsComponent X (K.subgroupOf X) := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective X.subtype_injective] using hJ
  obtain ⟨T',hsetup⟩ := ComponentRefinement.exists_mathieuSourceSetup hG T hM hTM hunique hgam
    (localPairsIn_mono hHX d.full_pair) (show (d.S : Subgroup d.H).map d.H.subtype ≤
      (P : Subgroup X).map X.subtype by rw [hP]) hKX hcomp
  let : Nontrivial (T : Subgroup G) := (nontrivial_iff_ne_bot _).mpr
    (ne_bot_of_gt (bot_le.trans_lt hST))
  let : Nontrivial (T' : Subgroup G) := (T.equiv T').symm.toEquiv.nontrivial
  let : Nontrivial (center (T' : Subgroup G)) := T'.isPGroup'.center_nontrivial
  have hcp := T'.isPGroup'.to_subgroup (center (T' : Subgroup G))
  have hcd : 2 ∣ Nat.card (center (T' : Subgroup G)) := hcp.card_eq_or_dvd.resolve_left
    (ne_of_gt Finite.one_lt_card)
  obtain ⟨w,hw⟩ := exists_prime_orderOf_dvd_card' (G := center (T' : Subgroup G)) 2 hcd
  have hwG : orderOf ((w : T'):G)=2 := by
    exact (orderOf_injective (T' : Subgroup G).subtype (T' : Subgroup G).subtype_injective _).trans
      ((orderOf_injective (center (T' : Subgroup G)).subtype
        (center (T' : Subgroup G)).subtype_injective _).trans hw)
  obtain ⟨c,_⟩ := hsetup w (mem_map_of_mem _ w.property) hwG
  exact ⟨X,K,P,w,hLJ,hqui,hcK,heven,⟨c⟩⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
