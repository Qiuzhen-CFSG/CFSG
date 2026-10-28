module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognition
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Restriction
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.Source
public import CFSG.Quasithin.Chapter2.Section01To03.LocalStructure.C129Complete

/-!
# The original component catalogue and full-Sylow local block

The source Γ₀ configuration supplies the refined component alternatives.
The geometric Sylow-intersection bound restricts the original local block
to a full Sylow subgroup of its component. Bender components then disappear
by local-component uniqueness. Source: Aschbacher–Smith 2.3.9(7) and the
double-linear conclusion of 2.4.7, printed p.541.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
variable {G : Type*} [Group G] [Finite G]

/-- Restriction to the component gives a full Sylow actor when its intersection
with the original Sylow is contained in the index-two base. -/
theorem local_full_sylow_of_intersection_le
    (P : Sylow 2 G) (B L K : Subgroup G) (hBK : B ≤ P)
    (hlocal : L ∈ Chapter1.L G B) (hLK : L ≤ K) (hK : K.IsSubnormal)
    (hinter : K ⊓ (P : Subgroup G) ≤ B) :
    ∃ Q : Sylow 2 K, (Q : Subgroup K) = (P : Subgroup G).subgroupOf K ∧
      L.subgroupOf K ∈ ChapterA.Section03.localCComponents Q := by
  obtain ⟨Q,hQ⟩ := P.exists_subgroupOf_eq_of_subnormal K hK
  have he : B.subgroupOf K = (P : Subgroup G).subgroupOf K := by
    apply le_antisymm (subgroupOf_mono K hBK)
    intro k hk
    exact hinter ⟨k.property,hk⟩
  have h := ChapterA.Section03.SourceEmbeddings.local_restrict hlocal.1 hLK
  rw [he,←hQ] at h
  exact ⟨Q,hQ,h⟩

/-- The Bender rows cannot contain a proper natural block at the full Sylow. -/
theorem not_bender_of_local_natural_block
    (P : Sylow 2 G) (L : Subgroup G) {n : ℕ}
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hnatural : ChapterC.IsL2EvenBlock L n) [IsQuasisimple G] :
    ¬ ClassificationModels.IsBenderModel G := by
  intro hm
  have htop : IsComponent G (⊤ : Subgroup G) := by
    exact ⟨.top,IsQuasisimple.of_mulEquiv (topEquiv (G := G)).symm⟩
  have hmodel : ClassificationModels.IsBenderModel (⊤ : Subgroup G) :=
    hm.of_mulEquiv (topEquiv (G := G))
  have he := ChapterA.Section03.SourceEmbeddings.eq_of_bender_containing_component
    P hlocal htop.isCComponent le_top hmodel
  have hq : IsQuasisimple L := he.symm ▸ htop.2
  exact natural_block_not_quasisimple hnatural hq

/-- The original Γ₀ context supplies the actual refined component catalogue.
The binary M₂₂ quotient is retained explicitly for the rank argument. -/
theorem source_component_catalogue
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M X K B J : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hgamma : X ∈ gammaZero (Chapter1.He G) M)
    (hpair : (B,J) ∈ localPairsIn (Chapter1.He G) M X)
    (P : Sylow 2 X) (hBP : B ≤ (P : Subgroup X).map X.subtype)
    (hKX : K ≤ X) (hK : IsComponent X (K.subgroupOf X)) :
    ∃ z : G, ComponentRefinement.RefinedIntersection K M ((P : Subgroup X).map X.subtype) z ∨
      Nonempty ((K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) := by
  obtain ⟨T',hsetup⟩ := ComponentRefinement.exists_mathieuSourceSetup
    hG T hM hTM hunique hgamma hpair hBP hKX hK
  have hcore : twoCore X ≠ ⊥ := hgamma.elim (fun h => h.1.1.1) (fun h => h.1.1)
  let : Nontrivial (twoCore X) := (nontrivial_iff_ne_bot _).mpr hcore
  have htwo : 2 ∣ Nat.card (twoCore X) :=
    (show IsPGroup 2 (twoCore X) from pCore_isPGroup.map X.subtype).card_eq_or_dvd.resolve_left (ne_of_gt Finite.one_lt_card)
  have htwoG : 2 ∣ Nat.card G := htwo.trans (twoCore X).card_subgroup_dvd_card
  let : Nontrivial (T' : Subgroup G) := (nontrivial_iff_ne_bot _).mpr (T'.ne_bot_of_dvd_card htwoG)
  let : Nontrivial (center (T' : Subgroup G)) := T'.isPGroup'.center_nontrivial
  have hc : 2 ∣ Nat.card (center (T' : Subgroup G)) :=
    (T'.isPGroup'.to_subgroup (center (T' : Subgroup G))).card_eq_or_dvd.resolve_left
      (ne_of_gt Finite.one_lt_card)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center (T' : Subgroup G)) 2 hc
  have hzG : orderOf ((z:T'):G)=2 := by
    exact (orderOf_injective (T' : Subgroup G).subtype (T' : Subgroup G).subtype_injective _).trans
      ((orderOf_injective (center (T' : Subgroup G)).subtype
        (center (T' : Subgroup G)).subtype_injective _).trans hz)
  obtain ⟨c,_⟩ := hsetup z (mem_map_of_mem _ z.property) hzG
  have hh := (c.source_refinement_or_binary_mathieu hG
    (fun _ _ _ => ChapterA.Section02.theoremsABC_knownSimple)
    localC129Input_knownSimple).2
  exact ⟨z,hh.imp id (fun h => h.2.1)⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Double
