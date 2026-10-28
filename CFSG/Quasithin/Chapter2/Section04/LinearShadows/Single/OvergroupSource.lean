module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CatalogueSetupSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CenterNormalizerSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.Source
/-!
# Complete source normalizers and TI for the single natural block

A failed centralizer bound constructs an actual even-center quasisimple
component with its original Γ₀ catalogue context. The complete catalogue
contradiction eliminates it. The preceding center-normalizer and TI argument
then proves the unique maximal two-local overgroup of the block.

Every source hypothesis is retained. The universal A/B/C and local C.1.29
inputs are discharged by the completed known-simple source producers.
Source: Aschbacher–Smith, 2.4.11, printed pp.531–532.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}

theorem source_center_centralizer_le_normalizer
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    ∀ z ∈ (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype,
      z ≠ 1 → centralizer ({z} : Set G) ≤ normalizer (d.block.map d.H.subtype : Set G) := by
  intro z hz hz1
  by_contra hn
  have hZ : center (d.block.map d.H.subtype) ≠ ⊥ := by
    intro he
    rw [he,Subgroup.map_bot,mem_bot] at hz
    exact hz1 hz
  obtain ⟨X,K,P,w,hLK,hK,hcore,h2,⟨c⟩⟩ :=
    source_center_centralizer_catalogue_setup d hG T hST hsingle hL hM hTM hunique z hz hz1 hn
  let := hK
  exact source_overcomponent_catalogue_false d hG T hST hsingle hL hM hTM hunique
    hZ K hLK.le hcore X P w c h2

/-- Original 2.4.11(2), including the literal unique maximal two-local overgroup. -/
theorem lemma_2_4_11_2
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M) :
    IsMaximalTwoLocal (normalizer (twoCore d.H : Set G)) ∧
      {X : Subgroup G | IsMaximalTwoLocal X ∧ d.block.map d.H.subtype ≤ X} =
        {normalizer (twoCore d.H : Set G)} :=
  lemma_2_4_11_2_of_centralizers d hG T hST hsingle hL hM hTM hunique
    (source_center_centralizer_le_normalizer d hG T hST hsingle hL hM hTM hunique)

/-- Original 2.4.11(3), with the actual embedded center and core normalizer. -/
theorem lemma_2_4_11_3
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥) :
    let Z := (center (d.block.map d.H.subtype)).map (d.block.map d.H.subtype).subtype
    ChapterI.Section06To08.IsTISubgroup Z ∧
      normalizer (twoCore d.H : Set G) = normalizer (Z : Set G) := by
  have hc := source_center_centralizer_le_normalizer d hG T hST hsingle hL hM hTM hunique
  exact ⟨source_center_TI_of_centralizers d hG T hST hsingle hL hM hTM hunique hZ hc,
    (lemma_2_4_11_1 d hG T hST hsingle hL hM hTM hunique).trans
      (source_center_normalizer_of_centralizers d hG T hST hsingle hL hM hTM hunique hZ hc).symm⟩
end CFSG.Quasithin.Chapter2.LinearShadows.Single
