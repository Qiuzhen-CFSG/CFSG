module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.CentralizerSupplementSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.FieldInvolutionSource
/-!
# The original field-centralizer supplement

The checked field-involution orbit and the original index-two cyclic section
supply T = R C_T(s). In particular the literal centralizer contains an element
outside S. This discharges the supplement and outside-element premises of
Aschbacher–Smith 2.4.23(4), printed p.537, with no remaining orbit premise.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
variable {G : Type*} [Group G] [Finite G] {M : Subgroup G}
theorem source_field_centralizer_supplement
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hu : ∀ K : Subgroup G, IsMaximalTwoLocal K → (T : Subgroup G) ≤ K → K = M)
    (c : CyclicTorusSetup d T n) (s : T)
    (hs : (s : G) ∈ (d.S : Subgroup d.H).map d.H.subtype ⊓ normalizer (c.hall : Set G))
    (hs2 : orderOf s = 2)
    (hsR : (s : G) ∉ Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)) :
    let R := Stellmacher.elementaryAbelianMaxJ ((d.S : Subgroup d.H).map d.H.subtype)
    (T : Subgroup G) = R ⊔ ((T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G)) ∧
      ∃ x ∈ (T : Subgroup G) ⊓ centralizer ({(s : G)} : Set G),
        x ∉ (d.S : Subgroup d.H).map d.H.subtype := by
  have hL' := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  have hindex := (d.lemma_2_4_8_1 hG T hST hsingle hL').1
  have horbit := source_field_involution_coset_fusion d hG T hST hsingle hL hM hTM hu c
    (s:G) hs ((orderOf_coe s).trans hs2)
  have hsup := c.sylow_centralizer_supplement hST.le hindex s hs2 hs.1 hsR (by
    intro v hv hvr
    exact horbit v v.property ((orderOf_coe v).trans hv) hvr)
  refine ⟨hsup,?_⟩
  by_contra hn
  push Not at hn
  apply hST.not_ge
  rw [hsup]
  exact sup_le (sSup_le fun _ h => h.1) hn
end CFSG.Quasithin.Chapter2.LinearShadows.Single
