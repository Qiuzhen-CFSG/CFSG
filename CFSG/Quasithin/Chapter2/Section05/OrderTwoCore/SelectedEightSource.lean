module
public import CFSG.Quasithin.Chapter2.Section05.OrderTwoCore.PairEightSource
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.SelectedLargestPairSource
/-!
# The selected elementary eight in original 2.5.21

The genuine Γ* selection supplies the largest pair in the prescribed Sylow.
At core order two its four-group yields the elementary eight and its exact
normalizer. The original outside normalizer element is chosen internally;
its conjugate eight escapes the original Sylow orbit.
Source: Aschbacher--Smith 2.5.9--13 and 2.5.21, printed pp.557--559,565.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement ClassificationModels A6Shadow.Frattini
variable {G : Type*} [Group G] [Finite G] {H K M : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem MathieuSourceSetup.selected_eight_of_core_card_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K) (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hcard : Nat.card (twoCore H) = 2) :
    ∃ U L E : Subgroup G, (U,L) ∈ largestLocalPairs M H ∧
      U ≤ (S : Subgroup H).map H.subtype ∧
      E ≤ (S : Subgroup H).map H.subtype ⊓ K ∧ IsKleinFour E ∧
      let F := E ⊔ twoCore H
      F ≤ (S : Subgroup H).map H.subtype ∧ IsElementaryAbelian 2 F ∧ Nat.card F=8 ∧
      K ⊓ F=E ∧ centerIn ((S : Subgroup H).map H.subtype) ≤ F ∧
      L=H ⊓ normalizer (F:Set G) ∧
      U=(S : Subgroup H).map H.subtype ⊓ normalizer (F:Set G) ∧
      (c.T:Subgroup G) ⊓ normalizer (F:Set G)=U ∧
      ∃ x:G, x∈c.T ∧ x∉(S:Subgroup H).map H.subtype ∧
        x∈normalizer ((S:Subgroup H).map H.subtype:Set G) ∧
        x^2∈(S:Subgroup H).map H.subtype ∧
        ∀s∈(S:Subgroup H).map H.subtype,F.conjBy x⁻¹≠F.conjBy s⁻¹ := by
  obtain ⟨U,L,hp,hUS,_⟩ := MathieuSourceSetup.exists_largest_pair_in_sylow c hstar
  obtain ⟨E,hES,hE,hFS,hFe,hFc,hEK,hZF,hLF,hUF,hTF,hescape⟩ :=
    largest_pair_eight_of_core_card_two c hG hempty hgen hb hp hUS hcard
  obtain ⟨x,hxT,hxS,hxN,hx2⟩ := exists_outside_normalizer_square_mem
    ((S:Subgroup H).map H.subtype) (c.T:Subgroup G) c.T.isPGroup' c.sylow_lt
  exact ⟨U,L,E,hp,hUS,hES,hE,hFS,hFe,hFc,hEK,hZF,hLF,hUF,hTF,
    x,hxT,hxS,hxN,hx2,hescape x hxT hxS⟩
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
