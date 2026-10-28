module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.CoreAlternatives
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Source
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.SourceAssembly

/-!
# The original A₆ terminal contradiction from the rank-one conclusion

The original source tuple supplies the full centralizer, compatible action,
largest four-group normalizer pairs, nontrivial core Frattini subgroup and
crossing involution identities. Rank one then supplies the three core models
of 2.5.27. The terminal construction produces its elementary sixteen-group;
the original ambient even-characteristic hypothesis puts its normalizer in
the forbidden even local family.

The only later source premise retained here is 2.5.26, rank one of the actual
two-core. In particular no terminal setup, quotient model, action, fusion,
normalizer pair or finite-model premise is added to the original tuple.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
2.5.23--27 and completion of Theorem 2.1.1, printed pp.567--570.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement A6Shadow.Frattini A6Shadow.OriginalFrattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Original 2.5.27 on O₂(H), retaining only the earlier rank-one conclusion. -/
theorem MathieuSourceSetup.alternating_six_source_core_alternatives
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hrank : primeRank 2 (twoCore H) = 1) :
    Nonempty (twoCore H ≃* Multiplicative (ZMod 4)) ∨
    Nonempty (twoCore H ≃* Multiplicative (ZMod 8)) ∨
    Nonempty (twoCore H ≃* QuaternionGroup 2) := by
  obtain ⟨d, _, _, _, _, _, _, hSC, _⟩ :=
    original_earlier_setup c hG hempty hgen hb hstar eK
  have hphi := (MathieuSourceSetup.alternating_six_source_frattini_and_crossing
    c hG hempty hgen hb hstar eK).1
  have h := d.core_alternatives_of_rank_one (hSC ▸ hrank) (hSC ▸ hphi)
  let e := (MulEquiv.subgroupCongr hSC).symm
  rcases h with h | h | h
  · exact Or.inl ⟨e.trans h.some⟩
  · exact Or.inr (Or.inl ⟨e.trans h.some⟩)
  · exact Or.inr (Or.inr ⟨e.trans h.some⟩)

/-- The entire original terminal A₆ construction and contradiction, with only
the genuine preceding 2.5.26 rank conclusion still supplied by its producer. -/
theorem MathieuSourceSetup.alternating_six_source_false_of_rank_one
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (hrank : primeRank 2 (twoCore H) = 1) : False := by
  let D := K.subgroupOf H
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  obtain ⟨d,hH,hK,hS,hM,_,_,hSC,hGt⟩ :=
    original_earlier_setup c hG hempty hgen hb hstar eK
  have hpairs : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        largestLocalPairs d.M d.H :=
    normalizer_pairs_of_source c hG hempty hgen hb hstar d hH hK hS hM
  have hact := zConjugateActions_of_centralizer_He d (conjugate_centralizer_mem_He d)
  have hphi := frattini_ne_of_elementary_orbits d hpairs d.sourceNormalizerCondition
    (ElementaryCore.elementary_normalizer_orbit d hact)
  obtain ⟨htx,hz⟩ := d.involution_identities_of_frattini_ne hphi
  have halternatives := d.core_alternatives_of_rank_one (hSC ▸ hrank) hphi
  rw [d.centralizer_K] at halternatives
  have hlargest : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        localPairs (Chapter1.He G) d.M ∧
      ∀ W ∈ localBases (Chapter1.He G) d.M,
        Nat.card W ≤ Nat.card (d.S ⊓ normalizer (E : Set G) : Subgroup G) := by
    intro E hE hfour
    exact ⟨(hpairs E hE hfour).1.1, (hpairs E hE hfour).2⟩
  have hsylow : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      ∃ P : Sylow 2 (d.H ⊓ normalizer (E : Set G) : Subgroup G),
      (P : Subgroup (d.H ⊓ normalizer (E : Set G) : Subgroup G)).map
        (d.H ⊓ normalizer (E : Set G)).subtype = d.S ⊓ normalizer (E : Set G) := by
    intro E hE hfour
    exact (largest_pair_sylows d.simpleQTKE d.T d.maximalM d.t_le_m
      (hpairs E hE hfour)).2.2
  let q := A6Shadow.toConstructionSetup d halternatives hlargest hsylow htx hz
  obtain ⟨hqH,hqM,hqT,hqt,hqz⟩ :=
    A6Shadow.toConstructionSetup_coordinates d halternatives hlargest hsylow htx hz
  change q.H = d.H at hqH
  change q.M = d.M at hqM
  change q.T = (d.T : Subgroup G) at hqT
  change q.t = d.t at hqt
  change q.z = d.z at hqz
  have hzT : d.z ∈ (center (d.T : Subgroup G)).map (d.T : Subgroup G).subtype := by
    rw [← centerIn_eq_map_center, d.center_t]
    exact mem_zpowers d.z
  have hz1 : d.z ≠ 1 := by
    intro he
    have ho := d.z_order
    simp [he] at ho
  apply A6Shadow.false_of_terminal_source q
    (by rw [hqH,hqM]; exact d.star)
    (by rw [hqM]; exact d.even_empty)
    (by rw [hqt,hqH]; exact hGt.ge)
    (by rw [hqz,hqT]; exact hzT)
    (by rw [hqz]; exact hz1)
  intro A hA hp hcenter
  rw [hqT] at hcenter
  exact Chapter1.lemma_1_1_4_3 d.T (d.simpleQTKE.evenCharacteristic d.T) hA hp hcenter

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
