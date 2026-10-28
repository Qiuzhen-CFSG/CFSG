module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Setup
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.OriginalFrattini.Pairs
public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini

/-!
# Original A₆ source normalizer pairs and crossing involutions

The original tuple constructs the earlier A₆ setup and its compatible action.
The two inner four-groups account for every largest pair by source 2.5.12,
and conjugacy inside the actual Sylow makes both of their normalizer pairs
largest. Their bases are consequently the literal Sylow subgroups of the
normalizers. The original characteristic-two hypotheses supply the conjugate
centralizer condition in 2.5.22(1). The already proved elementary-core orbit
argument then contradicts a trivial core Frattini subgroup and gives the
original identities tˣ = zK and z = t zK.

Source: Aschbacher--Smith, 2.5.23--25, printed pp.567--568. These conclusions
supply the later rank-one and terminal-shadow source assemblies.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection
open ComponentRefinement A6Shadow.Frattini A6Shadow.OriginalFrattini
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- Original 2.5.23: both coordinates of every largest pair are the
normalizers of one of the actual inner four-groups, and conversely. -/
theorem MathieuSourceSetup.alternating_six_source_largest_pair_iff
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (U L : Subgroup G) :
    (U,L) ∈ largestLocalPairs M H ↔
      ∃ E : Subgroup G, E ≤ (S : Subgroup H).map H.subtype ⊓ K ∧ IsKleinFour E ∧
        U = (S : Subgroup H).map H.subtype ⊓ normalizer (E : Set G) ∧
        L = H ⊓ normalizer (E : Set G) := by
  let D := K.subgroupOf H
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  obtain ⟨d,hH,hK,hS,hM,_,_,_,_⟩ := original_earlier_setup c hG hempty hgen hb hstar eK
  constructor
  · intro hp
    have hpd : (U,L) ∈ largestLocalPairs d.M d.H := by simpa only [hH,hM] using hp
    have hUS : U ≤ (S : Subgroup H).map H.subtype :=
      (d.h_le_s_of_largest_pair hpd).trans_eq hS
    obtain ⟨E,hE,hfour,hL,hU,_⟩ :=
      largest_pair_four_normalizers_of_source c hG hempty hgen hb hp hUS
    exact ⟨E,hE,hfour,hU,hL⟩
  · rintro ⟨E,hE,hfour,rfl,rfl⟩
    have hEd : E ≤ d.S ⊓ d.K := by simpa only [hS,hK] using hE
    simpa only [hS,hH,hM] using
      normalizer_pairs_of_source c hG hempty hgen hb hstar d hH hK hS hM E hEd hfour

/-- The forward pair and Sylow assertions of original 2.5.23, on the
literal normalizers consumed by the terminal construction. -/
theorem MathieuSourceSetup.alternating_six_source_four_normalizers
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6)
    (E : Subgroup G) (hE : E ≤ (S : Subgroup H).map H.subtype ⊓ K)
    (hfour : IsKleinFour E) :
    (((S : Subgroup H).map H.subtype ⊓ normalizer (E : Set G),
      H ⊓ normalizer (E : Set G)) ∈ largestLocalPairs M H) ∧
      ∃ P : Sylow 2 (H ⊓ normalizer (E : Set G) : Subgroup G),
        (P : Subgroup (H ⊓ normalizer (E : Set G) : Subgroup G)).map
          (H ⊓ normalizer (E : Set G)).subtype =
            (S : Subgroup H).map H.subtype ⊓ normalizer (E : Set G) := by
  have hp := (MathieuSourceSetup.alternating_six_source_largest_pair_iff
    c hG hempty hgen hb hstar eK _ _).mpr ⟨E,hE,hfour,rfl,rfl⟩
  exact ⟨hp,(largest_pair_sylows hG c.T c.maximal c.sylow_le hp).2.2⟩

/-- The original 2.5.24--25 conclusions, including all original marks and
crossing memberships. The core is O₂(H), with no earlier-setup, quotient,
Frattini or compatible-action premise. -/
theorem MathieuSourceSetup.alternating_six_source_frattini_and_crossing
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (eK : K ≃* AlternatingSix.ShadowLocal.A6) :
    frattini (twoCore H) ≠ ⊥ ∧
      ∃ t zK x : G, orderOf t = 2 ∧ orderOf zK = 2 ∧ t ∈ twoCore H ∧ zK ∈ K ∧
        x ∈ c.T ∧ x ∉ (S : Subgroup H).map H.subtype ∧
        x ∈ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
        x ^ 2 ∈ (S : Subgroup H).map H.subtype ∧
        x⁻¹ * t * x = zK ∧ z = t * zK ∧
        centerIn ((S : Subgroup H).map H.subtype) = zpowers t ⊔ zpowers zK ∧
        centerIn (((S : Subgroup H).map H.subtype) ⊓ K) = zpowers zK ∧
        H = centralizer ({t} : Set G) := by
  let D := K.subgroupOf H
  let : D.Normal := alternatingGroup.normal_of_component_a6_of_quasithin
    (hG.quasithin.subgroup H) D ((subgroupOfEquivOfLe c.component_le).trans eK) c.component
  obtain ⟨d,hH,hK,hS,hM,hT,hz,hSC,hGt⟩ := original_earlier_setup c hG hempty hgen hb hstar eK
  have hpairs : ∀ E : Subgroup G, E ≤ d.S ⊓ d.K → IsKleinFour E →
      (d.S ⊓ normalizer (E : Set G), d.H ⊓ normalizer (E : Set G)) ∈
        largestLocalPairs d.M d.H :=
    normalizer_pairs_of_source c hG hempty hgen hb hstar d hH hK hS hM
  have hact := zConjugateActions_of_centralizer_He d (conjugate_centralizer_mem_He d)
  have hphi := frattini_ne_of_elementary_orbits d hpairs d.sourceNormalizerCondition
    (ElementaryCore.elementary_normalizer_orbit d hact)
  obtain ⟨htx,hzz⟩ := d.involution_identities_of_frattini_ne hphi
  have hzk : d.zK ∈ d.K := by
    have hh : d.zK ∈ centerIn (d.S ⊓ d.K) := d.center_sk.symm ▸ mem_zpowers d.zK
    exact hh.1.2
  refine ⟨?_,d.t,d.zK,d.x,d.t_order,d.zK_order,?_,?_,?_,?_,?_,?_,htx,?_,?_,?_,?_⟩
  · exact hSC ▸ hphi
  · simpa only [hSC] using d.t_mem
  · simpa only [hK] using hzk
  · simpa only [hT] using d.x_mem
  · simpa only [hS] using d.x_outside
  · simpa only [hS] using d.x_normalizes
  · simpa only [hS] using d.square_mem
  · simpa only [hz] using hzz
  · simpa only [hS] using d.center_s
  · simpa only [hS,hK] using d.center_sk
  · simpa only [hH] using hGt

end CFSG.Quasithin.Chapter2.Section05.ComponentSelection
