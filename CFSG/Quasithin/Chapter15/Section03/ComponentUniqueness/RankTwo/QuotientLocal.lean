module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Transport
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.CharacteristicTwo
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.TwoLocal
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.QuotientLocal.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.ComponentStructure

/-!
# The local quotient in 15.3.41

The actual component quotient now has its mapped Sylow subgroup, the required
containments and relative normality, the S₃×S₃ quotient by O_{2,Φ}, and
maximality among subgroups satisfying F*=O₂. The denominator is proved to be
a two-group, and the equivalence with L/Z(L) transports actual upstream
model identifications.

Characteristic two descends by first restricting to M∩L and then extending
by a two-group. The two-local witness is the nontrivial embedded two-core
of M_I⁺. These results assemble every field of LocalConfiguration from
the standing local setup and the earlier source conclusions.
The final theorem also gives F*(I⁺)=L⁺, simplicity, and every underlying
model alternative of 1.1.5(3), transported by the genuine central-quotient
isomorphism. Its earlier source inputs remain explicit, as required for
the subsequent assembly of 15.3.35.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
Lemma 15.3.41, printed p.1138.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.RankTwo
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- All of 15.3.41(2) in the actual centralizer quotient. The inputs are
15.3.11(1),(4),(7), the component facts preceding 15.3.41, 15.3.36(1),
and 15.3.25 for the actual outside family. No quotient-local clause is
assumed. -/
theorem componentImage_localConfiguration
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} [(L.subgroupOf I).Normal]
    (hM : IsMaximalTwoLocal d.M) (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hIeq : I = L ⊔ d.S)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hZ : IsPGroup 2 (center L)) (hLM : ¬ L ≤ d.M) (hYL : d.Yplus ≤ L)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hF : generalizedFitting (d.MI I) = pCore 2 (d.MI I))
    (hshadow : RankTwoShadow d.Yplus d.S)
    (h25 : ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A) :
    LocalConfiguration (componentImage I L L) (componentImage I L d.M)
      (componentImage I L d.Yplus) (componentImage I L d.S) := by
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hYM : d.Yplus ≤ d.M := by
    rcases d.choice with h | ⟨_, h⟩
    · exact h ▸ Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc
    · rw [h]
      exact (map_subtype_le _).trans
        (inf_le_left.trans (Chapter14.SourcePreliminaries.sourceResidual_le d.M d.Mc))
  have hS : IsPGroup 2 d.S := hP ▸ P.isPGroup'.map I.subtype
  have hFrel : generalizedFitting (d.M.subgroupOf I) = pCore 2 (d.M.subgroupOf I) := by
    apply generalizedFitting_eq_pCore_of_selfCentralizing 2
    have hc : centralizer (pCore 2 (d.MI I) : Set (d.MI I)) ≤ pCore 2 (d.MI I) := by
      rw [← hF]
      exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le
    have he := (Theory.Quasithin.centralizer_pCore_le_iff 2
      (subgroupOfEquivOfLe (show d.M ⊓ I ≤ I from inf_le_right))).mpr hc
    rwa [inf_subgroupOf_right] at he
  obtain ⟨hyle, hynormal⟩ := componentImage_normal_in_intersection I L d.M d.Yplus
    hYL (hYL.trans hLI) hN hYM
  exact {
    twoLocal := componentImage_isTwoLocal d hM hI hLI hIeq P hP hZ hLM hF h25
    sylow := componentImage_sylow I L d.S P hP
    sylow_le := componentImage_sylow_le hSM
    yplus_le := hyle
    yplus_normal := hynormal
    shadow := componentImage_rankTwoShadow hLI hIeq hS hZ hYL hshadow
    characteristicTwo := componentImage_characteristicTwo hLI hIeq hS hFrel
    maximal := componentImage_maximal hLI hIeq hZ hI P hP hYM hSM h25 }

/-- Both clauses of 15.3.41 from the permitted earlier source conclusions.
Here `hL` is the actual ordinary component chosen on p.1134, `h33` is
15.3.33(3) for that component, and `hIeq` and `hYL` are the preceding
15.3.39--40 reduction. The simple-model conclusion includes all six
alternatives; it is obtained through the actual L/Z(L) isomorphism.
Every field of the quotient's LocalConfiguration is proved. -/
theorem lemma_15_3_41_of_earlier
    (d : CharacteristicTwo.LocalData G) {I L : Subgroup G} [(L.subgroupOf I).Normal]
    (hM : IsMaximalTwoLocal d.M) (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hIeq : I = L ⊔ d.S)
    (hL : IsComponent I (L.subgroupOf I)) {z : G}
    (h33 : Candidates.ComponentStructure.Conclusions (L.subgroupOf I) d.M z)
    (P : Sylow 2 I) (hP : (P : Subgroup I).map I.subtype = d.S)
    (hYL : d.Yplus ≤ L)
    (hN : I ⊓ normalizer (d.Yplus : Set G) = d.MI I)
    (hF : generalizedFitting (d.MI I) = pCore 2 (d.MI I))
    (hshadow : RankTwoShadow d.Yplus d.S)
    (h25 : ∀ A ∈ d.Hplus, generalizedFitting A ≠ pCore 2 A) :
    IsSimpleGroup (componentImage I L L) ∧
      generalizedFitting (ComponentQuotient I L) = componentImage I L L ∧
      SimpleModel115 (componentImage I L L) ∧
      LocalConfiguration (componentImage I L L) (componentImage I L d.M)
        (componentImage I L d.Yplus) (componentImage I L d.S) := by
  let : IsQuasisimple (L.subgroupOf I) := hL.2
  let : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLI)
  have hcenter : center (L.subgroupOf I) = pCore 2 (L.subgroupOf I) :=
    IsQuasisimple.center_eq_pCore h33.odd_core
  have hZrel : IsPGroup 2 (center (L.subgroupOf I)) := by
    rw [hcenter]
    exact pCore_isPGroup
  have hZ : IsPGroup 2 (center L) :=
    hZrel.of_equiv (centerCongr (subgroupOfEquivOfLe hLI))
  have hLM : ¬ L ≤ d.M := by
    simpa only [map_subgroupOf_eq_of_le hLI] using h33.outside
  have hS : IsPGroup 2 d.S := hP ▸ P.isPGroup'.map I.subtype
  obtain ⟨hsimple, hfitting⟩ := simple_generalizedFitting_of_join hLI hIeq hS
  obtain ⟨α, _, hmodel⟩ := h33.model_action
  have hm := (simpleModel115_centralQuotient h33.odd_core hmodel).of_mulEquiv
    (centralizerQuotientComponentEquiv (L.subgroupOf I)).symm
  exact ⟨hsimple, hfitting, hm,
    componentImage_localConfiguration d hM hI hLI hIeq P hP hZ hLM hYL hN hF hshadow h25⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo

end
