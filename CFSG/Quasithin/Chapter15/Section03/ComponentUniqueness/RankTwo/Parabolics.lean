module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Reductions
public import Theory.SpecificGroups.BinaryLinear.FourParabolicRadical

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Models
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField

/-!
# The parabolic contradiction in the rank-two component argument

Once the component-action quotient and Y₊S are identified with PSL₄(2)
and its end-node parabolic, the actual radical has order sixteen and
irreducible conjugation action. The four-group V₂ maps into that radical
because it is a normalized two-subgroup of Y₊S. The existing centralizer
quotient argument proves that its image is nontrivial from V₂ = [V₂,Y₊].
Its order is at most four, giving the contradiction without assuming that
V₂ embeds in the quotient.

The source action alternatives first select the small binary models or a
larger-field rank-two Borel. The larger-field argument forces PSL₃(4) and
bounds the Borel's three-rank even through a central two-cover. In the binary
branch, trivial diagram action and characteristic-two maximality exclude
PSL₅(2) and construct the marked PSL₄(2) parabolic used above.

`no_characteristicTwo_of_source` assembles both contradictions in the original
ambient group, using only the supplied preceding component and local action
facts. The selected Borel is transported from I to L with its actual Sylow
marking. No parabolic recognition, radical, centerlessness or Borel-rank
premise remains. The five-clause conclusion of 15.3.35 is assembled separately
by the rank-two theorem owner.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139. The ambient group is the source's I, so the
normality instance for L asserts relative normality in I.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
open BinaryLinear.FourParabolicRadical
variable {G : Type*} [Group G] [Finite G]

/-- The recognized end-node parabolic cannot contain the source's normalized
four-group. The radical, its order, its action, and containment of the plane
image are proved here; only the actual marked group equivalence is an input. -/
theorem no_endNodeParabolic
    (L Yplus J V₂ : Subgroup G) [L.Normal]
    (hYL : Yplus ≤ L) (hV : ⁅V₂, Yplus⁆ = V₂) (hcardV : Nat.card V₂ = 4)
    (hVJ : V₂ ≤ J) (hJV : J ≤ normalizer (V₂ : Set G))
    (e : CentralizerQuotient L ≃* Lin)
    (hJ : J.map (e.toMonoidHom.comp (centralizerQuotientMap L)) =
      BinaryLinear.parabolic plane) : False := by
  let q := centralizerQuotientMap L
  let R := (BinaryLinear.radical plane).comap e.toMonoidHom
  have hR : R.map e.toMonoidHom = BinaryLinear.radical plane :=
    Subgroup.map_comap_eq_self_of_surjective e.surjective _
  have hcardR : Nat.card R = 16 := by
    rw [Nat.card_congr (e.subgroupMap R).toEquiv]
    change Nat.card (R.map e.toMonoidHom) = 16
    rw [hR]
    exact card_radical
  have hp : IsPGroup 2 V₂ := IsPGroup.of_card (n := 2) hcardV
  have hVR : V₂.map q ≤ R := by
    apply (map_le_iff_le_comap).mp
    rw [map_map]
    rw [← twoCore_eq_radical]
    apply le_pCoreIn_of_normalizes (hp.map _)
    · rw [← hJ]
      exact map_mono hVJ
    · rw [← hJ]
      exact (map_mono hJV).trans (V₂.le_normalizer_map _)
  apply no_irreducible_sixteen_radical L Yplus J V₂ hYL hV hcardV hJV R hcardR hVR
  intro W hWR hWN
  have hWP : W.map e.toMonoidHom ≤ BinaryLinear.radical plane :=
    hR ▸ map_mono hWR
  have hPW : BinaryLinear.parabolic plane ≤
      normalizer (W.map e.toMonoidHom : Set Lin) := by
    rw [← hJ, ← map_map]
    exact (map_mono hWN).trans (W.le_normalizer_map e.toMonoidHom)
  rcases radical_irreducible (W.map e.toMonoidHom) hWP hPW with hz | ht
  · left
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hz
  · right
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    exact ht.trans hR.symm

omit [Finite G] in
private theorem selectionSetup {I L M Yplus S : Subgroup G} [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S) :
    Selection.Setup (L.subgroupOf I) (M.subgroupOf I) (Yplus.subgroupOf I)
      (S.subgroupOf I) := by
  let := c.component_quasisimple
  refine ⟨IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe c.component_le).symm,
    comap_mono c.yplus_le, ?_, ?_, c.quotient_local⟩
  · apply Subgroup.map_injective I.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le c.component_le,
      map_subgroupOf_eq_of_le (c.join_eq ▸ le_sup_right)]
    simpa only [← MonoidHom.range_eq_map, range_subtype] using c.join_eq.symm
  · obtain ⟨P, hP⟩ := c.sylow
    refine ⟨P, ?_⟩
    apply Subgroup.map_injective I.subtype_injective
    rw [hP, map_subgroupOf_eq_of_le (c.join_eq ▸ le_sup_right)]

private theorem borelOverSylow_map_subtype {I L S : Subgroup G}
    (hLI : L ≤ I) (hSI : S ≤ I) {B : Subgroup I}
    (hB : BorelOverSylow (L.subgroupOf I) (S.subgroupOf I) B) :
    BorelOverSylow L S (B.map I.subtype) := by
  obtain ⟨P, hP, hB⟩ := hB
  let e := subgroupOfEquivOfLe hLI
  have he : Function.Surjective e.toMonoidHom := e.surjective
  have hmap (A : Subgroup (L.subgroupOf I)) :
      (A.map e.toMonoidHom).map L.subtype =
        (A.map (L.subgroupOf I).subtype).map I.subtype := by
    rw [map_map, map_map]
    rfl
  refine ⟨P.mapSurjective he, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective, hmap, hP, map_inf _ _ _ I.subtype_injective,
      map_subgroupOf_eq_of_le hSI, map_subgroupOf_eq_of_le hLI]
  · change B.map I.subtype =
      (normalizer (((P : Subgroup (L.subgroupOf I)).map e.toMonoidHom) : Set L)).map L.subtype
    rw [hB, ← map_equiv_normalizer_eq, hmap]
    rfl

/-- The small binary branch cannot contain the source's normalized four-group.
The genuine local configuration constructs the marked end-node parabolic;
its radical and irreducibility are supplied by the concrete model calculation.
No marked equivalence or radical premise is assumed. -/
theorem no_smallBinaryModel
    (L MI Yplus S V₂ : Subgroup G) [L.Normal]
    (d : Selection.Setup L MI Yplus S)
    (hN : normalizer (Yplus : Set G) = MI)
    (hmodel : SmallBinaryModel (centralizerQuotientComponent L))
    (hV : ⁅V₂, Yplus⁆ = V₂) (hcardV : Nat.card V₂ = 4)
    (hVS : V₂ ≤ S) (hSV : S ≤ normalizer (V₂ : Set G)) : False := by
  let := d.quasisimple
  obtain ⟨_, _, e, he⟩ := BinaryRecognition.recognize_quotient_of_source
    L MI Yplus S d.yplus_le d.generated d.sylow hN hmodel d.quotient_local
  exact no_endNodeParabolic L Yplus (Yplus ⊔ S) V₂ d.yplus_le hV hcardV
    (hVS.trans le_sup_right)
    (sup_le (le_normalizer_iff_commutator_le_left.mpr hV.le) hSV) e he

/-- The characteristic-two contradiction in the final proof of 15.3.35,
printed p.1139, with the component normal only inside I.

`c` contains the preceding component conclusions of 15.3.33 and 15.3.39--41;
`a`, `natural`, `hV` and `hSV` retain the earlier natural action and plane
facts of 15.3.2, 15.3.7, 15.3.10--11 and 15.3.36. The action of the source
involution is literally conjugation on the relative component in I.
`hBaction` supplies the earlier Borel normalization and literal {2,3}-residual
centralization used on p.1139, only in the selected larger-field branch.

All alternatives, actual model markings, field restrictions and radical
premises are discharged here. In particular the larger-field contradiction
works for central two-covers, without asserting centerlessness from O(L)=1.
The owner of 15.3.35 must supply these preceding inputs and assemble its
five conclusions; this theorem completes its characteristic-two exclusion. -/
theorem no_characteristicTwo_of_source
    (I L M Y S V V₁ V₂ Yplus : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (a : NonCharacteristicTwo.ActionSetup M Y S V V₁ V₂ Yplus)
    (natural : NaturalOrthogonalAction M V)
    {z : I} {α : MulAut (L.subgroupOf I)}
    (action : Selection.SourceAction (L.subgroupOf I) (S.subgroupOf I) z α)
    (hV : ⁅V₂, Yplus⁆ = V₂) (hSV : S ≤ normalizer (V₂ : Set G))
    (hBaction : ∀ B : Subgroup G,
      LargerFieldRankTwoModel (componentImage I L L) →
      BorelOverSylow L S B → Yplus ≤ B →
      B ≤ normalizer ((⁅V, Yplus⁆ : Subgroup G) : Set G) ∧
      closure {x : G | x ∈ B ∧ Nat.Coprime (orderOf x) 6} ≤
        centralizer (V : Set G)) : False := by
  have hSI : S ≤ I := c.join_eq ▸ le_sup_right
  have hYI : Yplus ≤ I := c.yplus_le.trans c.component_le
  have hVS : V₂ ≤ S := a.second_le.trans a.le_sylow
  have hVI : V₂ ≤ I := hVS.trans hSI
  let d := selectionSetup c
  rcases Selection.alternatives d action with hsmall | ⟨hlarge, B, hB, hYB⟩
  · have hNI : normalizer (Yplus.subgroupOf I : Set I) = M.subgroupOf I := by
      rw [← subgroupOf_normalizer_eq hYI]
      ext x
      exact ⟨fun hx => (c.normalizer_eq.le ⟨x.property, hx⟩).1,
        fun hx => (c.normalizer_eq.ge ⟨hx, x.property⟩).2⟩
    have hVc : ⁅V₂.subgroupOf I, Yplus.subgroupOf I⁆ = V₂.subgroupOf I := by
      apply Subgroup.map_injective I.subtype_injective
      rw [map_commutator, map_subgroupOf_eq_of_le hVI,
        map_subgroupOf_eq_of_le hYI, hV]
    have hcard : Nat.card (V₂.subgroupOf I) = 4 :=
      (Nat.card_congr (subgroupOfEquivOfLe hVI).toEquiv).trans a.second_card
    have hSVI : S.subgroupOf I ≤ normalizer (V₂.subgroupOf I : Set I) := by
      rw [← subgroupOf_normalizer_eq hVI]
      exact comap_mono hSV
    exact no_smallBinaryModel (L.subgroupOf I) (M.subgroupOf I) (Yplus.subgroupOf I)
      (S.subgroupOf I) (V₂.subgroupOf I) d hNI hsmall hVc hcard (comap_mono hVS) hSVI
  · have hB' := borelOverSylow_map_subtype c.component_le hSI hB
    have hYB' : Yplus ≤ B.map I.subtype := by
      simpa only [map_subgroupOf_eq_of_le hYI] using map_mono (f := I.subtype) hYB
    obtain ⟨hBN, hres⟩ := hBaction (B.map I.subtype) hlarge hB' hYB'
    have hnoncentral : ¬ Yplus ≤ centralizer (V : Set G) := by
      intro hc
      have hb : V₂ = ⊥ := hV.symm.trans (commutator_eq_bot_iff_le_centralizer.mpr
        (a.second_le.trans (le_centralizer_iff.mp hc)))
      have hcard := V₂.card_eq_one.mpr hb
      have hfour := a.second_card
      omega
    exact HigherField.no_larger_field_component_borel I L M Y S V V₁ V₂ Yplus
      (B.map I.subtype) c ⟨natural, a, hnoncentral, hBN, hres⟩ hlarge hB' hYB'

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics
