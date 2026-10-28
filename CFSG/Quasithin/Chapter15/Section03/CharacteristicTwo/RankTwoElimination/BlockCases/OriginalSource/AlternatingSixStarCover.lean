module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.LocalGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource.AlternatingSix
public import Theory.Alternating.OddCentralCovers
public import Theory.GroupTheory.PerfectCentralCoverCyclicOddSylow
public import Theory.GroupTheory.CComponent.HexacodeTheta
/-!
# Ordinary and triple covers of the actual A6 star component

The perfect core-to-star cover has kernel equal to its center. Its trivial
two-core and the alternating multiplier leave the ordinary A6 quotient or
the triple hexacode cover. In the latter case the ambient three-rank bound
puts the original theta generators in the selected component.

Source: Aschbacher–Smith 15.3.17–21 and GLS3 5.2.3, 5.2.7.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
theorem coreToStar_alternatingSix_alternatives
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hR : d.R ≤ normalizer (c.L : Set G))
    (e : starImage c.L d.R c.L ≃* alternatingGroup (Fin 6)) :
    Nonempty ((c.L ⧸ pCore 2 c.L) ≃* alternatingGroup (Fin 6)) ∨
      (Nat.card (coreToStar hR).ker = 3 ∧
        Nonempty ((c.L ⧸ pCore 2 c.L) ≃* Atlas.Codes.HexEvenAutomorphisms)) := by
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : Nontrivial (starImage c.L d.R c.L) := e.symm.injective.nontrivial
  have hne : starImage c.L d.R c.L ≠ ⊥ := (nontrivial_iff_ne_bot _).mp inferInstance
  let f := coreStarCover hR c.core_quotient_quasisimple hne
  have hz : center (starImage c.L d.R c.L) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : e x ∈ center (alternatingGroup (Fin 6)) := (centerCongr e ⟨x,hx⟩).property
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  have hk : (coreToStar hR).ker = center (c.L ⧸ pCore 2 c.L) := by
    have hh := f.comap_center
    rwa [hz,MonoidHom.comap_bot] at hh
  let q : ((c.L ⧸ pCore 2 c.L) ⧸ center (c.L ⧸ pCore 2 c.L)) ≃*
      alternatingGroup (Fin 6) :=
    f.quotientCenterEquiv.trans
      (((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e)
  let : IsQuasisimple (c.L ⧸ pCore 2 c.L) := c.core_quotient_quasisimple
  have ho : Odd (Nat.card (center (c.L ⧸ pCore 2 c.L))) :=
    Nat.not_even_iff_odd.mp (fun hh =>
      PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
        (pCore_quotient_pCore_eq_bot 2) _ le_rfl (even_iff_two_dvd.mp hh))
  rcases GLS3.Chapter5.OddCentralCovers.odd_center_alternatives 6 (by decide) q ho with hc | ⟨_,hc⟩
  · exact Or.inl ⟨GLS3.Chapter5.OddCentralCovers.alternatingEquivOfCenterCardOne 6 q hc⟩
  · exact Or.inr ⟨hk ▸ hc,GLS3.Chapter5.OddCentralCovers.triple_six_equiv_hexacode q hc⟩

theorem yplus_le_of_hexacode_quotient
    (d : LocalData G) {I : Subgroup G} (c : ComponentWitness d I)
    (hθ : theta (d.MI I) = d.Yplus) (hrI : primeRank 3 I ≤ 2)
    (f : (c.L ⧸ pCore 2 c.L) ≃* Atlas.Codes.HexEvenAutomorphisms) :
    d.Yplus ≤ c.L := by
  let K := c.L.subgroupOf I
  let a : K ≃* c.L := subgroupOfEquivOfLe (component_le c)
  let b : (K ⧸ pCore 2 K) ≃* Atlas.Codes.HexEvenAutomorphisms :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans f
  have hYN : d.Yplus ≤ normalizer (c.L : Set G) :=
    le_normalizer_iff_commutator_le_left.mpr c.commutator_eq.ge
  have hYNK : d.Yplus.subgroupOf I ≤ normalizer (K : Set I) := by
    rw [←subgroupOf_normalizer_eq (component_le c)]
    exact comap_mono hYN
  rw [←hθ]
  apply (closure_le _).mpr
  rintro x ⟨hx,hx3⟩
  let y : I := ⟨x,hx.2⟩
  have hy3 : orderOf y = 3 := by simpa only [←Subgroup.orderOf_coe] using hx3
  have hyN : y ∈ normalizer (K : Set I) :=
    hYNK (hθ ▸ subset_closure ⟨hx,hx3⟩)
  exact HexacodeTheta.order_three_mem K
    (LinearThree.Extension.SourceCases.component_in_overgroup d c) b hrI hy3 hyN

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.BlockCases.OriginalSource
