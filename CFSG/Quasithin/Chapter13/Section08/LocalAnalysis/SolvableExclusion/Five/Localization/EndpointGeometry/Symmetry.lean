module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.SourceActions
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.ReversedGeneration
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Bounds
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.CriticalGeometry.FinalAssembly

/-!
# Symmetry and the two source lines in the five-primary branch

Corrected 13.8.10 and the rank-one star image construct an actual reversed
critical pair. Its graph and conjugator identities exchange the two literal
denominators, so both reversed indices are two and the rank selection remains
valid. `reversalQuotientEquiv` realizes this exchange as a group isomorphism.

The common-axis alternative descends to Uγ/A₁ and transports to UH/V₁;
13.8.5(1) and solvability exclude it. Applying corrected 13.8.10 in the
opposite orientation also proves A₁≤UH, rather than assuming this placement.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.8.10–11 and 13.8.13, printed pp.950–951, and Remark F.9.17, p.324.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
open CriticalGeometry CriticalGeometry.Reorientation
variable {G : Type*} [Group G]

open Representation.BinaryOffender
open ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer.PairConsequences.ReversedSourceData
variable {L T H V V₃ V₁ : Subgroup G} [Finite G]

omit [Finite G] in
/-- The star action excludes the precise endpoint-axis hypothesis in 13.8.11(2).
The proof descends to Uγ/A₁ and conjugates back to UH/V₁. -/
theorem no_endpoint_axis
    (c : CriticalPair L T H V) [IsElementaryAbelian 2 (Source.UH H V₃)]
    [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃) :
    ¬ HasTransvectionAxis (Source.UH H V₃) (c.Ugamma V₃)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁)
      (hUJ.trans (c.normalizes_Ugamma V₃)) := by
  have hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁ := by
    rw [commutator_comm]
    exact core_commutator_le a
  exact SectionActions.CriticalPair.no_axis_of_no_uStar_transvection c V₃ V₁ hz hQ
    hUJ hproper (no_uStar_transvection a hz hQ hs h135)

/-- Corrected 13.8.10 in the opposite orientation places the actual conjugate
line inside UH. Its alternative would give forbidden transvections on UH/V₁. -/
theorem Aone_le_of_indices
    (c : CriticalPair L T H V) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hz : H ≤ normalizer (V₁ : Set G))
    (hs : Group.IsSolvable H) (h135 : TransvectionComponentConclusion a T)
    (hγH : c.Ugamma V₃ ≤ H)
    (hUJ : Source.UH H V₃ ≤ vertexGroup L T H c.gamma)
    (hline : Nat.card V₁ = 2)
    (hDγ : Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁ < c.Ugamma V₃)
    (hi : (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex
      (Source.UH H V₃) = 2 ∧
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) = 2) :
    c.Aone V₁ ≤ Source.UH H V₃ := by
  let _ : IsElementaryAbelian 2 (c.Ugamma V₃) := IsElementaryAbelian.map _
  have hc := corrected_rank_one (c.Ugamma V₃) (Source.UH H V₃) V₁ (c.Aone V₁)
    hDγ (by
      change (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃) ≤
        (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)).relIndex (Source.UH H V₃)
      rw [hi.1, hi.2]) hi.1 (endpoint_line_card c V₁ hline)
    (hγH.trans a.normalizes) (hUJ.trans (SectionActions.CriticalPair.normalizes_Aone c V₁ hz))
  exact hc.2.resolve_right (no_axis_on_base a hγH hs h135 hDγ)

/-- Quotients of genuinely mapped subgroups, with their mapped denominators. -/
def sectionEquiv_of_maps (e : G ≃* G) (U Z U' Z' : Subgroup G)
    [(Z.subgroupOf U).Normal] [(Z'.subgroupOf U').Normal]
    (hU : U.map e.toMonoidHom = U') (hZ : Z.map e.toMonoidHom = Z') :
    (U ⧸ Z.subgroupOf U) ≃* (U' ⧸ Z'.subgroupOf U') := by
  subst U'
  subst Z'
  let _ := map_section_normal e U Z
  exact sectionEquiv e U Z

/-- The reversed UH/DH is the original Uγ/Dγ, transported by the actual
reversal conjugator. Both stabilizer adjustments are retained in r. -/
def reversalQuotientEquiv (c : CriticalPair L T H V)
    [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (c.Ugamma V₃)]
    (r : Reversal c) (hz : H ≤ normalizer (V₁ : Set G))
    (hγH : c.Ugamma V₃ ≤ H)
    (hUA : Source.UH H V₃ ≤ normalizer (c.Aone V₁ : Set G)) :
    (c.Ugamma V₃ ⧸ (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).subgroupOf
      (c.Ugamma V₃)) ≃*
    (Source.UH H V₃ ⧸ (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃)
      (r.pair.Aone V₁)).subgroupOf (Source.UH H V₃)) :=
  sectionEquiv_of_maps (MulAut.conj (transporter r : G)) _ _ _ _
    (return_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H))
    (denominators r V₃ V₁ hz hγH hUA).1.symm

/-- Actual geometric symmetry, including the rank choice for the reversed
critical pair; equality of two ranks alone is not the output. -/
theorem exists_symmetric_reversal
    (c : CriticalPair L T H V) [IsElementaryAbelian 2 (Source.UH H V₃)]
    (a : StarAction H (Source.UH H V₃) V₁) {P : Subgroup G}
    (f : RankOneFactors a P (c.Ugamma V₃))
    (hV₃ : V₃ ≤ V) (hz : H ≤ normalizer (V₁ : Set G))
    (hgeo : ∀ d : CriticalPair L T H V, EarlierGeometry d V₃ V₁)
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hline : Nat.card V₁ = 2) :
    ∃ r : Reversal c,
      (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁)).relIndex
        (Source.UH H V₃) = 2 ∧
      (Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (r.pair.Ugamma V₃) = 2 ∧
      rank (Source.starImage H (r.pair.Ugamma V₃)) = 1 ∧
      denominatorRank V₃ V₁ r.pair ≤ rank (Source.starImage H (r.pair.Ugamma V₃)) := by
  have hrank : rank (Source.starImage H (c.Ugamma V₃)) = 1 := by
    simp only [rank, f.actor_card]
    decide
  obtain ⟨r⟩ := (c.rank_one_corrected V₃ V₁ hV₃ hz (hgeo c) hcomp hrank hproper hline).2.2.1
  have hγH : c.Ugamma V₃ ≤ H := (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans
    (hgeo c).Vgamma_H
  have hUA := ((conjugateSpanBy_mono hV₃ le_rfl).trans (hgeo c).VH_endpoint).trans
    (SectionActions.CriticalPair.normalizes_Aone c V₁ hz)
  have hi := denominator_indices c V₃ V₁ a f hγH (hgeo c).Dgamma_kernel hproper
    (c.index_comparison_of_selected_rank V₃ V₁ hγH (hgeo c).Dgamma_kernel hcomp)
  have hd := denominators r V₃ V₁ hz hγH hUA
  have hret := return_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  have hend := endpoint_map r (Source.UH H V₃) (le_normalizer_conjugateSpanBy V₃ H)
  have hiH : (Source.DH (Source.UH H V₃) (r.pair.Ugamma V₃) (r.pair.Aone V₁)).relIndex
      (Source.UH H V₃) = 2 := by
    rw [hd.1]
    have hm := relIndex_map_map_of_injective
      (f := (MulAut.conj (transporter r : G)).toMonoidHom)
      (Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁) (c.Ugamma V₃)
      (MulAut.conj (transporter r : G)).injective
    rw [show (c.Ugamma V₃).map (MulAut.conj (transporter r : G)).toMonoidHom =
      Source.UH H V₃ from hret] at hm
    exact hm.trans hi.2
  have hiγ : (Source.Dgamma (r.pair.Ugamma V₃) (Source.UH H V₃) V₁).relIndex
      (r.pair.Ugamma V₃) = 2 := by
    rw [hd.2, show r.pair.Ugamma V₃ = _ from hend,
      relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hi.1
  have hcard : Nat.card (Source.starImage H (r.pair.Ugamma V₃)) = 2 := by
    have hrH : r.pair.Ugamma V₃ ≤ H :=
      (map_mono (conjugateSpanBy_mono hV₃ le_rfl)).trans (hgeo r.pair).Vgamma_H
    rw [starImage_card H (r.pair.Ugamma V₃) hrH,
      ← inf_relIndex_left, ← (hgeo r.pair).Dgamma_kernel]
    exact hiγ
  have hr : rank (Source.starImage H (r.pair.Ugamma V₃)) = 1 := by
    simp only [rank, hcard]
    decide
  exact ⟨r, hiH, hiγ, hr, by simp only [denominatorRank, hiH, hr]; decide⟩

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
