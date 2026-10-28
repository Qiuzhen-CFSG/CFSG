module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Preparation
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Wreath.NonBender.NormalSeed.Rank

/-!
# The normal-seed branch on the original involution centralizer

The parabolic input supplies the literal elementary-nine quotient, and
X=K_z supplies normality in G_z. The first independent obligation then
excludes three from the original component. The second recognizes its
two-core quotient, transported along the original subgroup inclusion.

The intrinsic rank and recognition inputs are proved in `Rank` and
`Recognition`. The final theorem discharges both and supplies exactly the
normal-seed contract consumed by
`NonBender.Source.nonBenderGeneration_of_remaining`. Only the independently
proved parabolic-seed input remains explicit at this boundary; `Complete`
supplies that input and applies the actual non-Bender consumer.
Source: Aschbacher--Smith 10.3.3, printed p.756.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
open Chapter3.Section02 Overgroups.Closure NormalSeed
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D}

/-- Application of the rank obligation to each original C-component. -/
theorem component_three_free_of_normalNineRank
    (hrank : NormalNineRankInput.{u}) (d : CentralizerData T D s)
    (r : ParabolicSeedData T L (d.first * d.second))
    (he : centralizerSeed T L (d.first * d.second) =
      componentSpan T L (d.first * d.second))
    {I : Subgroup G}
    (hI : I ∈ Chapter1.cComponentsIn (centralizer ({d.first * d.second} : Set G))) :
    ¬ 3 ∣ Nat.card I := by
  let H := centralizer ({d.first * d.second} : Set G)
  let X := (centralizerSeed T L (d.first * d.second)).subgroupOf H
  have h3 := hrank H (D.simpleQTKE.involution_centralizer_sqtk d.order)
    X (seed_normal_in_centralizer d he) (restricted_seed_quotient_elementaryNine r)
    (I.subgroupOf H) hI.2
  rwa [Nat.card_congr (subgroupOfEquivOfLe hI.1).toEquiv] at h3

/-- Exact normal-seed contract, conditional only on the two intrinsic
obligations. The earlier parabolic seed retains its separate producer. -/
theorem normalSeedBender_of_inputs (hrank : NormalNineRankInput.{u})
    (hrecognition : ThreeFreeRecognitionInput.{u}) (hseed : ParabolicSeedAt T) :
    NormalSeedBenderAt T := by
  intro hmany L D s d he I hI _hout
  obtain ⟨r⟩ := hseed hmany L D s d
  have h3 := component_three_free_of_normalNineRank hrank d r he hI
  let H := centralizer ({d.first * d.second} : Set G)
  let a := subgroupOfEquivOfLe hI.1
  have h3' : ¬ 3 ∣ Nat.card (I.subgroupOf H) := by
    rwa [Nat.card_congr a.toEquiv]
  have hm := hrecognition H (D.simpleQTKE.involution_centralizer_sqtk d.order)
    (I.subgroupOf H) hI.2 h3'
  let b := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  exact hm.of_mulEquiv b.symm

/-- Source 10.3.3's normal-seed obstruction and Suzuki recognition, with
only the earlier literal parabolic-seed theorem supplied explicitly. -/
theorem normalSeedBender_of_parabolicSeed (hseed : ParabolicSeedAt T) :
    NormalSeedBenderAt T :=
  normalSeedBender_of_inputs normalNineRankInput threeFreeRecognitionInput hseed

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.NonBender
