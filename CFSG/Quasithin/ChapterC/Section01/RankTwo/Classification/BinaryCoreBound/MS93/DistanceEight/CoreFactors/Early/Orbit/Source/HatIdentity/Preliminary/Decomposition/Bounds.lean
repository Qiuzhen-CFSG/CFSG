module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.ModuleAlternatives.BadEstimates.Models.Dimensions

/-!
# Three-conjugate bounds for the actual hat quotient

For this literal binary quotient action, an involution with displacement
order at most four bounds both the moving dimension and the codimension of
fixed vectors by six. The proof applies the checked three-conjugate
generation theorem and its dual. The endpoint adapter starts from the
actual subgroup commutator index and selects an involution in the marked
quotient; it does not require an involutory lift.

ActionBoundsOnPath publishes the remaining source estimates independently
of their producer and of the full fixed-seed lifting argument. Neither the
source bounds nor the requested decomposition are claimed here.
Source: Meierfrankenfeld--Stellmacher (1993), (1.1)(i), pp.832--833, and
its application in (4.5.3)(i), p.897.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
open Escape.Initial.Natural.Splitting
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

open Representation Representation.BinaryOffender
open scoped IsMulCommutative

/-- The two precise consequences of three-conjugate generation needed in the
lifting argument. The acting quotient and vector space are the literal ones. -/
def ActionBounds (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t) : Prop :=
  let := quotient_elementary earlier w
  let σ := Offenders.linearize (headAction common earlier w)
  Module.finrank (ZMod 2) (Coinvariants.ker σ) ≤ 6 ∧ fixedCodim σ ⊤ ≤ 6

private theorem involution_fixedCodim_le_two {E : Type*} [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (ρ : SL →* MulAut E) (u : SL)
    (hsmall : Nat.card (commutatorAction (zpowers (ρ u)) E) ≤ 4) :
    fixedCodim (Offenders.linearize ρ) (zpowers u) ≤ 2 := by
  let space : Subgroup E ≃o Submodule (ZMod 2) (Additive E) :=
    Subgroup.toAddSubgroup.trans (AddSubgroup.toZModSubmodule 2)
  let C := commutatorAction (zpowers (ρ u)) E
  have hc : 2 ^ Module.finrank (ZMod 2) (space C) ≤ 2 ^ 2 := by
    have he := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := space C)
    rw [Nat.card_zmod] at he
    rw [← he]
    exact hsmall
  have hd : Module.finrank (ZMod 2) (space C) ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  rw [fixedCodim_zpowers_eq_displacement_rank]
  apply (Submodule.finrank_mono (t := space C) ?_).trans hd
  rintro _ ⟨v, rfl⟩
  change ρ u v.toMul / v.toMul ∈ commutatorAction (zpowers (ρ u)) E
  rw [div_eq_mul_inv, commutatorAction_eq_closure]
  exact subset_closure ⟨⟨ρ u, mem_zpowers (ρ u)⟩, v.toMul, mul_comm _ _⟩

/-- Apply the checked three-conjugate bounds to this exact quotient action.
An involution moving at most two binary dimensions bounds both dimensions by six. -/
theorem actionBounds_of_small_displacement (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t)
    (u : SL) (hne : u ≠ 1) (htwo : u ^ 2 = 1)
    (hsmall : Nat.card (commutatorAction (zpowers (headAction common earlier w u))
      (HatQuotient b a)) ≤ 4) : ActionBounds common earlier w := by
  let := quotient_elementary earlier w
  let σ := Offenders.linearize (headAction common earlier w)
  have hd := involution_fixedCodim_le_two (headAction common earlier w) u hsmall
  have hm := ModuleAlternatives.Models.commutator_finrank_le_three_mul σ u htwo hne
  have hf := ModuleAlternatives.Models.fixedCodim_top_le_three_mul σ u htwo hne
  dsimp only [σ] at hm hf
  constructor <;> omega

/-- Endpoint actors need only have a nontrivial elementary image. No involutory
lift in the local group is postulated. The actual commutator index is retained. -/
theorem actionBounds_of_actor_index (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a b t : Vertex R} (w : Window geometry a b t)
    (J : Subgroup (FreeAmalgam R)) [IsElementaryAbelian 2 J]
    (hJ : J ≤ stabilizer R b) (hnot : ¬ J ≤ Q R b)
    (hsmall : (H R b).relIndex ⁅hatV R b a, J⁆ ≤ 4) : ActionBounds common earlier w := by
  obtain ⟨z, hz, hzQ⟩ := Set.not_subset.mp hnot
  let g : stabilizer R b := ⟨z, hJ hz⟩
  let π := localProjection source b w.color_b
  let ρ := headAction common earlier w
  have hne : π g ≠ 1 := by
    intro he
    have hk : g ∈ π.ker := he
    rw [localProjection_kernel] at hk
    exact hzQ hk
  have htwo : (π g) ^ 2 = 1 := by
    rw [← map_pow, show g ^ 2 = 1 from
      Subtype.ext (elemPow_eq_one_of_isElementaryAbelian z hz), map_one]
  apply actionBounds_of_small_displacement common earlier w (π g) hne htwo
  have hmem : ρ (π g) ∈ ((J.subgroupOf (stabilizer R b)).map π).map ρ :=
    mem_map_of_mem ρ (mem_map_of_mem π hz)
  have hle := displacement_mono (zpowers_le.mpr hmem)
  apply (card_le_of_le hle).trans
  rw [displacement_card common earlier w J hJ]
  exact hsmall

/-- The four independent action estimates on the supplied path. Their source
producer must prove the displacement bound from the earlier first facts. -/
structure ActionBoundsOnPath (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : SourcePath R a) : Prop where
  forward : ∀ (i : ℕ) (hi : Even i) (hi4 : 4 ≤ i) (hi6 : i ≤ 6),
    hatV R (p.walk.getVert (i - 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i - 2)) ⊔ Z R (p.walk.getVert (i - 2)) →
    ActionBounds common earlier (forwardWindow common earlier p hi hi4 hi6)
  backward : ∀ (i : ℕ) (hi : Even i) (hi8 : 8 ≤ i) (hi10 : i ≤ 10),
    hatV R (p.walk.getVert (i + 2)) (p.walk.getVert i) ≠
      Vcirc R (p.walk.getVert (i + 2)) ⊔ Z R (p.walk.getVert (i + 2)) →
    ActionBounds common earlier (backwardWindow common earlier p hi hi8 hi10)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Early.Orbit.Source.HatIdentity.Preliminary.Decomposition
