module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.Numerical.SourceCenterBound.DistanceGreaterFour.FixedFactor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup

/-!
# Conditional numerical assembly for the distance-greater-than-four branch

The numerical consumer needs only containment of the actual core center
in U_alpha H_alpha and an upper bound of four for H_alpha. The marked source
natural subgroup U_alpha has order eight and is normalized by H_alpha.
Multiplication therefore gives a surjection from U_alpha times H_alpha to
their join, whose order is at most 32.

The natural-section variant derives the H bound using genuine local
centrality and moving-span generation. The final applications transport
through InputSetup.coreEquiv to the original commutator core. These are
conditional source assemblies: the one-sided (4.5) center containment and
the required (4.4) source witnesses still have to be constructed. They do
not assert the complete b>4 branch or require its stronger exact-center,
distance-eight, disjointness or elementary-abelian conclusions.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4)--(4.5), pp.890--900,
especially (4.5)(iv) and (4.5.1)(v).
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceGreaterFour
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open MS93 MS93.DistanceEight MS93.DistanceEight.PathCentrality
open scoped Pointwise commutatorElement

private theorem card_join_le_product {A : Type*} [Group A] (U H : Subgroup A)
    [Finite U] [Finite H] (hn : H ≤ normalizer (U : Set A)) :
    Nat.card (U ⊔ H : Subgroup A) ≤ Nat.card U * Nat.card H := by
  let f : U × H → (U ⊔ H : Subgroup A) :=
    fun x => ⟨(x.1 : A) * (x.2 : A), mul_mem_sup x.1.property x.2.property⟩
  have hf : Function.Surjective f := by
    intro z
    have hz : (z : A) ∈ (U : Set A) * (H : Set A) := by
      rw [← coe_mul_of_right_le_normalizer_left U H hn]
      exact z.property
    obtain ⟨u, hu, h, hh, he⟩ := hz
    exact ⟨(⟨u, hu⟩, ⟨h, hh⟩), Subtype.ext he⟩
  simpa only [Nat.card_prod] using Nat.card_le_card_of_surjective f hf

universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The numerical conclusion needs only the one-sided source center containment
and the upper bound for H. Both are genuine remaining source obligations. -/
theorem center_bound_of_center_containment
    (common : CommonFacts R source geometry)
    (hcenter : (center (core R (alpha R))).map (core R (alpha R)).subtype ≤
      U R (alpha R) ⊔ H R (alpha R))
    (hH : Nat.card (H R (alpha R)) ≤ 4) :
    Nat.card (center (core R (alpha R))) ≤ 32 := by
  let S := stabilizer R (alpha R)
  have hUS : U R (alpha R) ≤ S :=
    (MS93.DistanceEight.U_le_Z R (alpha R)).trans (Z_le_stabilizer R (alpha R))
  have hHQ : H R (alpha R) ≤ Q R (alpha R) :=
    (commutator_mono
      ((MS93.DistanceEight.Vcirc_le_V R (alpha R)).trans
        (geometry.V_le_Q common.large_distance (alpha R) rfl)) le_rfl).trans
      (commutator_le_self _)
  have hHS : H R (alpha R) ≤ S := hHQ.trans (fun _ hx => hx.1)
  have hn : H R (alpha R) ≤ normalizer (U R (alpha R) : Set (FreeAmalgam R)) := by
    apply hHS.trans
    simpa only [S, alpha, stabilizer_m_base] using common.natural.normalized
  let : Finite S := finite_stabilizer R (alpha R)
  let : Finite (U R (alpha R)) :=
    Finite.of_injective (inclusion hUS) (inclusion_injective hUS)
  let : Finite (H R (alpha R)) :=
    Finite.of_injective (inclusion hHS) (inclusion_injective hHS)
  let : Finite (U R (alpha R) ⊔ H R (alpha R) : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion (sup_le hUS hHS)) (inclusion_injective _)
  have hj := card_join_le_product (U R (alpha R)) (H R (alpha R)) hn
  rw [MS93.DistanceEight.U_card R common.natural] at hj
  have hz := card_le_of_le hcenter
  rw [card_map_of_injective (core R (alpha R)).subtype_injective] at hz
  exact hz.trans (hj.trans ((Nat.mul_le_mul_left 8 hH).trans_eq (by decide)))

/-- The actual moving span and (4.4) centrality discharge the numerical H bound. -/
theorem center_bound_of_moving_span
    (common : CommonFacts R source geometry) (d : Vertex R)
    (hd : (cosetGraph R).dist d (alpha R) = 2)
    (hspan : Vcirc R (alpha R) ≤ localZSpan R d (alpha R))
    (hc : ⁅V R (alpha R), Q R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hcenter : (center (core R (alpha R))).map (core R (alpha R)).subtype ≤
      U R (alpha R) ⊔ H R (alpha R)) :
    Nat.card (center (core R (alpha R))) ≤ 32 :=
  center_bound_of_center_containment common hcenter
    (H_card_le_four_of_moving_span common rfl hd hspan hc)

/-- The genuine radius natural section gives the exact moving span used above. -/
theorem center_bound_of_natural_section
    (common : CommonFacts R source geometry)
    (s : Escape.NaturalSectionAt (alpha R) (V R (alpha R)) (Z R (alpha R)))
    (d : Vertex R) (hd : d ∈ Escape.movingNeighbors geometry (alpha R))
    (hc : ⁅V R (alpha R), Q R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype)
    (hcenter : (center (core R (alpha R))).map (core R (alpha R)).subtype ≤
      U R (alpha R) ⊔ H R (alpha R)) :
    Nat.card (center (core R (alpha R))) ≤ 32 :=
  center_bound_of_center_containment common hcenter
    (H_alpha_card_le_four_of_natural_section common s d hd hc)

/-- Apply the minimal conditional center bound through the original source
setup's literal core isomorphism. -/
theorem inputSetup_center_bound_of_center_containment
    {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {A T : Subgroup J}
    {h : Input κ A T} (s : InputSetup h)
    (common : CommonFacts s.reduction.radical s.source s.geometry)
    (hcenter : (center (core s.reduction.radical (alpha s.reduction.radical))).map
      (core s.reduction.radical (alpha s.reduction.radical)).subtype ≤
      U s.reduction.radical (alpha s.reduction.radical) ⊔
        H s.reduction.radical (alpha s.reduction.radical))
    (hH : Nat.card (H s.reduction.radical (alpha s.reduction.radical)) ≤ 4) :
    Nat.card (center (commutatorCore A)) ≤ 32 := by
  have hc := center_bound_of_center_containment common hcenter hH
  rw [Nat.card_congr (Subgroup.centerCongr s.coreEquiv).toEquiv] at hc
  exact hc

/-- Original-core application retaining precisely the genuine (4.4) section,
moving neighbor, centrality and the one-sided (4.5) center containment. -/
theorem inputSetup_center_bound_of_natural_section
    {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {A T : Subgroup J}
    {h : Input κ A T} (s : InputSetup h)
    (common : CommonFacts s.reduction.radical s.source s.geometry)
    (sectionData : Escape.NaturalSectionAt (alpha s.reduction.radical)
      (V s.reduction.radical (alpha s.reduction.radical))
      (Z s.reduction.radical (alpha s.reduction.radical)))
    (d : Vertex s.reduction.radical)
    (hd : d ∈ Escape.movingNeighbors s.geometry (alpha s.reduction.radical))
    (hc : ⁅V s.reduction.radical (alpha s.reduction.radical),
      Q s.reduction.radical (alpha s.reduction.radical)⁆ ≤
      (center (stabilizer s.reduction.radical (alpha s.reduction.radical))).map
        (stabilizer s.reduction.radical (alpha s.reduction.radical)).subtype)
    (hcenter : (center (core s.reduction.radical (alpha s.reduction.radical))).map
      (core s.reduction.radical (alpha s.reduction.radical)).subtype ≤
      U s.reduction.radical (alpha s.reduction.radical) ⊔
        H s.reduction.radical (alpha s.reduction.radical)) :
    Nat.card (center (commutatorCore A)) ≤ 32 :=
  inputSetup_center_bound_of_center_containment s common hcenter
    (H_alpha_card_le_four_of_natural_section common sectionData d hd hc)

end CFSG.Quasithin.ChapterC.BinaryMS.Numerical.SourceCenterBound.DistanceGreaterFour
