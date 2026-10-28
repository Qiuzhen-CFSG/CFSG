module
public import Stellmacher.SectionNine.NineEightContainedCenterPathIndex
public import Stellmacher.SectionNine.NineEightNoncontainedNormalizer
public import Stellmacher.SectionFiveToSeven.PrescribedCriticalPairNormalization

/-!
# Actual branch consequences on a prescribed critical pair

For a commuting critical pair with a prescribed first neighbor and the
terminal-center containment, transport the genuine extracted-neighbor
index, escape and noncommutation hypotheses into an ambient Section Nine
context. The extracted center and initial edge generate a proper subgroup
of the first-neighbor stabilizer. If that center lies in the initial
stabilizer, some normalized context of the same critical length satisfies
the exact path-index-two hypothesis of (9.7).

A single prescribed-edge normalization carries all vertices. W covariance
and injective conjugation preserve intersections, indices, noncontainment
and commutators. The already proved proper-normalizer and contained-center
path-index theorems then apply and their conclusions transport back.
No assertion from the unfinished numbered (9.7) or (9.8) is used.

Source: the repeated two branches in Stellmacher (9.8), printed pp.55–56
of `refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_critical_extraction_consequences
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (left right prescribed : ctx.Γ.Vertex)
    (hcritical : IsCriticalPair ctx.Γ left right)
    (hadj : ctx.Γ.adjacent left prescribed)
    (hdistance : ctx.Γ.distance left right = ctx.Γ.distance prescribed right + 1)
    (hcomm : ⁅ZAt ctx.Γ left,ZAt ctx.Γ right⁆ = ⊥)
    (hcontain : ZAt ctx.Γ right ≤ VAt ctx.Γ prescribed)
    (extracted : ctx.Γ.Vertex) (hextracted : extracted ∈ Neighborhood ctx.Γ right)
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ left)
      (GeneratedNeighborhoodV ctx.Γ left ⊓ GAt ctx.Γ extracted) 2)
    (hnot : ¬ ZAt ctx.Γ left ≤ GAt ctx.Γ extracted)
    (hnoncomm : ⁅ZAt ctx.Γ left,ZAt ctx.Γ extracted⁆ ≠ ⊥) :
    ((GAt ctx.Γ left ⊓ GAt ctx.Γ prescribed) ⊔ ZAt ctx.Γ extracted < GAt ctx.Γ prescribed) ∧
    (ZAt ctx.Γ extracted ≤ GAt ctx.Γ left →
      ∃ shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B,
        shifted.criticalPath.length = ctx.criticalPath.length ∧
        ∃ third, IsCriticalPathOffset shifted.Γ shifted.criticalPath 3 third ∧
          QuotientCardEq (VAt shifted.Γ shifted.criticalPath.firstStep)
            (VAt shifted.Γ shifted.criticalPath.firstStep ⊓ VAt shifted.Γ third) 2) := by
  let Γ := ctx.Γ
  obtain ⟨actor,path,hleft,hright,hfirst,hlength⟩ :=
    exists_criticalPath_of_critical_pair_through_neighbor ctx.sectionSeven Γ ctx.criticalPath
      left right prescribed hcritical hadj hdistance
  have hpathComm : ⁅Γ.z path.a,Γ.z path.a'⁆ = ⊥ := by
    rw [hleft,hright,z_act,z_act,← Subgroup.map_commutator]
    change (⁅ZAt Γ left,ZAt Γ right⁆).map _ = ⊥
    rw [hcomm,Subgroup.map_bot]
  let shifted : AmbientSectionNineContext H S0 S P1 P2 embedding T A B :=
    {ctx with criticalPath := path, commutator_eq := hpathComm}
  have hlong : 3 < shifted.criticalPath.length := by
    change 3 < path.length
    rwa [hlength]
  have hcontainPath : ZAt Γ path.a' ≤ VAt Γ path.firstStep := by
    change z Γ path.a' ≤ v Γ path.firstStep
    rw [hright,hfirst,z_act,v_act]
    exact Subgroup.map_mono hcontain
  have hextractedPath : Γ.act actor extracted ∈ Neighborhood Γ path.a' := by
    rw [hright]
    exact (mem_neighborhood_iff_adjacent Γ).mpr
      (adjacent_act Γ actor ((mem_neighborhood_iff_adjacent Γ).mp hextracted))
  have hindexPath : QuotientCardEq (GeneratedNeighborhoodV Γ path.a)
      (GeneratedNeighborhoodV Γ path.a ⊓ GAt Γ (Γ.act actor extracted)) 2 := by
    change Nat.card (GeneratedNeighborhoodV Γ path.a) =
      2 * Nat.card (GeneratedNeighborhoodV Γ path.a ⊓ stabilizer Γ (Γ.act actor extracted) : Subgroup G)
    rw [hleft,nine_seven_neighborhood_act,stabilizer_act,conjugateBy,
      ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective,
      Subgroup.card_map_of_injective (MulAut.conj actor⁻¹).injective]
    exact hindex
  have hnotPath : ¬ ZAt Γ path.a ≤ GAt Γ (Γ.act actor extracted) := by
    intro hle
    apply hnot
    change z Γ path.a ≤ stabilizer Γ (Γ.act actor extracted) at hle
    rw [hleft,z_act,stabilizer_act] at hle
    exact (Subgroup.map_le_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hle
  have hnoncommPath : ⁅ZAt Γ path.a,ZAt Γ (Γ.act actor extracted)⁆ ≠ ⊥ := by
    intro hzero
    apply hnoncomm
    change ⁅z Γ path.a,z Γ (Γ.act actor extracted)⁆ = ⊥ at hzero
    rw [hleft,z_act,z_act,← Subgroup.map_commutator] at hzero
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj actor⁻¹).injective).mp hzero
  constructor
  · have hproper := nine_eight_extracted_center_proper_join shifted hlong hcontainPath
      (Γ.act actor extracted) hextractedPath hindexPath hnotPath
    change (stabilizer Γ path.a ⊓ stabilizer Γ path.firstStep) ⊔ z Γ (Γ.act actor extracted) <
      stabilizer Γ path.firstStep at hproper
    rw [hleft,hfirst,stabilizer_act,stabilizer_act,z_act,conjugateBy,conjugateBy,
      ← Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective,← Subgroup.map_sup] at hproper
    exact (Subgroup.map_lt_map_iff_of_injective (MulAut.conj actor⁻¹).injective).mp hproper
  · intro hcontained
    have hcontainedPath : ZAt Γ (Γ.act actor extracted) ≤ GAt Γ path.a := by
      change z Γ (Γ.act actor extracted) ≤ stabilizer Γ path.a
      rw [hleft,z_act,stabilizer_act]
      exact Subgroup.map_mono hcontained
    exact ⟨shifted,hlength,nine_eight_contained_center_path_index shifted hlong hcontainPath
      (Γ.act actor extracted) hextractedPath hcontainedPath hindexPath hnotPath hnoncommPath⟩

end Stellmacher.SectionNine
