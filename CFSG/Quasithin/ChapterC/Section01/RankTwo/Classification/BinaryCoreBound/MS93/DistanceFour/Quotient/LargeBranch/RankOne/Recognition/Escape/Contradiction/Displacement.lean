module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Geometry

/-!
# Orbit-span displacement modulo a neighboring radius center

The moving-neighbor paragraph of MS93 (4.6.12)(4), printed p.911, bounds
`[V₀,V_μ/B_μ]`, where `V₀ = ⟨Z_(α+2)^G_α⟩` is the orbit span defined on
p.910. Its preceding commutator containment places `[V₀,V_μ]` in
`Z_α Z_(α+2)`. Both Z-layers have index two over Z_β, and Z_β lies in
B_μ, giving the stated bound of four.

The commutator lies in V_μ because V₀ lies in Q_β, which normalizes
V_μ. The denominator B_μ is normal inside V_μ by the earlier radius-center
identity. The quotient-image theorem uses the literal quotient homomorphism
of V_μ by this relative subgroup and proves that its image order equals
the ambient relative index. Finiteness is obtained from the local radius
group; the free amalgam is not assumed finite.

The final selector applies these results to the existing moving neighbor.
The estimate here concerns V₀. Replacing its first commutator argument by
the whole V_α is a stronger assertion absent from the cited paragraph.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(3)--(4), printed pp.910--911, with the frame notation on
p.905 and continuation on p.912.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem neighbor_color (μ : Vertex R) (hadj : Adjacent R (beta R) μ) :
    color R μ = false := by
  have hn := adjacent_color_ne R hadj
  have hb : color R (beta R) = true := rfl
  cases he : color R μ <;> simp_all

/-- The literal orbit-span commutator lies in the neighbor's radius group. -/
theorem span_neighbor_commutator_le_radius (common : CommonFacts R source geometry)
    (s : CriticalSegment geometry) (μ : Vertex R) (hadj : Adjacent R (beta R) μ) :
    ⁅orbitSpan s.middle, V R μ⁆ ≤ V R μ := by
  have hVQ : V R (alpha R) ≤ Q R (beta R) :=
    (Early.radius_le_Q common _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R))
  have hQG : Q R (beta R) ≤ stabilizer R μ := by
    rw [Q_h_eq_edge R rfl (adjacent_symm R hadj)]
    exact inf_le_left
  exact le_normalizer_iff_commutator_le_right.mp
    ((orbitSpan_le_radius _ ((cosetGraph R).dist_comm.trans s.first_distance).le).trans
      (hVQ.trans (hQG.trans (DistanceEight.V_normalized R μ))))

private theorem join_index {G : Type*} [Group G] (A C : Subgroup G)
    (hn : C ≤ normalizer A) : A.relIndex (A ⊔ C) = A.relIndex C := by
  let J := A ⊔ C
  let : (A.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hn)
  have hh := relIndex_sup_left (C.subgroupOf J) (A.subgroupOf J)
  rwa [← subgroupOf_sup le_sup_left le_sup_right, relIndex_subgroupOf le_rfl,
    relIndex_subgroupOf le_sup_right] at hh

/-- The source displacement estimate for V₀, valid for every neighbor on the
specified edge once the orbit span is contained in the midpoint kernel. -/
theorem span_neighbor_displacement_index_le_four (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (μ : Vertex R) (hadj : Adjacent R (beta R) μ) :
    (B R μ (geometry.Z_normal μ)).relIndex ⁅orbitSpan s.middle, V R μ⁆ ≤ 4 := by
  let J := Z R (alpha R) ⊔ Z R s.middle
  have hJV : J ≤ V R (alpha R) := sup_le (Z_le_VBall R _ _)
    ((Z_le_orbitSpan s.middle).trans
      (orbitSpan_le_radius _ ((cosetGraph R).dist_comm.trans s.first_distance).le))
  let : Finite (V R (alpha R)) := Early.finite_radius common _ rfl
  let : Finite J := Finite.of_injective (inclusion hJV) (inclusion_injective _)
  let : Finite (Z R s.middle) := finite_Z R _
  have hbeta : Z R (beta R) ≤ Z R (alpha R) :=
    Flags.edge_Z_le _ _ rfl (base_adjacent R)
  have hbetaB : Z R (beta R) ≤ B R μ (geometry.Z_normal μ) :=
    (Flags.edge_Z_le _ _ (neighbor_color μ hadj) (adjacent_symm R hadj)).trans
      (Early.Z_le_B common μ (neighbor_color μ hadj))
  have hnormal : Z R s.middle ≤ normalizer (Z R (alpha R)) :=
    (le_sup_right.trans hJV).trans
      ((Early.radius_le_Q common _ rfl).trans
        ((show Q R (alpha R) ≤ stabilizer R (alpha R) from fun _ hx => hx.1).trans
          (Z_normalized R _)))
  have hjoin : (Z R (alpha R)).relIndex J =
      (Z R (alpha R)).relIndex (Z R s.middle) := join_index _ _ hnormal
  have hindex : (Z R (beta R)).relIndex J ≤ 4 := by
    rw [← relIndex_mul_relIndex (Z R (beta R)) (Z R (alpha R)) J hbeta le_sup_left,
      radius.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R), hjoin]
    have hle := relIndex_le_of_le_left (L := Z R s.middle) hbeta index_ne_zero_of_finite
    rw [radius.edge_Z_index s.middle (beta R) s.middle_color (adjacent_symm R hbc)] at hle
    omega
  calc
    (B R μ (geometry.Z_normal μ)).relIndex ⁅orbitSpan s.middle, V R μ⁆ ≤
        (Z R (beta R)).relIndex ⁅orbitSpan s.middle, V R μ⁆ := by
      apply relIndex_le_of_le_left hbetaB
      exact fun hz => (index_ne_zero_of_finite : (Z R (beta R)).relIndex J ≠ 0)
        (relIndex_eq_zero_of_le_right (span_neighbor_commutator_le common radius hb s hbc hspan μ hadj) hz)
    _ ≤ (Z R (beta R)).relIndex J := relIndex_le_of_le_right
      (span_neighbor_commutator_le common radius hb s hbc hspan μ hadj) index_ne_zero_of_finite
    _ ≤ 4 := hindex

omit [Finite M] in
/-- Normality is relative to V_μ, as needed for its quotient by B_μ. -/
theorem neighbor_radius_center_normal (radius : RadiusFacts R geometry)
    (μ : Vertex R) (hadj : Adjacent R (beta R) μ) :
    ((B R μ (geometry.Z_normal μ)).subgroupOf (V R μ)).Normal := by
  rw [radius.B_eq_center μ (neighbor_color μ hadj)]
  change ((center (V R μ)).map (V R μ).subtype |>.comap (V R μ).subtype).Normal
  rw [comap_map_eq_self_of_injective (V R μ).subtype_injective]
  infer_instance

/-- The image of the actual commutator under V_μ → V_μ/B_μ has order at most
four. The subgroupOf operation loses no elements, by the proved containment. -/
theorem span_neighbor_quotient_image_card_le_four (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (μ : Vertex R) (hadj : Adjacent R (beta R) μ) :
    letI := neighbor_radius_center_normal radius μ hadj
    Nat.card (((⁅orbitSpan s.middle, V R μ⁆).subgroupOf (V R μ)).map
      (QuotientGroup.mk' ((B R μ (geometry.Z_normal μ)).subgroupOf (V R μ)))) ≤ 4 := by
  let := neighbor_radius_center_normal radius μ hadj
  rw [← relIndex_ker, QuotientGroup.ker_mk',
    relIndex_subgroupOf (span_neighbor_commutator_le_radius common s μ hadj)]
  exact span_neighbor_displacement_index_le_four common radius hb s hbc hspan μ hadj

/-- The moving neighbor selected from the source geometry satisfies the
literal V₀-displacement bound used on printed p.911. -/
theorem exists_moving_neighbor_with_span_displacement (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle) :
    ∃ μ, nu R geometry (alpha R) μ ∧ Adjacent R (beta R) μ ∧
      ⁅Z R μ, orbitSpan s.middle⁆ ≠ ⊥ ∧
      ⁅orbitSpan s.middle, V R μ⁆ ≤ V R μ ∧
      (B R μ (geometry.Z_normal μ)).relIndex ⁅orbitSpan s.middle, V R μ⁆ ≤ 4 := by
  obtain ⟨μ, hnu, hadj, hnonzero⟩ := exists_moving_neighbor common radius hb s
  exact ⟨μ, hnu, hadj, hnonzero, span_neighbor_commutator_le_radius common s μ hadj,
    span_neighbor_displacement_index_le_four common radius hb s hbc hspan μ hadj⟩
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
