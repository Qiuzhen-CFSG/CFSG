module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

/-!
# The moving neighbor and the edge star inside the literal fixed preimage

The critical midpoint has noncentral displacement, so the existing
noncentral-neighbor selector applies to its actual orbit span. The proved
midpoint/edge supplement bounds its commutator with every neighboring
radius group by Z_alpha Z_c. The further bound modulo B_mu remains to be
proved; neither an order estimate nor module recognition is assumed here.

The edge star is fixed modulo Z_alpha by the first ordered residual. The
first natural quotient has no invariants, placing that star in K. The
actual cubic fixed-preimage calculation then places it in Y. Fixation of
Y by the full first actor consequently embeds the edge-star image in the
second star: its intrinsic core lies in the first full parabolic. That
full-actor fixation remains explicit, and is distinct from residual fixation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(1)--(4), printed pp.910--911; frame notation on p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
open Sections
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The actual moving neighbor exists, with all selector premises discharged. -/
theorem exists_moving_neighbor (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) :
    ∃ μ, nu R geometry (alpha R) μ ∧ Adjacent R (beta R) μ ∧
      ⁅Z R μ, orbitSpan s.middle⁆ ≠ ⊥ := by
  apply exists_noncentral_neighbor source common radius (beta R) (base_adjacent R)
    (orbitSpan s.middle) (orbitSpan_le_radius _
      ((cosetGraph R).dist_comm.trans s.first_distance).le) (orbitSpan_normalized s.middle)
  intro hzero
  apply Sections.midpoint_displacement_noncentral common radius hb s
  rw [commutator_comm] at hzero
  exact ((commutator_mono (Z_le_orbitSpan s.middle) le_rfl).trans_eq hzero).trans bot_le

/-- The moving-neighbor commutator bound is an instance of the actual
midpoint/edge supplement, before any quotient cardinality argument. -/
theorem span_neighbor_commutator_le
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (μ : Vertex R) (hμ : Adjacent R (beta R) μ) :
    ⁅orbitSpan s.middle, V R μ⁆ ≤ Z R (alpha R) ⊔ Z R s.middle := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hμc : color R μ = false := by
    have hn := adjacent_color_ne R hμ
    have hb : color R (beta R) = true := rfl
    cases he : color R μ <;> simp_all
  have hμQ : V R μ ≤ Q R (beta R) :=
    (Flags.V_le_Q geometry common.large_distance μ hμc).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R hμ))
  have hK : orbitSpan s.middle ≤ intersection s.middle :=
    le_inf (orbitSpan_le_radius _ ((cosetGraph R).dist_comm.trans s.first_distance).le) hspan
  exact ((commutator_mono hK hμQ).trans
    (Sections.intersection_commutator_edge_le_sup common radius k hb s hbc)).trans_eq (sup_comm _ _)

/-- The edge star lies in the literal denominator Y. The first quotient has
no residual-fixed vectors, and the cubic fixed-preimage calculation supplies Y. -/
theorem edgeStar_le_fixedPreimage (common : CommonFacts R source geometry)
    (radius : RadiusFacts R geometry) (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    edgeStar R geometry (alpha R) (beta R) ≤ Sections.fixedPreimage s.middle := by
  obtain ⟨k⟩ := Sections.exists_frame common radius hb
  have hEV : edgeStar R geometry (alpha R) (beta R) ≤ V R (alpha R) :=
    (Flags.edgeStar_le_star geometry _ _).trans (Flags.star_le_radius geometry _ _)
  have hEb : edgeStar R geometry (alpha R) (beta R) ≤ V R (beta R) := by
    rw [Flags.RankOne.V_eq_neighborSpan (alpha R) (beta R) rfl (base_adjacent R)]
    exact iSup_le fun t => iSup_le fun ht =>
      le_iSup_of_le t (le_iSup_of_le ht.2 le_rfl)
  have hcomm : ⁅edgeStar R geometry (alpha R) (beta R),
      Flags.RankOne.flagResidual source k.orientation⁆ ≤ Z R (alpha R) :=
    (commutator_mono hEb le_rfl).trans
      (Flags.RankOne.flag_commutator_le_Z_of_Bzero source geometry common.large_distance
        radius.toEarlyFacts k.orientation k.edge_kernel k.triple (Sections.Bzero_eq_B common radius))
  have hEK : edgeStar R geometry (alpha R) (beta R) ≤ intersection s.middle := by
    intro x hx
    let v : V R (alpha R) := ⟨x, hEV hx⟩
    have hfix : (d.quotientMap (intersection s.middle) v).toAdd ∈
        Representation.invariants (Sections.firstRepresentation common radius k s hbc d) := by
      intro g
      have hn : (g : FreeAmalgam R) ∈ normalizer (V R (alpha R)) :=
        ((Flags.RankOne.flagResidual_le source k.orientation).trans
          ((Flags.RankOne.flagParabolic_le source k.orientation).trans
            (DistanceEight.V_normalized R _))) g.property
      let w : V R (alpha R) := ⟨g * (v : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹,
        (mem_normalizer_iff.mp hn v).mp v.property⟩
      have hz : (w * v⁻¹ : V R (alpha R)) ∈ (d.quotientMap (intersection s.middle)).ker := by
        rw [d.quotientMap_kernel _ (Sections.Z_le_intersection common s.first_distance)]
        apply Sections.Z_le_intersection common s.first_distance
        have hc := hcomm (commutator_mem_commutator hx g.property)
        change ⁅x, (g : FreeAmalgam R)⁆ ∈ Z R (alpha R) at hc
        change ⁅(g : FreeAmalgam R), x⁆ ∈ Z R (alpha R)
        rw [← commutatorElement_inv]
        exact (Z R (alpha R)).inv_mem hc
      have he : d.quotientMap (intersection s.middle) w = d.quotientMap (intersection s.middle) v := by
        change d.quotientMap (intersection s.middle) (w * v⁻¹) = 1 at hz
        simpa only [map_mul, map_inv, mul_inv_eq_one] using hz
      exact (Sections.firstRepresentation_action common radius k s hbc d g v w rfl).symm.trans
        (congrArg Multiplicative.toAdd he)
    rw [Sections.firstRepresentation_invariants_eq_bot common radius k hb s hbc d] at hfix
    have hk : v ∈ (d.quotientMap (intersection s.middle)).ker := hfix
    rw [d.quotientMap_kernel _ (Sections.Z_le_intersection common s.first_distance)] at hk
    exact hk
  obtain ⟨T, hT, _⟩ := Sections.exists_marked_cubic source k
  apply le_trans _ (Sections.cubic_fixedPreimage_le common radius k hb s hbc T hT)
  exact le_commutatorPreimage hEK ((commutator_mono le_rfl (map_subtype_le _)).trans hcomm)

omit [Finite M] in
private theorem firstStar_one : Seed.firstStar geometry (1 : M) =
    edgeStar R geometry (alpha R) (beta R) := by
  have he : (MulAut.conj (embedM R (1 : M))).toMonoidHom = MonoidHom.id (FreeAmalgam R) := by
    apply MonoidHom.ext
    intro x
    simp
  simp only [Seed.firstStar, he, map_id]

/-- Fixation of Y by the full first actor puts the edge star in the actual
second starred layer. Fixation by the ordered residual alone is insufficient here. -/
theorem edgeStar_subspace_le_second_of_Y_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source)
    (hY : d.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace d.representation ((f.actor false).map source.projection)) :
    d.subspace (edgeStar R geometry (alpha R) (beta R)) ≤
      Seed.secondTildeStar (geometry := geometry) d f 1 := by
  have hEY := d.subspace_mono (edgeStar_le_fixedPreimage common radius hb s hbc d)
  rw [f.actor_eq false] at hY
  intro v hv
  apply (le_iSup (fun p : f.parabolic true =>
    Seed.firstTildeStar (geometry := geometry) d (1 * p) ⊓
      fixedSpace d.representation ((Seed.secondCore f 1).map source.projection)) 1)
  refine ⟨?_, ?_⟩
  · simp only [Subgroup.coe_one, one_mul, Seed.firstTildeStar, firstStar_one]
    exact hv
  · have hcore : Seed.secondCore f 1 = f.core true := by
      have he : (MulAut.conj (1 : M)).toMonoidHom = MonoidHom.id M := by ext m; simp
      simp only [Seed.secondCore, he, map_id]
    rw [hcore]
    intro g
    exact hY (hEY hv) ⟨g, (map_mono (f.core_le_parabolic true false)) g.property⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
