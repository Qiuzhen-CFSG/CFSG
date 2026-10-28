module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.CentralizerIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Lifting

/-!
# The original field restriction from the centralizer character

The source relative centralizer is identified with the centralizer of the
constructed marked pair. Its commutator character determines its order and
projection index. The square/inverse comparison then forces it to be the
opposite layer unless the field has four elements. Original strict movement
rules out that layer after lifting through the complete fixed attachment.

The character construction and opposite fixed-core disjointness are the
remaining inputs to this assembly. The source natural marking, critical
root, full quotient, movement bound and commutator order are retained.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.OneCohomology.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
variable {H F E : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable [Field E] [Finite E] [CharP E 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

omit [Finite H] [Finite E] [CharP E 2] in
/-- Passing through the complete fixed attachment preserves the selected
root marking, including its exact inner conjugation. -/
theorem layerImage_marked_image {a : Vertex R} (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (B : Subgroup (FreeAmalgam R)) :
    (layerImage R a B).map (markedQuotient R κ hκ u) =
      (B.subgroupOf (stabilizer R a)).map ((MulAut.conj u).toMonoidHom.comp κ) := by
  rw [layerImage,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro x
  exact markedQuotient_projection R κ hκ u x

omit [Finite H] [Finite F] [CharP F 2] [Finite E] [CharP E 2] in
/-- The literal original relative centralizer agrees with that of the
marked pair. This uses the original commutator image, not a replacement. -/
theorem original_relativeCentralizer_eq
    {g : Geometry R} {a z : Vertex R} (path : CriticalPath R g a z)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E) :
    relativeCentralizer R κ z u =
      commutatorPreimage (layerImage R a (Z R a)⊔layerImage R a (Z R z))
        (pointRadicalAmbient.comap (markedQuotient R κ hκ u))
        ⁅layerImage R a (Z R a),layerImage R a (Z R z)⁆ := by
  have hZzS : Z R z≤stabilizer R a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  rw [relativeCentralizer,markedPointCore_image R κ hκ u,
    layerImage_commutator R _ _ (Z_le_stabilizer R a) hZzS]

/-- The original degree restriction reduces to the actual commutator
character and opposite fixed-core disjointness. All movement and order
premises are proved from the field-critical source configuration. -/
theorem original_degree_two_of_character
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hcritical : (Q R z).relIndex (Z R a)=2^n)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (hE : Nat.card E=2^n)
    (s : ParabolicOppositeSections.MarkedPair (markedQuotient R κ hκ u)
      (layerImage R a (Z R a)) (layerImage R a (Z R z)))
    (φ : (layerImage R a (Z R a)⊔layerImage R a (Z R z) : Subgroup (FixedQuotient R a)) →*
      Multiplicative E)
    (hφA : ∀ v : layerImage R a (Z R a),
      φ ⟨v,(show layerImage R a (Z R a)≤layerImage R a (Z R a)⊔layerImage R a (Z R z)
        from le_sup_left) v.property⟩=s.naturalLine v)
    (hφker : φ.ker=(relativeCentralizer R κ z u).subgroupOf
      (layerImage R a (Z R a)⊔layerImage R a (Z R z)))
    (hdis : Disjoint (fixedCore R a) (U R z)) : n=2 ∧ Nat.card F=4 := by
  let : Finite (stabilizer R a) := finite_stabilizer R a
  let : Finite (FixedQuotient R a) :=
    inferInstanceAs (Finite (stabilizer R a ⧸ fixedAttachment R a))
  have he := original_relativeCentralizer_eq path κ hκ u
  have hindices := centralizer_indices_of_character s φ hφA (by rw [←he]; exact hφker)
  have hq : 2<Nat.card E := by
    rw [hE]
    exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have h4 : Nat.card E=4 := by
    by_contra hn
    rcases s.invariant_order_q hq hn
      (commutatorPreimage (layerImage R a (Z R a)⊔layerImage R a (Z R z))
        (pointRadicalAmbient.comap (markedQuotient R κ hκ u))
        ⁅layerImage R a (Z R a),layerImage R a (Z R z)⁆)
      (commutatorPreimage_le _ _ _) (intersection_le_relativeCentralizer s)
      hindices.2.2.1 (relativeCentralizer_normalized s hE h.nonbinary) with hA | hB
    · have hi := hindices.2.2.2
      rw [hA,sup_idem,relIndex_self] at hi
      omega
    · have hroot := s.root_image
      rw [layerImage_marked_image κ hκ u] at hroot
      apply original_relativeCentralizer_not_opposite h hshort hinner hnsyl path hb hat hzt
        hcritical κ hκ u hE hroot hdis
      rw [he,hB]
  have hn : n=2 := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    exact hE.symm.trans h4
  exact ⟨hn,by rw [h.field_card,hn]; rfl⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison
