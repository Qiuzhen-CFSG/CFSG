module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.P1StrictMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.AttachmentsTrivial
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.P1Comparison.Source

/-!
# The original full-Sylow field restriction from the centralizer character

The scalar commutator character determines the relative centralizer's order
and projection index. The square/inverse comparison forces it onto the
opposite layer unless the field has four elements. The full original Sylow
movement bound excludes that layer after lifting through the complete fixed
attachment. Only opposite fixed-core disjointness remains explicit here.

Source: MS93 (3.7), printed pp.876--877.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Representation.OneCohomology.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
open OriginalStar OriginalStar.P1Comparison
variable {H F E : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable [Field E] [Finite E] [CharP E 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)

/-- The actual field-critical pair and marked point core rule out the
opposite section as the relative centralizer, once opposite disjointness
allows the complete fixed attachment to be removed. -/
private theorem original_relativeCentralizer_not_opposite
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (κ : stabilizer R a →* Sp E)
    (hκ : κ.ker=(Q R a).subgroupOf (stabilizer R a)) (u : Sp E)
    (hE : Nat.card E=2^n)
    (hroot : ((Z R z).subgroupOf (stabilizer R a)).map
      ((MulAut.conj u).toMonoidHom.comp κ)=RootSubgroup.group 0)
    (hdis : Disjoint (fixedCore R a) (U R z)) :
    ¬ layerImage R a (Z R z) ≤ relativeCentralizer R κ z u := by
  have hcritical := (original_critical_indices_eq_field_of_full_sylow
    h hshort hinner hsyl path hb hat hzt).1
  intro hcentral
  have hle := original_movement_le_critical_commutator h hinner path hb hat hzt κ u hdis hcentral
  have hRcard := original_source_field_critical_commutator_order h hshort hinner hsyl
    g hb path hat hzt
  have hstrict := original_point_core_strict_movement h hinner hsyl path hb hat hzt hcritical κ hκ u hE hroot
  let : Finite (⁅Z R a,Z R z⁆ : Subgroup (FreeAmalgam R)) :=
    Nat.finite_of_card_ne_zero (by rw [hRcard]; exact pow_ne_zero _ (by decide))
  exact (not_lt_of_ge ((Nat.card_le_card_of_injective (inclusion hle)
    (inclusion_injective hle)).trans_eq hRcard)) hstrict

/-- The original degree restriction reduces to the actual commutator
character and opposite fixed-core disjointness. All movement and order
premises are proved from the field-critical source configuration. -/
theorem original_degree_two_of_character
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {g : Geometry R} {a z t : Vertex R} (path : CriticalPath R g a z)
    (hb : g.b R=2) (hat : Adjacent R a t) (hzt : Adjacent R z t)
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
      apply original_relativeCentralizer_not_opposite h hshort hinner hsyl path hb hat hzt
        κ hκ u hE hroot hdis
      rw [he,hB]
  have hn : n=2 := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    exact hE.symm.trans h4
  exact ⟨hn,by rw [h.field_card,hn]; rfl⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
