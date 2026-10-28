module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison.Lifting
public import Theory.SpecificGroups.SymplecticFour.ParabolicOppositeSections.Marked

/-!
# The conditional point-parabolic endgame in MS93 (3.7)

Work inside Gₐ / Dₐ, where Dₐ is the entire component-fixed part of Qₐ.
The original symplectic quotient, with one retained inner conjugation,
descends to this group and identifies the literal Q₁ image with the full
preimage of the standard point radical. Whole-core collapse identifies
Z̃ₐ with the natural kernel. The original quotient on Z̃_z and the
compatible whole-core natural map then construct coordinates on
(Z̃ₐ Z̃_z)/(Z̃ₐ ∩ Z̃_z), with square and inverse weights under the same
point-parabolic actor.

`SourceEndgame` retains the preceding whole-core and incidence conclusions,
the compatible natural action, and the source centralizer/index clauses.
The whole-core marking must be compatible with the supplied original
symplectic quotient: `Input.quotientEquiv` alone does not establish this.
No marking of the critical quotient, module inequivalence, axis conclusion,
or field-four conclusion is a record field.

For q ≠ 4 the distinct-simple-pair theorem makes the order-q image of
Ũ = C_(Z̃ₐ Z̃_z)(Q̃₁/R̃) one of the two axes. The projection index excludes
Z̃ₐ; the other axis contradicts the retained strict movement after lifting
through the full fixed attachment. Thus q = 4 and the original degree is two.
Constructing the earlier source data and proving the subsequent nonsplitting
and block recognition remain separate source obligations.

Source: Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two*,
(3.7), printed pp.876–877, especially the first paragraph of p.877. The
centralizer subscript is one; R is the original critical commutator.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
open DistanceTwoRecognition Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

omit [Finite H] [Finite F] [CharP F 2] in
private theorem edge_kernel {a t : Vertex d.radical} (c : EdgeMarking h d a t) :
    c.quotient.ker = (Q d.radical a).subgroupOf (stabilizer d.radical a) := by
  rw [←c.kernel,subgroupOf_map_subtype_eq]

omit [Finite H] [Finite F] [CharP F 2] in
private theorem fixedAttachment_le_marked_kernel {a t : Vertex d.radical}
    (c : EdgeMarking h d a t) (u : Sp F) :
    fixedAttachment d a ≤ ((MulAut.conj u).toMonoidHom.comp c.quotient).ker := by
  intro x hx
  have hxQ : x ∈ c.quotient.ker := (edge_kernel h d c).symm ▸ (show x.val ∈ Q d.radical a from hx.1)
  change u * c.quotient x * u⁻¹ = 1
  rw [show c.quotient x = 1 from hxQ]
  simp

/-- The original symplectic quotient descends through the whole fixed
attachment, retaining the single chosen inner conjugation. -/
def markedQuotient {a t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    FixedQuotient d a →* Sp F :=
  QuotientGroup.lift (fixedAttachment d a)
    ((MulAut.conj u).toMonoidHom.comp c.quotient) (fixedAttachment_le_marked_kernel h d c u)

omit [Finite H] [Finite F] [CharP F 2] in
@[simp] theorem markedQuotient_projection {a t : Vertex d.radical}
    (c : EdgeMarking h d a t) (u : Sp F) (x : stabilizer d.radical a) :
    markedQuotient h d c u (fixedProjection d a x) = u*c.quotient x*u⁻¹ := by
  exact QuotientGroup.lift_mk' (fixedAttachment d a) (fixedAttachment_le_marked_kernel h d c u) x

omit [Finite H] [Finite F] [CharP F 2] in
theorem markedQuotient_onto {a t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    Function.Surjective (markedQuotient h d c u) :=
  QuotientGroup.lift_surjective_of_surjective _ _ ((MulAut.conj u).surjective.comp c.onto) _

omit [Finite H] [Finite F] [CharP F 2] in
theorem markedQuotient_kernel {a t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    (markedQuotient h d c u).ker = layerImage d a (Q d.radical a) := by
  have he := QuotientGroup.ker_lift (fixedAttachment d a)
    ((MulAut.conj u).toMonoidHom.comp c.quotient) (fixedAttachment_le_marked_kernel h d c u)
  change (markedQuotient h d c u).ker =
    (((MulAut.conj u).toMonoidHom.comp c.quotient).ker).map (fixedProjection d a) at he
  rw [he]
  change (MonoidHom.ker _).map _ = ((Q d.radical a).subgroupOf _).map _
  congr 1
  ext x
  change u*c.quotient x*u⁻¹ = 1 ↔ x.val ∈ Q d.radical a
  rw [show (u*c.quotient x*u⁻¹ = 1) ↔ c.quotient x = 1 from (MulAut.conj u).map_eq_one_iff]
  exact show x ∈ c.quotient.ker ↔ x ∈ (Q d.radical a).subgroupOf _ from
    (edge_kernel h d c) ▸ Iff.rfl

omit [Finite H] [Finite F] [CharP F 2] in
/-- The Q-one image is the full point-radical preimage in the tilde quotient,
for the very same original marking used on both module sections. -/
theorem markedPointCore_image {a t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) :
    layerImage d a (markedPointCore h d c u) =
      pointRadicalAmbient.comap (markedQuotient h d c u) := by
  rw [layerImage,markedPointCore,subgroupOf_map_subtype_eq]
  have he : ((MulAut.conj u).toMonoidHom.comp c.quotient) =
      (markedQuotient h d c u).comp (fixedProjection d a) := by ext x; rfl
  rw [he,←comap_comap]
  exact map_comap_eq_self_of_surjective (f := fixedProjection d a) (QuotientGroup.mk'_surjective _) _

omit [Finite H] in
/-- Whole-core collapse identifies the full tilde Z with the full natural
kernel. The entire fixed attachment is retained until the projection. -/
theorem whole_layer_eq_core {g : Geometry d.radical} {a : Vertex d.radical}
    (hb : g.b d.radical = 2) (ha : color d.radical a = false)
    (hwhole : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a) :
    layerImage d a (Z d.radical a) = layerImage d a (Q d.radical a) := by
  have hZQ : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a ha (by rw [g.distance_constant a ha]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le _)
  have hQS : Q d.radical a ≤ stabilizer d.radical a := fun _ hx => hx.1
  have hUS := ((U_le_Z a).trans hZQ).trans hQS
  have hDS := (show fixedCore d.radical a ≤ Q d.radical a from inf_le_left).trans hQS
  apply le_antisymm (map_mono (subgroupOf_mono _ hZQ))
  rw [hwhole,subgroupOf_sup hUS hDS,Subgroup.map_sup]
  apply sup_le
  · exact map_mono (subgroupOf_mono _ (U_le_Z a))
  · have he : layerImage d a (fixedCore d.radical a) = ⊥ := QuotientGroup.map_mk'_self _
    exact he.le.trans bot_le

/-- Earlier geometric and action clauses for the first paragraph of p.877.
The natural marking is on the entire core modulo its full fixed attachment;
its action uses exactly the original quotient, not a freely chosen action.
The distinguished centralizer below uses Q-one, as in the printed source. -/
structure SourceEndgame {a z t : Vertex d.radical} (c : EdgeMarking h d a t) (u : Sp F) where
  whole_core : Q d.radical a = U d.radical a ⊔ fixedCore d.radical a
  /-- The full natural kernel after quotienting by Dₐ. -/
  natural : layerImage d a (Q d.radical a) ≃* Multiplicative (Vector F)
  /-- Compatibility with the retained original symplectic marking. -/
  natural_conjugation : ∀ (x : FixedQuotient d a) (v w : layerImage d a (Q d.radical a)),
    (w : FixedQuotient d a) = x*v*x⁻¹ →
      (natural w).toAdd = markedQuotient h d c u x • (natural v).toAdd
  /-- The original critical image, in the specified long-root orientation. -/
  root_image : (layerImage d a (Z d.radical z)).map (markedQuotient h d c u) =
    RootSubgroup.group 0
  opposite_normalized : (stabilizer (point F)).comap (markedQuotient h d c u) ≤
    normalizer (layerImage d a (Z d.radical z) : Set (FixedQuotient d a))
  intersection_index : (layerImage d a (Z d.radical z)).relIndex
    (layerImage d a (Z d.radical a)) = 2^n
  /-- The intersection lies in the actual relative centralizer of Q₁/R. -/
  intersection_centralizes : layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z) ≤
    relativeCentralizer h d (z := z) c u
  /-- Order q of the centralizer image in the critical quotient. -/
  centralizer_order : (layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z)).relIndex
    (relativeCentralizer h d (z := z) c u) = 2^n
  centralizer_normalized : (stabilizer (point F)).comap (markedQuotient h d c u) ≤
    normalizer (relativeCentralizer h d (z := z) c u : Set (FixedQuotient d a))
  /-- The printed clause |Ũ Z̃ₐ / Z̃ₐ| = q. -/
  projection_index : (layerImage d a (Z d.radical a)).relIndex
    (relativeCentralizer h d (z := z) c u ⊔ layerImage d a (Z d.radical a)) = 2^n
  fixed_disjoint : Disjoint (fixedCore d.radical a) (U d.radical z)
  commutator_order : Nat.card (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) = 2^n
  /-- Strict movement is retained on the original, unquotiented groups. -/
  strict_movement : 2^n < Nat.card
    (⁅Z d.radical z,markedPointCore h d c u ⊓ Q d.radical t⁆ : Subgroup (FreeAmalgam d.radical))

namespace SourceEndgame
variable {h d} {a z t : Vertex d.radical} {c : EdgeMarking h d a t} {u : Sp F}
variable (s : SourceEndgame h d (z := z) c u)
include s

/-- The earlier source data constructs the common model marking. Its root
map is the actual original symplectic quotient; its natural map is the
specified whole-core action. -/
def markedPair {g : Geometry d.radical} (path : CriticalPath d.radical g a z)
    (hb : g.b d.radical = 2) :
    ParabolicOppositeSections.MarkedPair (markedQuotient h d c u)
      (layerImage d a (Q d.radical a)) (layerImage d a (Z d.radical z)) := by
  let : IsElementaryAbelian 2 (Z d.radical z) := g.Z_elementary (by omega) z path.end_color
  have he := whole_layer_eq_core d hb path.start_color s.whole_core
  exact {
    onto := markedQuotient_onto h d c u
    kernel := markedQuotient_kernel h d c u
    natural := s.natural
    natural_conjugation := s.natural_conjugation
    root_image := s.root_image
    opposite_commutative := by
      change IsMulCommutative (((Z d.radical z).subgroupOf _).map _)
      infer_instance
    opposite_normalized := s.opposite_normalized
    intersection_index := by rw [←he]; exact s.intersection_index.trans h.field_card.symm }

omit [Finite H] [Finite F] [CharP F 2] in
/-- The critical source image has field order under the retained quotient. -/
theorem opposite_critical_image_card :
    Nat.card ((layerImage d a (Z d.radical z)).map (markedQuotient h d c u)) = 2^n := by
  rw [s.root_image,RootSubgroup.card,h.field_card]

omit [Finite F] [CharP F 2] in
/-- Normality is relative to the actual critical span. It follows from the
constructed coordinate map's kernel, with no global normality assumption. -/
theorem critical_normal {g : Geometry d.radical} (path : CriticalPath d.radical g a z)
    (hb : g.b d.radical = 2) :
    ((layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z)).subgroupOf
      (layerImage d a (Z d.radical a) ⊔ layerImage d a (Z d.radical z))).Normal := by
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite (FixedQuotient d a) := inferInstanceAs (Finite (stabilizer d.radical a ⧸ fixedAttachment d a))
  have sm : ParabolicOppositeSections.MarkedPair (markedQuotient h d c u)
      (layerImage d a (Z d.radical a)) (layerImage d a (Z d.radical z)) := by
    rw [whole_layer_eq_core d hb path.start_color s.whole_core]
    exact s.markedPair path hb
  obtain ⟨r,_,_,_⟩ := sm.coordinates
  have hk : r.map.ker =
      (layerImage d a (Z d.radical a) ⊓ layerImage d a (Z d.radical z)).subgroupOf
        (layerImage d a (Z d.radical a) ⊔ layerImage d a (Z d.radical z)) := r.kernel
  exact hk ▸ inferInstanceAs r.map.ker.Normal

omit [Finite F] [CharP F 2] in
/-- The literal critical quotient after dividing by the full fixed attachment.
Its two kernel equations identify the original coordinate axes; its action
formula uses the same original point-parabolic marking. The centralizer's
order is stated on its actual quotient image. -/
theorem critical_quotient_coordinates {g : Geometry d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    let A := layerImage d a (Z d.radical a)
    let B := layerImage d a (Z d.radical z)
    let C := A ⊔ B
    let I := (A ⊓ B).subgroupOf C
    let _ := s.critical_normal path hb
    ∃ e : (C ⧸ I) ≃* Multiplicative (F × F),
        (∀ x : C,
          (((e (QuotientGroup.mk' I x)).toAdd.1 = 0 ↔ x.val ∈ A) ∧
           ((e (QuotientGroup.mk' I x)).toAdd.2 = 0 ↔ x.val ∈ B))) ∧
        Nat.card (((relativeCentralizer h d (z := z) c u).subgroupOf C).map
          (QuotientGroup.mk' I)) = 2^n ∧
        ∀ (v : FixedQuotient d a) (hv : markedQuotient h d c u v ∈ stabilizer (point F))
          (x y : C), y.val = v*x*v⁻¹ →
          (e (QuotientGroup.mk' I y)).toAdd =
            ((determinantCharacter (point F) ⟨markedQuotient h d c u v,hv⟩ : F)^2*
               (e (QuotientGroup.mk' I x)).toAdd.1,
             (determinantCharacter (point F) ⟨markedQuotient h d c u v,hv⟩ : F)⁻¹*
               (e (QuotientGroup.mk' I x)).toAdd.2) := by
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite (FixedQuotient d a) := inferInstanceAs (Finite (stabilizer d.radical a ⧸ fixedAttachment d a))
  let A := layerImage d a (Z d.radical a)
  let B := layerImage d a (Z d.radical z)
  let C := A ⊔ B
  let I := (A ⊓ B).subgroupOf C
  have he := whole_layer_eq_core d hb path.start_color s.whole_core
  have sm : ParabolicOppositeSections.MarkedPair (markedQuotient h d c u) A B := by
    change ParabolicOppositeSections.MarkedPair _ (layerImage d a (Z d.radical a)) _
    rw [he]
    exact s.markedPair path hb
  obtain ⟨r,_,_,hr⟩ := sm.coordinates
  have hk : r.map.ker = I := r.kernel
  let _ := s.critical_normal path hb
  let e : (C ⧸ I) ≃* Multiplicative (F × F) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r.map r.onto)
  have ep (x : C) : e (QuotientGroup.mk' I x) = r.map x := rfl
  refine ⟨e,?_,?_,?_⟩
  · intro x
    rw [ep]
    exact ⟨r.first_kernel x,r.second_kernel x⟩
  · rw [←relIndex_ker,QuotientGroup.ker_mk']
    change ((A ⊓ B).subgroupOf C).relIndex
      ((relativeCentralizer h d (z := z) c u).subgroupOf C) = _
    have hWC : relativeCentralizer h d (z := z) c u ≤ C := commutatorPreimage_le _ _ _
    rw [relIndex_subgroupOf hWC]
    exact s.centralizer_order
  · intro v hv x y hy
    exact hr v hv x y hy

/-- Conditional field-four endgame on the literal source layers. The model
comparison and axis classification are derived inside the proof, and the
second-axis contradiction is lifted through the whole fixed attachment. -/
theorem field_card_eq_four {g : Geometry d.radical} (path : CriticalPath d.radical g a z)
    (hb : g.b d.radical = 2) (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c' : EdgeMarking h d z t) : Nat.card F = 4 := by
  by_contra h4
  let : Finite (stabilizer d.radical a) := finite_stabilizer d.radical a
  let : Finite (FixedQuotient d a) := inferInstanceAs (Finite (stabilizer d.radical a ⧸ fixedAttachment d a))
  have hq : 2 < Nat.card F := by
    rw [h.field_card]
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) h.nonbinary
    omega
  have he := whole_layer_eq_core d hb path.start_color s.whole_core
  have hs := (s.markedPair path hb).invariant_order_q hq h4
    (relativeCentralizer h d (z := z) c u)
    (by rw [←he]; exact commutatorPreimage_le _ _ _)
    (by rw [←he]; exact s.intersection_centralizes)
    (by rw [←he]; exact s.centralizer_order.trans h.field_card.symm)
    s.centralizer_normalized
  rcases hs with hs | hs
  · have hi := s.projection_index
    rw [←he] at hs
    rw [hs,sup_idem,relIndex_self] at hi
    have hn := h.nonbinary
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hn
    omega
  · exact source_relativeCentralizer_not_opposite h d path hb hat hzt c c' u
      s.fixed_disjoint s.commutator_order s.strict_movement hs.ge

/-- The numerical degree is obtained only after the source contradiction. -/
theorem degree_eq_two {g : Geometry d.radical} (path : CriticalPath d.radical g a z)
    (hb : g.b d.radical = 2) (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c' : EdgeMarking h d z t) : n = 2 := by
  have hh := (s.field_card_eq_four path hb hat hzt c').symm.trans h.field_card
  exact (Nat.pow_right_injective (by decide : 1 < (2:ℕ)) hh).symm
end SourceEndgame
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
