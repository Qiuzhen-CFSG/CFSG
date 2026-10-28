module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.InnerEdge
public import Theory.Representation.BinaryConjugationSection.FiniteOffenderIndex
public import Theory.GroupTheory.FaithfulNormalRestriction

/-!
# Natural recognition on the actual secondary quotient

Choose the critical endpoint whose secondary image is smaller. The paired
q-factor estimate makes the opposite image an offender on A/Z. Nontrivial
component action, proved using the full inner edge, and simplicity give a
faithful ambient action. The existing FF classification then recognizes the
canonical moved section at the original field degree. The final constructor
makes the endpoint choice and supplies the original quotient coordinates.

This retains the full fixed layer of A/Z. Its elimination, the sharp paired
image orders and the whole-core contradiction still require proof.
Source: MS93 (3.6), printed p.871; Aschbacher--Smith B.4.2 and B.5.1.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource Sp4Four.CoreReconstruction
/-- Natural recognition of the canonical moved section, with the field degree
and literal ambient action retained. -/
@[expose] def NaturalMovedSectionAtDegree
    {J V : Type*} [Group J] [AddCommGroup V] [Module (ZMod 2) V]
    (σ : Representation (ZMod 2) J V) (C : Subgroup J) [C.Normal] (n : ℕ) : Prop :=
  Function.Injective σ ∧ IsIrrPlus σ C (subspaceCommutator σ ⊤ C) ∧
    ∃ E : BinaryField, E.degree = n ∧
      Nonempty (ActionEquiv ((MovedSection.ofNormal σ C).action.comp C.subtype) (binarySymplectic E))

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private def reverse_secondary_path
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    CriticalPath d.radical g z a := {
  start_color := path.end_color
  walk := path.walk.reverse
  shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
  critical := critical_reverse d.radical g
    (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d))
    a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
    z path.end_color path.critical }

omit h [Finite H] [Finite F] [CharP F 2] [Field F] in
private theorem opposite_nonfrattini
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ¬ core d.radical z ≤
      (frattini (Q d.radical z)).map (Q d.radical z).subtype ⊔ X d.radical z := by
  obtain ⟨v,hv⟩ := exists_mVertex_of_color d.radical path.start_color
  have he : act d.radical v (alpha d.radical) = a := by
    rw [hv]
    simp only [alpha,act_mVertex,one_mul]
  exact nonfrattini_at_vertex d.radical
    ((nonfrattini_act_iff d.radical v (alpha d.radical)).mp (he.symm ▸ hlarge))
    path.end_color

/-- The opposite secondary image is elementary, with its literal index as order. -/
theorem replacement_secondary_actor_image
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    {J : Type*} [Group J] (κ : stabilizer d.radical a →* J)
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    IsElementaryAbelian 2 ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
      Nat.card ((A'.subgroupOf (stabilizer d.radical a)).map κ) =
        (Q d.radical a).relIndex A' := by
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let S := stabilizer d.radical a
  let rev := reverse_secondary_path h d path hb
  have hlarge' := opposite_nonfrattini d path hlarge
  have hA'Q := (replacement_secondary_orbit_bounds h d rev hb hzt hat hlarge').1
  have hA'S : A' ≤ S := hA'Q.trans
    (Q_le_stabilizer_of_dist_two d.radical z a path.end_color (by
      rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color]
      exact hb))
  obtain ⟨E,hE,β,hβk,hβe,hβc,hβbound⟩ :=
    replacement_secondary_image h d rev hb hzt hat hlarge'
  let f := κ.comp (inclusion hA'S)
  have hfR : f.range = (A'.subgroupOf S).map κ := by
    rw [MonoidHom.range_comp,inclusion_range]
  have hfk : f.ker = β.ker := by
    apply map_injective A'.subtype_injective
    rw [hβk]
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      refine ⟨u.property,?_⟩
      exact hk ▸ mem_map_of_mem S.subtype (show inclusion hA'S u ∈ κ.ker from hu)
    · rintro ⟨hx,hq⟩
      refine ⟨⟨x,hx⟩,?_,rfl⟩
      obtain ⟨s,hs,he⟩ := (hk.symm ▸ hq : x ∈ κ.ker.map S.subtype)
      have heq : s = ⟨x,hA'S hx⟩ := Subtype.ext he
      change κ ⟨x,hA'S hx⟩ = 1
      change κ s = 1 at hs
      rwa [heq] at hs
  let e := (QuotientGroup.quotientKerEquivRange f).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hfk).trans (QuotientGroup.quotientKerEquivRange β))
  let := hβe
  have hel : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hc : Nat.card f.range = (Q d.radical a).relIndex A' :=
    Sp4Four.SourceComparison.quotient_image_card A' S (Q d.radical a) hA'S κ hk
  exact ⟨hfR ▸ hel,hfR ▸ hc⟩

/-- The paired q-factor estimate makes the larger opposite image an offender. -/
theorem replacement_secondary_offender_of_index_le
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (horder : (Q d.radical z).relIndex
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) ≤
      (Q d.radical a).relIndex
        (Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)))
    {J V : Type*} [Group J] [Finite J] [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* J)
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    IsOffender σ ((A'.subgroupOf (stabilizer d.radical a)).map κ) := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  let S := stabilizer d.radical a
  let B := (A'.subgroupOf S).map κ
  let C := commutatorPreimage A A' (Z d.radical a)
  let : Finite S := finite_stabilizer _ _
  let : Finite A := Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  obtain ⟨hel,hcard⟩ := replacement_secondary_actor_image h d path hb hat hzt hlarge κ hk
  have hprod := (replacement_paired_centralizer_index h d path hb hat hzt hlarge).1
  have hcp : 0 < C.relIndex A := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hqcard : 2^n ≤ Nat.card B := by
    calc
      _ ≤ 2^n * C.relIndex A := by simpa using Nat.mul_le_mul_left (2^n) hcp
      _ ≤ (Q d.radical z).relIndex A := hprod
      _ ≤ (Q d.radical a).relIndex A' := horder
      _ = _ := hcard.symm
  have hne : B ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hqcard
    have hfour : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by decide) h.nonbinary
    norm_num at hfour
    omega
  refine BinaryConjugationSection.offender_of_section_index_of_finite σ κ c A' C
    ?_ ⟨hne,hel⟩ ?_
  · rw [commutator_comm]
    exact commutator_commutatorPreimage_le A A' (Z d.radical a)
      (c.section_le.trans (Z_normalized d.radical a))
  · calc
      C.relIndex A ≤ 2^n*C.relIndex A := by
        simpa using Nat.mul_le_mul_right (C.relIndex A) (show 1 ≤ 2^n from Nat.succ_le_of_lt (pow_pos (by decide) _))
      _ ≤ (Q d.radical z).relIndex A := hprod
      _ ≤ (Q d.radical a).relIndex A' := horder
      _ = _ := hcard.symm

/-- Nontrivial component movement gives faithfulness; FF recognition identifies
the actual moved quotient at the original field degree. -/
theorem replacement_secondary_moved_natural_of_index_le
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (horder : (Q d.radical z).relIndex
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) ≤
      (Q d.radical a).relIndex
        (Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup))
    (hk : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hL : ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
      replacementComponent d)
    (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup) V)
    (c : BinaryConjugationSection (stabilizer d.radical a)
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z))
      (Z d.radical a) (σ.comp κ)) :
    let := replacementComponent_normal h d
    NaturalMovedSectionAtDegree σ (replacementComponent d) n := by
  let C := replacementComponent d
  let := replacementComponent_normal h d
  let : IsSimpleGroup C := (replacement_component_image_structure h d).2.2.1
  let : IsQuasisimple C := (replacement_component_image_structure h d).2.2.2.1
  have hcent : centralizer (C : Set (d.overgroup ⧸ pCore 2 d.overgroup)) = ⊥ :=
    (replacement_component_image_structure h d).2.2.2.2
  have hmove := secondary_component_action_nontrivial d κ C hL σ c
    (replacement_secondary_moves h d path hb hat hzt hlarge)
  have hfC : Function.Injective (σ.comp C.subtype) := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rcases (σ.comp C.subtype).normal_ker.eq_bot_or_eq_top with he | he
    · exact he
    · obtain ⟨b,v,hv⟩ := hmove
      have hbker : b ∈ (σ.comp C.subtype).ker := he.symm ▸ mem_top _
      have heq : σ b.val = 1 := hbker
      exact (hv (congrArg (fun f : Module.End (ZMod 2) V => f v) heq)).elim
  have hf := σ.injective_of_injective_normal_restriction C hfC hcent
  let : Finite (stabilizer d.radical a) := finite_stabilizer _ _
  let : Finite (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) :=
    Finite.of_injective (inclusion c.section_le) (inclusion_injective _)
  let : Finite V := Finite.of_surjective (fun a => (c.coordinates a).toAdd)
    (Multiplicative.toAdd.surjective.comp c.onto)
  have hff : IsFFModule σ := ⟨_,replacement_secondary_offender_of_index_le h d
    path hb hat hzt hlarge horder κ hk σ c⟩
  exact ⟨hf,ff_card_sp_moved_natural σ C F h.field_card h.nonbinary
    (replacement_component_image_card h d) hcent (replacement_component_image_sqtk h d) hf hff⟩

/-- The actual secondary quotient action with natural moved section. Its
coordinate map is the original quotient by the full endpoint Z-layer. -/
@[expose] def HasSecondaryNaturalSection
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) : Prop :=
    let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
    let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
    let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
    let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
    let := replacementComponent_normal h d
    ∃ (κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup)),
      Function.Surjective κ ∧
      κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
      ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ =
        replacementComponent d ∧
      ∃ (σ : Representation (ZMod 2) (d.overgroup ⧸ pCore 2 d.overgroup)
          (Additive (A ⧸ (Z d.radical a).subgroupOf A)))
        (c : BinaryConjugationSection (stabilizer d.radical a) A (Z d.radical a) (σ.comp κ)),
        (∀ u : A, (c.coordinates u).toAdd =
          Additive.ofMul (QuotientGroup.mk' ((Z d.radical a).subgroupOf A) u)) ∧
        IsQuadratic σ ((A'.subgroupOf (stabilizer d.radical a)).map κ) ∧
        fixedCodim σ ((A'.subgroupOf (stabilizer d.radical a)).map κ) ≤ 2*n ∧
        NaturalMovedSectionAtDegree σ (replacementComponent d) n

/-- In the source orientation of the paired images, the literal secondary
quotient has a faithful action and a natural moved section at the original
field degree. The full Z-kernel and original vertex quotient map are retained. -/
theorem replacement_secondary_natural_section_of_index_le
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a)
    (horder : (Q d.radical z).relIndex
      (Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)) ≤
      (Q d.radical a).relIndex
        (Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a))) :
    HasSecondaryNaturalSection h d path hb hat hzt hlarge := by
  let := replacement_secondary_quotient_normal h d path hb hat hzt hlarge
  let := replacement_secondary_quotient_elementary h d path hb hat hzt hlarge
  let := replacementComponent_normal h d
  obtain ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim,hmove⟩ :=
    replacement_secondary_section_nontrivial h d path hb hat hzt hlarge
  refine ⟨κ,hκ,hk,hL,σ,c,hc,hquad,hcodim,?_⟩
  exact replacement_secondary_moved_natural_of_index_le h d path hb hat hzt hlarge
    horder κ hk hL σ c

/-- One of the two original critical endpoints has the source orientation
and a natural moved section on its literal secondary quotient. The choice
of the smaller secondary image is discharged by totality of the index order. -/
theorem replacement_exists_oriented_secondary_natural_section
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    ∃ (u v : Vertex d.radical) (p : CriticalPath d.radical g u v)
      (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
      (hl : ¬ core d.radical u ≤
        (frattini (Q d.radical u)).map (Q d.radical u).subtype ⊔ X d.radical u),
      ((u = a ∧ v = z) ∨ (u = z ∧ v = a)) ∧
        HasSecondaryNaturalSection h d p hb hut hvt hl := by
  let A := Sp4Four.secondaryOrbit d.radical a (Sp4Four.secondarySeed d.radical a t z)
  let A' := Sp4Four.secondaryOrbit d.radical z (Sp4Four.secondarySeed d.radical z t a)
  rcases le_total ((Q d.radical z).relIndex A) ((Q d.radical a).relIndex A') with ho | ho
  · exact ⟨a,z,path,hat,hzt,hlarge,Or.inl ⟨rfl,rfl⟩,
      replacement_secondary_natural_section_of_index_le h d path hb hat hzt hlarge ho⟩
  · let rev := reverse_secondary_path h d path hb
    have hl := opposite_nonfrattini d path hlarge
    exact ⟨z,a,rev,hzt,hat,hl,Or.inr ⟨rfl,rfl⟩,
      replacement_secondary_natural_section_of_index_le h d rev hb hzt hat hl ho⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
