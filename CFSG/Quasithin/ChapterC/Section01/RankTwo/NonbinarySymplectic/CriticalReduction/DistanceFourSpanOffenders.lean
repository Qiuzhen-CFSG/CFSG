module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSpanEscape
public import Theory.Representation.BinaryConjugationSection.FiniteOffenderIndex

/-!
# An actual offender on one of the two literal midpoint span quotients

In the fixed-radius, large backward-image branch, both opposite spans
escape their actual kernels. Construct the faithful quotient actions on
W1/(W1 intersect B_a) and W2/(W2 intersect B_e) separately. Their full
vertex projections retain their original field degrees and exact kernels.
The crossed commutators bound the two fixed indices by the respective
opposite-kernel indices. Ordering those two integers supplies an offender
on one of these two actual quotient actions.

The conclusion retains the favorable orientation and all its literal
coordinates. The two quotient carriers and their field markings are not
identified. No action, faithfulness, nonzero-image or FF premise is added.
Source: the paired FF comparison in MS93 (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

/-- An offender on the specified full normal-span quotient, with its
original-degree field marking, full kernel and literal quotient coordinates. -/
@[expose] def distanceFourSpanOffender {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (a e : Vertex R) (n : ℕ) : Prop :=
  let W := localZSpan R e a
  let D := W ⊓ B R a (geometry.Z_normal a)
  ∃ E : BinaryField, E.degree=n ∧
    ∃ f : stabilizer R a →* Sp E.Carrier,
      Function.Surjective f ∧ f.ker.map (stabilizer R a).subtype=Q R a ∧
      ∃ hD : (D.subgroupOf W).Normal,
        letI := hD
        ∃ hEA : IsElementaryAbelian 2 (W ⧸ D.subgroupOf W),
          letI := hEA
          ∃ σ : Representation (ZMod 2) (Sp E.Carrier) (Additive (W ⧸ D.subgroupOf W)),
            Function.Injective σ ∧
            ∃ c : BinaryConjugationSection (stabilizer R a) W D (σ.comp f),
              (∀ w : W, (c.coordinates w).toAdd=
                Additive.ofMul (QuotientGroup.mk' (D.subgroupOf W) w)) ∧
              IsOffender σ (((localZSpan R a e).subgroupOf (stabilizer R a)).map f)

private theorem offender_of_opposite_index
    {G J V : Type*} [Group G] [Group J] [Finite J]
    [AddCommGroup V] [Module (ZMod 2) V]
    (S W D A Q P : Subgroup G) [Finite W]
    (f : S →* J) (hfQ : f.ker.map S.subtype=Q)
    (σ : Representation (ZMod 2) J V)
    (c : BinaryConjugationSection S W D (σ.comp f))
    (hAS : A ≤ S) (hA : IsElementaryAbelian 2 ((A.subgroupOf S).map f))
    (hnot : ¬ A ≤ Q) (hc : ⁅A,W ⊓ P⁆ ≤ D)
    (hi : P.relIndex W ≤ Q.relIndex A) : IsOffender σ ((A.subgroupOf S).map f) := by
  have hk : f.ker=Q.subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective f.ker).symm
  have hne : (A.subgroupOf S).map f ≠ ⊥ := by
    intro hz
    rw [Subgroup.map_eq_bot_iff,hk] at hz
    exact hnot (fun x hx => hz (show (⟨x,hAS hx⟩ : S) ∈ A.subgroupOf S from hx))
  have hcard : Nat.card ((A.subgroupOf S).map f)=Q.relIndex A := by
    rw [←relIndex_ker,hk,relIndex_subgroupOf hAS]
  apply BinaryConjugationSection.offender_of_section_index_of_finite σ f c A (W ⊓ P)
    hc ⟨hne,hA⟩
  rw [inf_relIndex_left,hcard]
  exact hi

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual source branch supplies an offender on one of the two
separately marked full-span quotients. The reciprocal alternative is retained. -/
theorem Input.replacement_distance_four_span_offender_or_reciprocal
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hlarge : Nat.card F < (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u))
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    distanceFourSpanOffender geometry a (path.walk.getVert 2) n ∨
      distanceFourSpanOffender geometry (path.walk.getVert 2) a n := by
  let e := path.walk.getVert 2
  let W1 := localZSpan d.radical e a
  let W2 := localZSpan d.radical a e
  let D1 := W1 ⊓ B d.radical a (geometry.Z_normal a)
  let D2 := W2 ⊓ B d.radical e (geometry.Z_normal e)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hl := path.length_eq_b
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hfixed_e : ⁅V d.radical e,Q d.radical e⁆ ≤ fixedCore d.radical e := by
    obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical path.start_color
    obtain ⟨k,hk⟩ := exists_mVertex_of_color d.radical he
    have hact : act d.radical (g⁻¹*k) a=e := by
      rw [hg,act_mVertex,mul_inv_cancel_left,←hk]
    have hh := map_mono (f := (MulAut.conj (g⁻¹*k)⁻¹).toMonoidHom) hfixed
    rwa [map_commutator,←V_act,←Q_act,←Escape.EdgeTransfer.fixedCore_act,hact] at hh
  let rev : CriticalPath d.radical geometry e u := {
    start_color := back.end_color
    walk := back.walk.reverse
    shortest := by rw [SimpleGraph.Walk.length_reverse,back.shortest,SimpleGraph.dist_comm]
    critical := critical_reverse d.radical geometry
      (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
      u back.start_color (by
        rw [geometry.distance_constant u back.start_color]
        exact lt_of_lt_of_le (by decide : 0<4) hb4)
      e back.end_color back.critical }
  have hrmid : rev.walk.getVert 2=a := by
    change back.walk.reverse.getVert 2=a
    rw [SimpleGraph.Walk.getVert_reverse,back.length_eq_b,hb]
    exact hmid
  obtain ⟨hesc1,hesc2⟩ := h.replacement_distance_four_spans_escape_of_large_back d path hb
    back hmid hlarge hfixed
  have hW1Q : W1 ≤ Q d.radical a :=
    localZSpan_le_Q d.radical path.start_color (by rw [SimpleGraph.dist_comm,hd]) hb2
  have hW2Q : W2 ≤ Q d.radical e := localZSpan_le_Q d.radical he hd.le hb2
  have hW1e : W1 ≤ stabilizer d.radical e := hW1Q.trans
    (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hd)
  have hW2a : W2 ≤ stabilizer d.radical a := hW2Q.trans
    (Q_le_stabilizer_of_dist_two d.radical e a he (by rw [SimpleGraph.dist_comm]; exact hd))
  have hW1a : W1 ≤ stabilizer d.radical a := hW1Q.trans (fun _ hx => hx.1)
  have hW2e : W2 ≤ stabilizer d.radical e := hW2Q.trans (fun _ hx => hx.1)
  let := finite_stabilizer d.radical a
  let := finite_stabilizer d.radical e
  let : Finite W1 := Finite.of_injective (inclusion hW1a) (inclusion_injective _)
  let : Finite W2 := Finite.of_injective (inclusion hW2e) (inclusion_injective _)
  obtain ⟨_,_,_,_,hcross1,hcross2⟩ :=
    h.replacement_distance_four_normal_spans_of_radius_fixed d path hb hfixed
  have hc1 : ⁅W2,W1 ⊓ Q d.radical e⁆ ≤ D1 := by
    apply le_inf
    · exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hW2a.trans (localZSpan_normalized d.radical e a)))
    · rw [commutator_comm]
      exact hcross1.trans (Escape.EdgeTransfer.Z_le_B hb2 a path.start_color)
  have hc2 : ⁅W1,W2 ⊓ Q d.radical a⁆ ≤ D2 := by
    apply le_inf
    · exact (commutator_mono le_rfl inf_le_left).trans
        (le_normalizer_iff_commutator_le_right.mp
          (hW1e.trans (localZSpan_normalized d.radical a e)))
    · rw [commutator_comm]
      exact hcross2.trans (Escape.EdgeTransfer.Z_le_B hb2 e he)
  rcases le_total ((Q d.radical e).relIndex W1) ((Q d.radical a).relIndex W2) with hi | hi
  · obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor⟩ :=
      h.replacement_distance_four_span_action_of_radius_fixed d path hb hfixed
    let := hD
    let := hEA
    refine Or.inl ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,?_⟩
    exact offender_of_opposite_index (stabilizer d.radical a) W1 D1 W2
      (Q d.radical a) (Q d.radical e) f hfQ σ c hW2a hactor hesc2 hc1 hi
  · have hdata := h.replacement_distance_four_span_action_of_radius_fixed d rev hb hfixed_e
    rw [hrmid] at hdata
    obtain ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,hactor⟩ := hdata
    let := hD
    let := hEA
    refine Or.inr ⟨E,hE,f,hf,hfQ,hD,hEA,σ,hfaith,c,hcoord,?_⟩
    exact offender_of_opposite_index (stabilizer d.radical e) W2 D2 W1
      (Q d.radical e) (Q d.radical a) f hfQ σ c hW1e hactor hesc1 hc2 hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
