module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.ActorFaithfulness

/-!
# Corrected quadratic recognition on the moving Chapter 8 neighbor

The nonzero source displacement selects an actual moving neighbor. On its
original center the preceding graph arguments construct the quotient action,
place its nontrivial quadratic actor in a quotient Sylow, and prove generation
by that Sylow's fixed space and vanishing of the two-residual fixed space.
The actor order remains the literal relative index against the neighbor core.
Corrected 5.12 then supplies the lower bound and, under the strict comparison,
actual equivariant natural coordinates. The same action is faithful on this two-actor, using the
Sylow-centralizer alternative. The reduced F1.11 consumer supplies
6.2(d) directly, preserving the full Borel and reduced completion.

Source: DGS, *Groups and Graphs* (1985), 8.0--8.1 and 8.2--8.7, pp.132--140;
corrected 5.12, pp.113--114. Faithfulness and the marked rank-one quotient
remain explicit. This is not the reverse-escape, distance-three, or equal-field
theorem; those conclusions and all remaining premise discharge stay here.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.RankOne.QuadraticRecognition
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G]

/-- Corrected 5.12 at the literal moving neighbor. The graph proof supplies
all actor and fixed-space premises; only faithfulness of the constructed
quotient action and the numerical strict comparison remain implications. -/
theorem source_moving_center_bound_and_recognition
    {P : Fin 2 → Subgroup G} {B : Subgroup G} (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D] (M : BinaryRankOneModel D)
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h w.val
    let F := family P
    let A := V F beta 1 ⊓ Q F a'
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
    let Aq := (A.subgroupOf (d.localGroup w.val)).map q
    ∃ (ρ : Representation (ZMod 2) D (Additive (Z F w.val))) (S : Sylow 2 D),
      (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) ∧
      Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsQuadratic ρ Aq ∧
      Function.Injective (ρ.comp Aq.subtype) ∧
      GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ ∧
      Nat.card Aq = (Q F w.val).relIndex A ∧
      (Function.Injective ρ →
        (Q F w.val).relIndex A ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) ∧
        (Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) < (Q F w.val).relIndex A ^ 2 →
          NaturalRealization ρ S)) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h w.val
  let : Finite (Z (family P) w.val) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) w.val)) (inclusion_injective _)
  dsimp only
  obtain ⟨ρ, S, hact, hAS, hne, hq, hgen, hfix, hcard⟩ :=
    source_moving_center_module h d hc hab hd hb hcomm w hm e
  obtain ⟨hz, hAL, _⟩ := source_moving_actor h d hc hab hd hb hcomm w hm
  have hp : IsPGroup 2 ↥(V (family P) beta 1 ⊓ Q (family P) a' : Subgroup G) :=
    (isPGroup_pCoreIn 2 (stabilizer (family P) a')).to_le inf_le_right
  have hfaith := source_centerless_two_actor_faithful h d w.val hz _ hp hAL e ρ hact
  refine ⟨ρ, S, hact, hAS, hne, hq, hfaith, hgen, hfix, hcard, ?_⟩
  intro hf
  have hbound := binary_rank_one_bound_and_recognition M ρ hf S _ hAS hq hgen hfix
  rwa [hcard] at hbound

/-- The original nonzero H selects a moving neighbor and constructs its
corrected-5.12 module for every actual marked binary rank-one quotient.
Reduced 6.2(d) is discharged from F1.11, not assumed in the consumer. -/
theorem reduced_exists_moving_center_recognition
    {J : Fin 2 → Subgroup G} {S₀ : Subgroup G} (h : HypothesisF11 J S₀)
    (d : RemainingLocalTheorems (Reduction.reducedFamily J S₀))
    {a beta a' : Vertex (Reduction.reducedFamily J S₀)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S₀) a a')
    (hab : (graph (Reduction.reducedFamily J S₀)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S₀)).dist beta a' + 1 = b (Reduction.reducedFamily J S₀))
    (hb : 1 < b (Reduction.reducedFamily J S₀))
    (hcomm : ⁅Z (Reduction.reducedFamily J S₀) a, Z (Reduction.reducedFamily J S₀) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S₀) beta 1 ⊓ Q (Reduction.reducedFamily J S₀) a',
      V (Reduction.reducedFamily J S₀) a' 1⁆ ≠ ⊥)
    {D : Type*} [Group D] [Finite D] (M : BinaryRankOneModel D) :
    let F := Reduction.reducedFamily J S₀
    letI : ∀ v : Vertex F, IsElementaryAbelian 2 (Z F v) :=
      fun v => CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) v
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a',
      ⁅A, Z F w.val⁆ ≠ ⊥ ∧
      center (d.localGroup w.val) = ⊥ ∧
      ∀ e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* D,
        let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup w.val)))
        let Aq := (A.subgroupOf (d.localGroup w.val)).map q
        ∃ (ρ : Representation (ZMod 2) D (Additive (Z F w.val))) (S : Sylow 2 D),
          (∀ (l : d.localGroup w.val) (z : Additive (Z F w.val)),
            ((ρ (q l) z).toMul : Reduction.G₀ J S₀) =
              (l : Reduction.G₀ J S₀) * z.toMul * (l : Reduction.G₀ J S₀)⁻¹) ∧
          Aq ≤ S ∧ Aq ≠ ⊥ ∧ IsQuadratic ρ Aq ∧
          Function.Injective (ρ.comp Aq.subtype) ∧
          GeneratedByFixedSpace ρ S ∧ fixedSpace ρ (pResidual 2 D) = ⊥ ∧
          Nat.card Aq = (Q F w.val).relIndex A ∧
          (Function.Injective ρ →
            (Q F w.val).relIndex A ≤ Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) ∧
            (Nat.card (Additive (Z F w.val) ⧸ fixedSpace ρ Aq) < (Q F w.val).relIndex A ^ 2 →
              NaturalRealization ρ S)) := by
  let : ∀ v : Vertex (Reduction.reducedFamily J S₀),
      IsElementaryAbelian 2 (Z (Reduction.reducedFamily J S₀) v) :=
    fun v => CommutingOneProfile.source_center_elementary (Reduction.reduced_triple h) v
  dsimp only
  let h' := Reduction.reduced_triple h
  let d' := reducedEarlierLocalTheorems h d
  obtain ⟨w, hm, _⟩ := exists_moving_neighbor (Reduction.reducedFamily J S₀)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  exact ⟨w, hm, (source_moving_actor h' d' hc hab hd hb hcomm w hm).1,
    fun e => source_moving_center_bound_and_recognition h' d' hc hab hd hb hcomm w hm M e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
