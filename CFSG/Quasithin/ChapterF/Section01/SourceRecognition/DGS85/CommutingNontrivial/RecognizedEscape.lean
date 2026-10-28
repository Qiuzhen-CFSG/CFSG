module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.NaturalEscape
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingNontrivial.IndexEstimates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.LocalStructure.EarlierInputs

/-!
# Recognized natural modules in the reciprocal escape argument

Corrected 5.12 gives an equivariant natural action on the original center.
Its coordinate map is converted to the graph's literal natural-center
section, with actor kernel Q and trivial vector kernel. The natural case
of 8.2 then excludes reverse core containment. Consequently hypothetical
containment gives the square lower bound for every prepared faithful actor.

The moving linear application constructs its quotient action, faithfulness,
quadraticity and corrected fixed-space generation from the source inputs.
The resulting square bound uses the original subgroup and centralizer
indices, including the field-two model. Both the natural case and the
moving index bound are applied to the unchanged reduced F1.11 graph.

Source: DGS, *Groups and Graphs* (1985), 8.2, pp.134--135, using corrected
5.12, pp.113--115. These are the natural case and numerical reduction;
the nonnatural contradiction and 8.3--8.7 remain with this owner.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open Representation.RankOne.QuadraticRecognition
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
open Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] {P : Fin 2 → Subgroup G} {B : Subgroup G}

/-- Corrected 5.12 natural recognition has exactly the natural-center marking
used by the graph argument: the actor kernel is the original Q, and the
vector kernel is the actual central omega, which vanishes here. -/
theorem source_natural_center_of_recognition (h : LocallyRankOneTriple P B)
    (d : EarlierLocalTheorems (family P)) (v : Vertex (family P))
    (hz : center (d.localGroup v) = ⊥)
    {D : Type u} [Group D] [Finite D]
    (e : (d.localGroup v ⧸ pCore 2 (d.localGroup v)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h v
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup v)))
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) v))) (T : Sylow 2 D),
      (∀ (l : d.localGroup v) (z : Additive (Z (family P) v)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      NaturalRealization ρ T →
      Noncommuting.HasNaturalCenter (d.localGroup v) (Z (family P) v) (Q (family P) v) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h v
  dsimp only
  intro ρ T hact hn
  let L := d.localGroup v
  let Z₀ := Z (family P) v
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  obtain ⟨k,hk,hfin,hchar,n,_,_,eD,_,_,_,_,_,_,E,hE⟩ := hn
  let : Algebra (ZMod 2) k := ZMod.algebra k 2
  let π := eD.toMonoidHom.comp q
  have hZL : Z₀ ≤ L := pGroup_le_localGroup (family P) d v Z₀
    (IsElementaryAbelian.isPGroup 2 _) (Z_le_stabilizer (family P) v)
  let δ := centerSection L Z₀ hZL ((d.local_le v).trans
    (stabilizer_normalizes_Z (family P) v)) q ρ hact
  have hω : Stellmacher.omegaOneCenterAmbient L = ⊥ := by
    apply bot_unique
    intro x hx
    obtain ⟨hxL,_,hxc⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hx
    have hm : (⟨x,hxL⟩ : L) ∈ center L :=
      mem_center_iff.mpr (fun l => Subtype.ext (hxc l l.property))
    rw [hz,mem_bot] at hm
    exact congrArg Subtype.val hm
  refine ⟨k,inferInstance,inferInstance,inferInstance,π,
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _)),?_,?_⟩
  · ext l
    change eD (q l) = 1 ↔ (l : G) ∈ Q (family P) v
    rw [eD.map_eq_one_iff]
    exact SetLike.ext_iff.mp (local_quotient_kernel (family P) d v e) l
  · refine ⟨{
      section_le := hZL
      kernel_le := hω ▸ bot_le
      normalized := δ.normalized
      coordinates := E.toAddEquiv.toMultiplicative.toMonoidHom.comp δ.coordinates
      onto := E.toAddEquiv.toMultiplicative.surjective.comp δ.onto
      kernel_eq := ?_
      equivariant := ?_ }⟩
    · ext z
      change E (δ.coordinates z).toAdd = 0 ↔ (z : G) ∈ Stellmacher.omegaOneCenterAmbient L
      rw [E.map_eq_zero_iff,hω]
      exact δ.coordinates_eq_one_iff z
    · intro l z
      change E (δ.coordinates _).toAdd = Matrix.mulVec (π l).val (E (δ.coordinates z).toAdd)
      rw [δ.equivariant]
      exact hE _ _

/-- Recognition on the original starting center supplies the natural case
of 8.2 with the same quotient action and vectors. -/
theorem source_reciprocal_escape_of_recognized_center (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥)
    {D : Type u} [Group D] [Finite D]
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D) :
    letI := CommutingOneProfile.source_center_elementary h a
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) a))) (T : Sylow 2 D),
      (∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      NaturalRealization ρ T → ¬ V (family P) a' 1 ≤ Q (family P) beta := by
  let := CommutingOneProfile.source_center_elementary h a
  dsimp only
  intro ρ T hact hnat
  have hz := local_center_eq_bot_of_neighbor_central h d hab
    (source_critical_geometry h d hc hab hd hb hcomm).2.2.1
  exact source_reciprocal_escape_of_natural_center h hB d hc hab hd hb hcomm models hne
    (source_natural_center_of_recognition h d a hz e ρ T hact hnat)

/-- If reciprocal core containment held, every faithful quadratic actor on
the starting center would satisfy the square lower bound. Corrected 5.12
uses the actual Sylow-fixed generation and O²-fixed vanishing proved here;
neither is an added module hypothesis. This is the numerical reduction (*)
of 8.2, with faithfulness and quadraticity kept explicit for its chosen actor. -/
theorem source_reverse_containment_square_bound (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hne : ⁅V (family P) beta 1 ⊓ Q (family P) a', V (family P) a' 1⁆ ≠ ⊥)
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    {D : Type u} [Group D] [Finite D] (M : BinaryRankOneModel D)
    (T : Sylow 2 (stabilizer (family P) a))
    (e : (d.localGroup a ⧸ pCore 2 (d.localGroup a)) ≃* D)
    (A : Subgroup (d.localGroup a)) :
    letI := CommutingOneProfile.source_center_elementary h a
    let K := (d.localGroup a).subgroupOf (stabilizer (family P) a)
    let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (d.localGroup a)))
    let qK := q.comp (subgroupOfEquivOfLe (d.local_le a)).toMonoidHom
    ∀ (ρ : Representation (ZMod 2) D (Additive (Z (family P) a))),
      (∀ (l : d.localGroup a) (z : Additive (Z (family P) a)),
        ((ρ (q l) z).toMul : G) = (l : G) * z.toMul * (l : G)⁻¹) →
      Function.Injective ρ →
      A.map q ≤ ((T : Subgroup (stabilizer (family P) a)).subgroupOf K).map qK →
      IsQuadratic ρ (A.map q) →
      Nat.card (A.map q)^2 ≤ Nat.card (Additive (Z (family P) a) ⧸ fixedSpace ρ (A.map q)) := by
  let := finite_endpoints h
  let := CommutingOneProfile.source_center_elementary h a
  let : Finite (Z (family P) a) := Finite.of_injective
    (inclusion (Z_le_stabilizer (family P) a)) (inclusion_injective _)
  dsimp only
  intro ρ hact hf hAS hquad
  obtain ⟨S,hS,hgen,hfix⟩ := source_critical_center_module_prepared h d hc hab hd hb hcomm T e ρ hact
  by_contra! hstrict
  have hnat := (binary_rank_one_bound_and_recognition M ρ hf S _
    (hS.symm ▸ hAS) hquad hgen hfix).2 hstrict
  exact source_reciprocal_escape_of_recognized_center h hB d hc hab hd hb hcomm models hne
    e ρ S hact hnat hreverse

/-- Literal reduced F1.11 application of the natural-center case of 8.2.
The source constructs all earlier local data except the independent 6.5
obstruction and 6.1 model markings. The critical pair is arbitrary. -/
theorem reduced_reciprocal_escape_of_natural_center
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a, Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    (hnat : Noncommuting.HasNaturalCenter (graphLocalGroup (Reduction.reducedFamily J S) a)
      (Z (Reduction.reducedFamily J S) a) (Q (Reduction.reducedFamily J S) a)) :
    ¬ V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta :=
  source_reciprocal_escape_of_natural_center (Reduction.reduced_triple h)
    (Reduction.reduced_borel_core_sylow h) (Reduction.reducedEarlierLocalTheorems h hob)
    hc hab hd hb hcomm models hne hnat

/-- Under reverse containment the actual moving linear actor satisfies the
square bound. Whole-action faithfulness, quadraticity, Sylow placement and
the corrected fixed-space generation are all discharged by the existing
source module construction. Small SL₂(2) is included. -/
theorem source_moving_linear_square_bound_of_reverse_containment
    (h : LocallyRankOneTriple P B)
    (hB : ∃ T : Sylow 2 B, (T : Subgroup B) = pCore 2 B)
    (d : EarlierLocalTheorems (family P))
    {a beta a' : Vertex (family P)} (hc : IsCriticalPair (family P) a a')
    (hab : (graph (family P)).Adj a beta)
    (hd : (graph (family P)).dist beta a' + 1 = b (family P))
    (hb : 1 < b (family P)) (hcomm : ⁅Z (family P) a, Z (family P) a'⁆ = ⊥)
    (models : ∀ v : Vertex (family P), IsRankOneModel (d.localGroup v ⧸ pCore 2 (d.localGroup v)))
    (hreverse : V (family P) a' 1 ≤ Q (family P) beta)
    (w : (graph (family P)).neighborSet a')
    (hm : ⁅V (family P) beta 1 ⊓ Q (family P) a', Z (family P) w.val⁆ ≠ ⊥)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n)
    (e : (d.localGroup w.val ⧸ pCore 2 (d.localGroup w.val)) ≃* SL(2,K)) :
    let A := V (family P) beta 1 ⊓ Q (family P) a'
    (Q (family P) w.val).relIndex A ^ 2 ≤
      (centralizer (A : Set G)).relIndex (Z (family P) w.val) := by
  let := CommutingOneProfile.source_center_elementary h w.val
  dsimp only
  by_contra! hstrict
  obtain ⟨ρ,T,hact,_,hnat⟩ := (source_moving_linear_index_recognition h d hc hab hd hb hcomm
    w hm hn hK e).2 hstrict
  have hmark := source_natural_center_of_recognition h d w.val
    (source_moving_actor h d hc hab hd hb hcomm w hm).1 e ρ T hact hnat
  have hne : ⁅V (family P) beta 1 ⊓ Q (family P) a',V (family P) a' 1⁆ ≠ ⊥ := by
    intro he
    exact hm (bot_unique ((commutator_mono le_rfl (Z_neighbor_le_V (family P) w.property)).trans he.le))
  exact source_reciprocal_escape_of_natural_moving_neighbor h hB d hc hab hd hb hcomm
    models hne w hmark hreverse

/-- The original reduced F1.11 moving actor has the square lower bound
whenever the hypothetical reverse core containment of 8.2 holds. The
constructed action and all its auxiliary module premises are discharged. -/
theorem reduced_moving_linear_square_bound_of_reverse_containment
    {J : Fin 2 → Subgroup G} {S : Subgroup G} (h : HypothesisF11 J S)
    (hob : ∀ v w : Vertex (Reduction.reducedFamily J S),
      (graph (Reduction.reducedFamily J S)).Adj v w →
      ¬ stabilizer (Reduction.reducedFamily J S) v ≤ normalizer
        ((Q (Reduction.reducedFamily J S) w ⊓ Q (Reduction.reducedFamily J S) v :
          Subgroup (Reduction.G₀ J S)) : Set (Reduction.G₀ J S)))
    (models : ∀ v : Vertex (Reduction.reducedFamily J S),
      IsRankOneModel (graphLocalGroup (Reduction.reducedFamily J S) v ⧸
        pCore 2 (graphLocalGroup (Reduction.reducedFamily J S) v)))
    {a beta a' : Vertex (Reduction.reducedFamily J S)}
    (hc : IsCriticalPair (Reduction.reducedFamily J S) a a')
    (hab : (graph (Reduction.reducedFamily J S)).Adj a beta)
    (hd : (graph (Reduction.reducedFamily J S)).dist beta a' + 1 = b (Reduction.reducedFamily J S))
    (hb : 1 < b (Reduction.reducedFamily J S))
    (hcomm : ⁅Z (Reduction.reducedFamily J S) a, Z (Reduction.reducedFamily J S) a'⁆ = ⊥)
    (hne : ⁅V (Reduction.reducedFamily J S) beta 1 ⊓ Q (Reduction.reducedFamily J S) a',
      V (Reduction.reducedFamily J S) a' 1⁆ ≠ ⊥)
    (hreverse : V (Reduction.reducedFamily J S) a' 1 ≤ Q (Reduction.reducedFamily J S) beta)
    {K : Type u} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2^n) :
    let F := Reduction.reducedFamily J S
    let A := V F beta 1 ⊓ Q F a'
    ∃ w : (graph F).neighborSet a', ⁅A,Z F w.val⁆ ≠ ⊥ ∧
      ∀ _e : (graphLocalGroup F w.val ⧸ pCore 2 (graphLocalGroup F w.val)) ≃* SL(2,K),
        (Q F w.val).relIndex A ^ 2 ≤
          (centralizer (A : Set (Reduction.G₀ J S))).relIndex (Z F w.val) := by
  dsimp only
  let h' := Reduction.reduced_triple h
  let d := Reduction.reducedEarlierLocalTheorems h hob
  obtain ⟨w,hm,_⟩ := exists_moving_neighbor (Reduction.reducedFamily J S)
    (fun v => (source_Z_Q_U h' v).1) beta a' hne
  exact ⟨w,hm,fun e => source_moving_linear_square_bound_of_reverse_containment h'
    (Reduction.reduced_borel_core_sylow h) d hc hab hd hb hcomm models hreverse w hm hn hK e⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingNontrivial
