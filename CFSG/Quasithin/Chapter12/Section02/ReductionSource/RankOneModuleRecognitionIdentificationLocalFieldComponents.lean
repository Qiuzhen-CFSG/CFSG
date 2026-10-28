module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldComponents
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldCubic

/-!
# Component restrictions on the Chapter12 field plane

The original one-sided conjugate configuration supplies the field plane
and its cubic witness. Its full normalizer is SQTK, and the witness is
outside the plane centralizer. The centerless outer-two component branch
then has cubic rank at most one. For an actual C-component whose intrinsic
two-core quotient belongs to the B.5 small-moved catalogue, this leaves
the concrete A5, PSL3(2), and SL3(4) quotient models.

These statements apply to the literal Chapter12 layer and centralizer.
Lifting the faithful action's components and excluding the remaining
three actions are still required for source 6.2.7 and LocalAnalysis.
Source: Aschbacher--Smith, 6.2.4(6), 6.2.7, printed pp.680,683,
applied to 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual Chapter12 plane normalizer is SQTK and contains the original
cubic outside its plane centralizer. -/
theorem source_local_one_sided_component_ambient
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    IsSQTK KnownSimple.IsKnownSimple (normalizer (U : Set G)) ∧
      ∃ d ∈ fieldLocalResidual L U, orderOf d = 3 ∧
        d ∈ normalizer (U : Set G) ∧ d ∉ centralizer (U : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  have hUne : commutatorLayer T L ⊓ centralizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G) ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hUc
    contradiction
  exact ⟨local_field_normalizer_sqtk h611 hfield hUne,
    field_plane_cubic_outside_centralizer hnat hfield hUc⟩

/-- The centerless outer-two branch of source 6.2.4(6), specialized to each
literal C-component of the original Chapter12 plane centralizer. -/
theorem source_local_one_sided_component_rank
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    ∀ K : Subgroup (centralizer (U : Set G)), K.IsCComponent →
      center (K ⧸ pCore 2 K) = ⊥ →
      IsPGroup 2 (MulAut.Outer (K ⧸ pCore 2 K)) → primeRank 3 (K ⧸ pCore 2 K) ≤ 1 := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  dsimp only
  intro K hK hz ho
  exact local_field_component_three_rank_le_one h611 hnat hfield hUc K hK hz ho

/-- The B.5 list on an actual original component quotient reduces to the
three rows retained in the proof of 6.2.7. Component lifting and the final
cubic action contradictions are not assumed by this restriction theorem. -/
theorem source_local_one_sided_component_models
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    ∀ K : Subgroup (centralizer (U : Set G)), K.IsCComponent →
      SmallMoved.ActorList (K ⧸ pCore 2 K) →
      Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* PSL(3,ZMod 2)) ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* SL(3,BinaryField.four.Carrier)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  dsimp only
  intro K hK hm
  exact local_field_component_small_actor h611 hnat hfield hUc K hK hm

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
