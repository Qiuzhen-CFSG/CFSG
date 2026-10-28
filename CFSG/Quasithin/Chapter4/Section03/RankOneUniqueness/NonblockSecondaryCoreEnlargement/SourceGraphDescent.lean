module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceCubic
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceFrattiniKernel

/-!
# Descent of the original cubic action to the Frattini graph extension

The component quotient is marked literally by `mark`, while the selected
cubic extension is mapped to the projective general-linear group by `φ`.
The projection square identifies the quotient action with the inner-diagonal
projective action.  The prime-to-three kernel lemma then makes the whole
Frattini action descend through the cubic extension; the stated crossing
equation supplies the graph actor and its normalizer.  The construction keeps
the original crossing and does not assume that it normalizes the chosen cubic
subgroup.  The final source proof still has to construct the markings and
the crossing equation from the original parabolic frame.

Source: Aschbacher--Smith B.4.14, printed p.98, together with original
4.3.14--16 and the conclusion of 4.3.2, printed pp.617--619.
-/

public noncomputable section
open Subgroup Matrix Representation
open scoped MatrixGroups
open Matrix.PSL3.OuterSolvable Matrix.PSL3.ExtensionBorel
open Representation.SL3.AdjointCubicCentralizer
open Representation.SL3.AdjointCubicCentralizer.GraphExtension
open Representation.SL3.AdjointCubicCentralizer.GraphExtension.FrattiniDescent
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
attribute [local instance] ZMod.algebra SecondaryActionData.normal
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]
  {T : Sylow 2 G} {L V : Subgroup G} {c : SourceConfiguration T L}
set_option backward.isDefEq.respectTransparency false

omit [Finite G] [Finite F] [CharP F 2] in
/-- The original projection square identifies the whole cubic-extension action. -/
theorem cubic_extension_actor (s : SecondaryActionData c 2)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F)) (X : Subgroup G)
    (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F)
    (hsquare : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      ProjectiveSpecialLinearGroup.toPGL (mark (QuotientGroup.mk' (pCore 2 s.component) b)))
    (g : cubicExtension s X) :
    (MulAut.congr mark) (s.action (g : rootNormalizer c)) =
      (pglEquivInnerDiagonal F (φ g)).val := by
  apply MulEquiv.ext
  intro z
  obtain ⟨w,rfl⟩ := mark.surjective z
  change mark (s.action (g : rootNormalizer c) (mark.symm (mark w))) = _
  rw [mark.symm_apply_apply]
  exact cubic_extension_action s mark X φ hsquare g w

theorem action_eq_of_kernel_le {N A B : Type*} [Group N] [Group A] [Group B]
    (f : N →* A) (α : N →* B) (hker : f.ker ≤ α.ker) {x y : N}
    (he : f x = f y) : α x = α y :=
  α.div_mem_ker_iff.mp (hker (f.div_mem_ker_iff.mpr he))

/-- The source kernel supplies both descent clauses without assuming that the
original crossing normalizes the chosen cubic extension. -/
@[expose] def sourceFrattiniGraphData (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F)
    (hφ : Function.Surjective φ)
    (hsquare : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      ProjectiveSpecialLinearGroup.toPGL (mark (QuotientGroup.mk' (pCore 2 s.component) b)))
    (e : Frattini s.component ≃* Multiplicative (TraceZero F))
    (he : ∀ (b : s.component) v,
      (e (coreAction s.component (b : rootNormalizer c) v)).toAdd =
        projectiveSpecialAdjoint F (mark (QuotientGroup.mk' (pCore 2 s.component) b))
          (e v).toAdd)
    (correction : GL (Fin 3) F) (field : F ≃+* F)
    (hgraph : (MulAut.congr mark) (s.action ⟨c.t,root_normalized c D c.crossing_mem⟩) =
      linearConj F correction * graph F * fieldAction F field) :
    FrattiniGraphData (F := F) s.component (cubicExtension s X) le_sup_left := by
  let f := s.action
  let α := coreAction s.component
  let t : rootNormalizer c := ⟨c.t,root_normalized c D c.crossing_mem⟩
  let a := (MulAut.congr mark) (f t)
  have hker : f.ker ≤ α.ker := s.action_kernel_le_frattini_kernel D h hF mark e he
  refine {
    componentMarking := mark
    projection := φ
    onto := hφ
    componentSquare := hsquare
    coordinates := e
    componentEquivariant := he
    kernelDescent := ?_
    crossing := t
    actor := a
    actor_eq := rfl
    correction := correction
    field := field
    graph_eq := hgraph
    crossingDescent := ?_ }
  · intro g hg
    apply hker
    apply (MulAut.congr mark).injective
    change (MulAut.congr mark) (s.action (g : rootNormalizer c)) = (MulAut.congr mark) 1
    rw [cubic_extension_actor s mark X φ hsquare g,show φ g = 1 from hg,map_one,map_one]
    rfl
  · intro g
    let hn := graphActor_normalizes F a correction field hgraph
    obtain ⟨g',hg'⟩ := hφ (conjugatePGL F a hn (φ g))
    refine ⟨g',hg',action_eq_of_kernel_le f α hker ?_⟩
    apply (MulAut.congr mark).injective
    change (MulAut.congr mark) (s.action (t * (g : rootNormalizer c) * t⁻¹)) =
      (MulAut.congr mark) (s.action (g' : rootNormalizer c))
    rw [map_mul,map_mul,map_inv,map_mul,map_mul,map_inv,
      cubic_extension_actor s mark X φ hsquare g,
      cubic_extension_actor s mark X φ hsquare g',hg',conjugatePGL_spec]

/-- The ordinary action follows under the unchanged full marking and original
crossing equation; the source kernel and crossing descent are now discharged. -/
theorem source_full_frattini_ordinary (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hF : Nat.card F = 4)
    (mark : (s.component ⧸ pCore 2 s.component) ≃* PSL(3,F))
    (X : Subgroup G) (φ : cubicExtension s X →* ProjGenLinGroup (Fin 3) F)
    (hφ : Function.Surjective φ)
    (hsquare : ∀ b : s.component, φ (cubicComponentInclusion s X b) =
      ProjectiveSpecialLinearGroup.toPGL (mark (QuotientGroup.mk' (pCore 2 s.component) b)))
    (e : Frattini s.component ≃* Multiplicative (TraceZero F))
    (he : ∀ (b : s.component) v,
      (e (coreAction s.component (b : rootNormalizer c) v)).toAdd =
        projectiveSpecialAdjoint F (mark (QuotientGroup.mk' (pCore 2 s.component) b))
          (e v).toAdd)
    (correction : GL (Fin 3) F) (field : F ≃+* F)
    (hgraph : (MulAut.congr mark) (s.action ⟨c.t,root_normalized c D c.crossing_mem⟩) =
      linearConj F correction * graph F * fieldAction F field)
    (g : cubicExtension s X) (v : Frattini s.component) :
    (e (coreAction s.component (g : rootNormalizer c) v)).toAdd =
      projectiveAdjoint F (φ g) (e v).toAdd :=
  (sourceFrattiniGraphData s D h hF mark X φ hφ hsquare e he correction field hgraph).ordinary_action hF g v

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.SourceActionEndgame
