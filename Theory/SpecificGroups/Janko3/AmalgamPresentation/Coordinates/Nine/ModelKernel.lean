module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ModelMarking
public import Theory.SpecificGroups.Janko3.SourceRecognition.CubicNormalizerModelPair

/-!
# Retained words and full cubic kernel of the actual third local

The marking transports every original word, and its projective quotient has
exactly the full order-three kernel. These interfaces keep the literal model
carrier throughout subsequent overlap normalization.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates

/-- The actual marked pair in the literal third local carrier. -/
def localGenerator (b : Bool) : thirdLocalModel :=
  if b then ⟨modelGenerator 5,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  else ⟨modelGenerator 4,Subgroup.subset_closure (Set.mem_insert _ _)⟩

theorem thirdLocalEquiv_generator (b : Bool) :
    thirdLocalEquiv (localGenerator b) = if b then canonicalSecond else canonicalFirst := by
  cases b
  · exact thirdLocalEquiv_first
  · exact thirdLocalEquiv_second

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

/-- Every original two-generator word retains its canonical value. -/
theorem thirdLocalEquiv_word (w : Word Bool) :
    thirdLocalEquiv (eval localGenerator w) =
      eval (fun b => if b then canonicalSecond else canonicalFirst) w := by
  exact (eval_hom thirdLocalEquiv.toMonoidHom localGenerator w).trans
    (congrArg (fun g => eval g w) (funext thirdLocalEquiv_generator))

/-- The actual quotient onto the projective complement, with the full kernel. -/
def cubicProjection : thirdLocalModel →* P :=
  SourceRecognition.CubicNormalizerModel.projection.comp thirdLocalEquiv.toMonoidHom

def cubicKernel : Subgroup thirdLocalModel := cubicProjection.ker

theorem cubicProjection_surjective : Function.Surjective cubicProjection :=
  SourceRecognition.CubicNormalizerModel.projection_surjective.comp thirdLocalEquiv.surjective

/-- The same local marking carries the entire kernel onto the canonical cubic. -/
theorem cubicKernel_map : cubicKernel.map thirdLocalEquiv.toMonoidHom =
    SourceRecognition.CubicNormalizerModel.projection.ker := by
  change (SourceRecognition.CubicNormalizerModel.projection.ker.comap
    thirdLocalEquiv.toMonoidHom).map thirdLocalEquiv.toMonoidHom = _
  exact map_comap_eq_self_of_surjective thirdLocalEquiv.surjective _

theorem cubicKernel_card : Nat.card cubicKernel = 3 := by
  rw [←card_map_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective,
    cubicKernel_map,SourceRecognition.CubicNormalizerModel.projection_kernel_card]

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
