module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.OverlapIdentification

/-!
# The actual first local with both standard overlaps

Conjugating the raw field coordinates by the explicit orientation retains
both original generators and sends the two literal overlap-word groups to
the standard point and pair subgroups, respectively.
-/
@[expose] public noncomputable section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates
open Sporadic.Janko3.SourceRecognition.Seventeen

/-- The original first pair, in its literal local subgroup. -/
def localGenerator (b : Bool) : firstLocalModel :=
  if b then ⟨modelGenerator 1,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  else ⟨modelGenerator 0,Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The actual first-local isomorphism, with point and pair orientation fixed. -/
def orientedLocalEquiv : firstLocalModel ≃* Theory.PSL2.BinaryFourFieldExtension.Model :=
  firstLocalEquiv.trans (MulAut.conj (modelEquiv orientation))

theorem orientedLocalEquiv_generator (b : Bool) :
    orientedLocalEquiv (localGenerator b) = modelEquiv (orientedGenerator b) := by
  cases b
  · change (MulAut.conj (modelEquiv orientation))
      (firstLocalEquiv ⟨modelGenerator 0,_⟩) = modelEquiv orientedFirst
    rw [firstLocalEquiv_first]
    change modelEquiv orientation * modelEquiv first * (modelEquiv orientation)⁻¹ = _
    rw [orientedFirst_eq,map_mul,map_mul,map_inv]
  · change (MulAut.conj (modelEquiv orientation))
      (firstLocalEquiv ⟨modelGenerator 1,_⟩) = modelEquiv orientedSecond
    rw [firstLocalEquiv_second]
    change modelEquiv orientation * modelEquiv second * (modelEquiv orientation)⁻¹ = _
    rw [orientedSecond_eq,map_mul,map_mul,map_inv]

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

theorem orientedLocalEquiv_word (w : Word Bool) :
    orientedLocalEquiv (eval localGenerator w) = modelEquiv (eval orientedGenerator w) := by
  have he : (fun i => orientedLocalEquiv (localGenerator i)) = fun i => modelEquiv (orientedGenerator i) :=
    funext orientedLocalEquiv_generator
  exact (eval_hom orientedLocalEquiv.toMonoidHom localGenerator w).trans
    ((congrArg (fun g => eval g w) he).trans (eval_hom modelEquiv.toMonoidHom orientedGenerator w).symm)

/-- The first pair of original overlap words, inside the actual first local. -/
def localPointWords : Subgroup firstLocalModel :=
  closure ({eval localGenerator pointFirstWord,eval localGenerator pointSecondWord} : Set _)

/-- The second pair of original overlap words, inside the actual first local. -/
def localPairWords : Subgroup firstLocalModel :=
  closure ({eval localGenerator pairFirstWord,eval localGenerator pairSecondWord} : Set _)

/-- The marked point words map onto the whole canonical point subgroup. -/
theorem orientedLocalEquiv_pointWords :
    localPointWords.map orientedLocalEquiv.toMonoidHom = ModelAmalgam.point := by
  rw [localPointWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({orientedLocalEquiv (eval localGenerator pointFirstWord),
    orientedLocalEquiv (eval localGenerator pointSecondWord)} : Set _) = _
  rw [orientedLocalEquiv_word,orientedLocalEquiv_word,pointFirst_word,pointSecond_word]
  have h := pointWords_image
  rw [pointWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton] at h
  exact h

/-- The marked pair words map onto the whole canonical pair subgroup. -/
theorem orientedLocalEquiv_pairWords :
    localPairWords.map orientedLocalEquiv.toMonoidHom = ModelAmalgam.pair := by
  rw [localPairWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({orientedLocalEquiv (eval localGenerator pairFirstWord),
    orientedLocalEquiv (eval localGenerator pairSecondWord)} : Set _) = _
  rw [orientedLocalEquiv_word,orientedLocalEquiv_word,pairFirst_word,pairSecond_word]
  have h := pairWords_image
  rw [pairWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton] at h
  exact h

/-- The marked point and pair groups generate the actual first local. -/
theorem local_overlaps_generate : localPointWords ⊔ localPairWords = ⊤ := by
  apply Subgroup.map_injective (f := orientedLocalEquiv.toMonoidHom) orientedLocalEquiv.injective
  rw [Subgroup.map_sup,orientedLocalEquiv_pointWords,orientedLocalEquiv_pairWords,
    map_top_of_surjective _ orientedLocalEquiv.surjective,ModelAmalgam.generated]

end Sporadic.Janko3.AmalgamPresentation.SixteenCoordinates
