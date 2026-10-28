module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.Overlaps

/-!
# The actual second local with both standard overlaps

A single explicit translation orients the exact ATLAS pair and sends its
original order-480 and order-180 overlap-word groups to the existing Singer
affine subgroup and the literal linear complement. These word groups also
generate the full actual second local. No arbitrary overlap compatibility is
assumed; compatibility with the other two independent local markings remains
a separate simultaneous marking theorem.
-/

@[expose] public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.FourCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates
open Representation.CentralCubicNaturalFour
open Sporadic.Janko3.SourceRecognition

/-- The original second pair as literal elements of its generated subgroup. -/
def localGenerator (b : Bool) : secondLocalModel :=
  if b then ⟨modelGenerator 3,Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  else ⟨modelGenerator 2,Subgroup.subset_closure (Set.mem_insert _ _)⟩

/-- The actual affine marking, retaining the simultaneous Singer/linear orientation. -/
def orientedLocalEquiv : secondLocalModel ≃* Affine :=
  secondLocalEquiv.trans (MulAut.conj orientation)

theorem orientedLocalEquiv_generator (b : Bool) :
    orientedLocalEquiv (localGenerator b) = orientedGenerator b := by
  cases b
  · change (MulAut.conj orientation) (secondLocalEquiv ⟨modelGenerator 2,_⟩) = orientedFirst
    rw [secondLocalEquiv_first,orientedFirst_eq]
    rfl
  · change (MulAut.conj orientation) (secondLocalEquiv ⟨modelGenerator 3,_⟩) = orientedSecond
    rw [secondLocalEquiv_second,orientedSecond_eq]
    rfl

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

theorem orientedLocalEquiv_word (w : Word Bool) :
    orientedLocalEquiv (eval localGenerator w) = eval orientedGenerator w := by
  have he : (fun i => orientedLocalEquiv (localGenerator i)) = orientedGenerator :=
    funext orientedLocalEquiv_generator
  exact (eval_hom orientedLocalEquiv.toMonoidHom localGenerator w).trans
    (congrArg (fun g => eval g w) he)

/-- The literal G12 word group in the actual second local. -/
def localSingerWords : Subgroup secondLocalModel :=
  closure ({eval localGenerator singerFirstWord,eval localGenerator singerSecondWord} : Set _)

/-- The literal G23 word group in the actual second local. -/
def localLinearWords : Subgroup secondLocalModel :=
  closure ({eval localGenerator linearFirstWord,eval localGenerator linearSecondWord} : Set _)

/-- The exact original G12 words map onto the canonical Singer field-affine subgroup. -/
theorem orientedLocalEquiv_singerWords :
    localSingerWords.map orientedLocalEquiv.toMonoidHom = SingerField.affineEmbedding.range := by
  rw [localSingerWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({orientedLocalEquiv (eval localGenerator singerFirstWord),
    orientedLocalEquiv (eval localGenerator singerSecondWord)} : Set _) = _
  rw [orientedLocalEquiv_word,orientedLocalEquiv_word,singerFirst_word,singerSecond_word]
  exact singerWords_eq

/-- The exact original G23 words map onto the pure linear complement. -/
theorem orientedLocalEquiv_linearWords :
    localLinearWords.map orientedLocalEquiv.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* Affine).range := by
  rw [localLinearWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({orientedLocalEquiv (eval localGenerator linearFirstWord),
    orientedLocalEquiv (eval localGenerator linearSecondWord)} : Set _) = _
  rw [orientedLocalEquiv_word,orientedLocalEquiv_word,linearFirst_word,linearSecond_word]
  exact linearWords_eq

/-- The two original overlap word groups generate the actual second local. -/
theorem local_overlaps_generate : localSingerWords ⊔ localLinearWords = ⊤ := by
  apply Subgroup.map_injective (f := orientedLocalEquiv.toMonoidHom) orientedLocalEquiv.injective
  rw [Subgroup.map_sup,orientedLocalEquiv_singerWords,orientedLocalEquiv_linearWords,
    map_top_of_surjective _ orientedLocalEquiv.surjective]
  apply top_unique
  intro x _
  have hl : (SemidirectProduct.inl x.left : Affine) ∈ SingerField.affineEmbedding.range := by
    obtain ⟨v,hv⟩ := SingerField.rootCoordinates.surjective x.left
    exact ⟨SingerField.root v,by rw [SingerField.affineEmbedding_root,hv]⟩
  have hr : (SemidirectProduct.inr x.right : Affine) ∈
      (SemidirectProduct.inr : LinearGroup →* Affine).range := ⟨x.right,rfl⟩
  have hx := (SingerField.affineEmbedding.range ⊔
    (SemidirectProduct.inr : LinearGroup →* Affine).range).mul_mem
      ((show SingerField.affineEmbedding.range ≤ SingerField.affineEmbedding.range ⊔
        (SemidirectProduct.inr : LinearGroup →* Affine).range from le_sup_left) hl)
      ((show (SemidirectProduct.inr : LinearGroup →* Affine).range ≤
        SingerField.affineEmbedding.range ⊔
          (SemidirectProduct.inr : LinearGroup →* Affine).range from le_sup_right) hr)
  rwa [SemidirectProduct.inl_left_mul_inr_right] at hx

end Sporadic.Janko3.AmalgamPresentation.FourCoordinates
