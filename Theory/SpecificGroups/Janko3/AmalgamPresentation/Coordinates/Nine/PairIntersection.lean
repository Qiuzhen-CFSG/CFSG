module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ModelMarking
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.OverlapMarking
import all Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Model

/-!
# The full literal first-third intersection

The first local fixes point zero. Thirty-six checked third-local words have
distinct images of that point, so its intersection with the first local has
order at most sixty. The original two overlap words already generate sixty
elements in the first local. The exact amalgam relations put both words in
the third local, proving equality with the whole intersection.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates OrderCertificate

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

private theorem first_fixes (x : Model) (hx : x ∈ firstLocalModel) : embedding x 0 = 0 := by
  have hi : embedding x ∈ H1 := by
    rw [←firstLocalModel_image]
    exact mem_map_of_mem embedding hx
  exact H1_fix ⟨embedding x,hi⟩

private def intersectionWitness (i : Fin 36 × ↥(firstLocalModel ⊓ thirdLocalModel)) : thirdLocalModel :=
  ⟨eval pairGenerator (baseWord i.1) * (i.2 : Model),
    thirdLocalModel.mul_mem (word_mem _) i.2.property.2⟩

private theorem intersectionWitness_injective : Function.Injective intersectionWitness := by
  rintro ⟨i,x⟩ ⟨k,y⟩ he
  have hv := congrArg (fun x : thirdLocalModel => (x : Model)) he
  change eval pairGenerator (baseWord i) * (x : Model) = eval pairGenerator (baseWord k) * (y : Model) at hv
  have hzero := congrArg (fun g : Model => embedding g 0) hv
  simp only [map_mul,Equiv.Perm.mul_apply,first_fixes x x.property.1,
    first_fixes y y.property.1,embedding_eval,base_cert] at hzero
  have hik : i = k := baseImage_injective hzero
  subst k
  exact Prod.ext rfl (Subtype.ext (mul_left_cancel hv))

/-- The upper bound is a literal permutation-orbit bound in the actual model. -/
theorem first_third_intersection_card_le : Nat.card (firstLocalModel ⊓ thirdLocalModel : Subgroup Model) ≤ 60 := by
  have hc := Nat.card_le_card_of_injective intersectionWitness intersectionWitness_injective
  rw [Nat.card_prod,Nat.card_fin,thirdLocalModel_card] at hc
  omega

private theorem first_pair_word_eq (which : Bool) :
    firstLocalModel.subtype (eval SixteenCoordinates.localGenerator
      (if which then SixteenCoordinates.pairSecondWord else SixteenCoordinates.pairFirstWord)) =
      (eval modelGenerator ((relatorWord (if which then 19 else 18)).drop 11))⁻¹ := by
  have he := modelGenerator_satisfies (if which then 19 else 18)
  have hs := eq_inv_of_mul_eq_one_left (show
    eval modelGenerator ((relatorWord (if which then 19 else 18)).take 11) *
      eval modelGenerator ((relatorWord (if which then 19 else 18)).drop 11) = 1 by
        rw [←eval_append,List.take_append_drop]
        exact he)
  rw [←hs]
  rw [eval_hom]
  cases which <;> simp only [Bool.false_eq_true,↓reduceIte,SixteenCoordinates.pairFirstWord,
    SixteenCoordinates.pairSecondWord,relatorWord,List.take_succ_cons,List.take_zero,
    eval_cons,eval_nil,SixteenCoordinates.localGenerator,Subgroup.subtype_apply]

private theorem third_tail_mem (which : Bool) :
    eval modelGenerator ((relatorWord (if which then 19 else 18)).drop 11) ∈ thirdLocalModel := by
  have hg (i : Fin 6) (hi : i = 4 ∨ i = 5) : modelGenerator i ∈ thirdLocalModel := by
    rcases hi with rfl | rfl <;> apply Subgroup.subset_closure <;> simp
  have hall : ∀ which : Bool, ∀ a ∈ ((relatorWord (if which then 19 else 18)).drop 11),
      a.1 = 4 ∨ a.1 = 5 := by decide +kernel
  generalize hw : ((relatorWord (if which then 19 else 18)).drop 11) = w
  have ha : ∀ a ∈ w, a.1 = 4 ∨ a.1 = 5 := hw ▸ hall which
  clear hw
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply thirdLocalModel.mul_mem _ (ih (by intro b hb; exact ha b (by simp [hb])))
    have hm := hg a.1 (ha a (by simp))
    split
    · exact hm
    · exact thirdLocalModel.inv_mem hm

private theorem pair_le_third :
    SixteenCoordinates.localPairWords.map firstLocalModel.subtype ≤ thirdLocalModel := by
  rw [SixteenCoordinates.localPairWords,MonoidHom.map_closure]
  apply (closure_le _).mpr
  rintro _ ⟨x,hx,rfl⟩
  rcases hx with rfl | rfl
  · rw [show firstLocalModel.subtype (eval SixteenCoordinates.localGenerator SixteenCoordinates.pairFirstWord) =
      (eval modelGenerator ((relatorWord 18).drop 11))⁻¹ from first_pair_word_eq false]
    exact thirdLocalModel.inv_mem (third_tail_mem false)
  · rw [show firstLocalModel.subtype (eval SixteenCoordinates.localGenerator SixteenCoordinates.pairSecondWord) =
      (eval modelGenerator ((relatorWord 19).drop 11))⁻¹ from first_pair_word_eq true]
    exact thirdLocalModel.inv_mem (third_tail_mem true)

/-- The actual first-third intersection is exactly the original marked pair. -/
theorem first_third_intersection_eq_pair :
    firstLocalModel ⊓ thirdLocalModel = SixteenCoordinates.localPairWords.map firstLocalModel.subtype := by
  have hle : SixteenCoordinates.localPairWords.map firstLocalModel.subtype ≤ firstLocalModel ⊓ thirdLocalModel :=
    le_inf (map_subtype_le _) pair_le_third
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective firstLocalModel.subtype_injective]
  rw [←card_map_of_injective (f := SixteenCoordinates.orientedLocalEquiv.toMonoidHom)
    SixteenCoordinates.orientedLocalEquiv.injective,SixteenCoordinates.orientedLocalEquiv_pairWords]
  simpa only [SourceRecognition.Seventeen.ModelAmalgam.pair_card] using first_third_intersection_card_le

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
