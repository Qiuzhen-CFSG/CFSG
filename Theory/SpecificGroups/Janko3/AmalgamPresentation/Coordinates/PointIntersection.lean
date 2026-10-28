module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Sixteen.OverlapMarking
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.OverlapMarking

/-!
# The full actual first-second intersection

The two literal overlap words agree by relators sixteen and seventeen.
They generate the whole 480-element point subgroup. Both local orders
force their full intersection to have order dividing gcd(8160,2880)=480,
so these same word groups are the entire actual intersection.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
open Subgroup Subgroup.CosetWordCertificate

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

/-- Equality of the two actual marked generators on both local carriers. -/
theorem point_singer_word_eq (b : Bool) :
    firstLocalModel.subtype (eval SixteenCoordinates.localGenerator
      (if b then SixteenCoordinates.pointSecondWord else SixteenCoordinates.pointFirstWord)) =
    secondLocalModel.subtype (eval FourCoordinates.localGenerator
      (if b then FourCoordinates.singerSecondWord else FourCoordinates.singerFirstWord)) := by
  have he := modelGenerator_satisfies (if b then 17 else 16)
  have hs := eq_inv_of_mul_eq_one_left (show
    eval modelGenerator ((relatorWord (if b then 17 else 16)).take (if b then 12 else 3)) *
      eval modelGenerator ((relatorWord (if b then 17 else 16)).drop (if b then 12 else 3)) = 1 by
        rw [←eval_append,List.take_append_drop]
        exact he)
  rw [eval_hom,eval_hom]
  cases b <;> simpa only [Bool.false_eq_true,↓reduceIte,
    SixteenCoordinates.pointFirstWord,SixteenCoordinates.pointSecondWord,
    FourCoordinates.singerFirstWord,FourCoordinates.singerSecondWord,
    SixteenCoordinates.localGenerator,FourCoordinates.localGenerator,
    relatorWord,List.take_succ_cons,List.take_zero,List.drop_succ_cons,List.drop_zero,
    eval_cons,eval_nil,Subgroup.subtype_apply,mul_one,mul_inv_rev,inv_inv,inv_one,mul_assoc] using hs

/-- The two local word groups are literally the same ambient subgroup. -/
theorem point_singer_subgroups_eq :
    SixteenCoordinates.localPointWords.map firstLocalModel.subtype =
      FourCoordinates.localSingerWords.map secondLocalModel.subtype := by
  rw [SixteenCoordinates.localPointWords,FourCoordinates.localSingerWords,
    MonoidHom.map_closure,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton,
    Set.image_insert_eq,Set.image_singleton]
  rw [show firstLocalModel.subtype (eval SixteenCoordinates.localGenerator SixteenCoordinates.pointFirstWord) =
    secondLocalModel.subtype (eval FourCoordinates.localGenerator FourCoordinates.singerFirstWord) from
      point_singer_word_eq false,
    show firstLocalModel.subtype (eval SixteenCoordinates.localGenerator SixteenCoordinates.pointSecondWord) =
    secondLocalModel.subtype (eval FourCoordinates.localGenerator FourCoordinates.singerSecondWord) from
      point_singer_word_eq true]

/-- The full first-second intersection is exactly its original point-word subgroup. -/
theorem first_second_intersection_eq_point :
    firstLocalModel ⊓ secondLocalModel =
      SixteenCoordinates.localPointWords.map firstLocalModel.subtype := by
  have hle : SixteenCoordinates.localPointWords.map firstLocalModel.subtype ≤
      firstLocalModel ⊓ secondLocalModel := by
    apply le_inf (map_subtype_le _)
    rw [point_singer_subgroups_eq]
    exact map_subtype_le _
  have hc : Nat.card (firstLocalModel ⊓ secondLocalModel : Subgroup Model) ≤ 480 := by
    have hd := Nat.dvd_gcd (card_dvd_of_le (show firstLocalModel ⊓ secondLocalModel ≤ firstLocalModel from inf_le_left))
      (card_dvd_of_le (show firstLocalModel ⊓ secondLocalModel ≤ secondLocalModel from inf_le_right))
    rw [firstLocalModel_card,FourCoordinates.secondLocalModel_card] at hd
    exact Nat.le_of_dvd (by decide : 0 < 480) (by simpa using hd)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective firstLocalModel.subtype_injective]
  rw [←card_map_of_injective (f := SixteenCoordinates.orientedLocalEquiv.toMonoidHom)
    SixteenCoordinates.orientedLocalEquiv.injective,SixteenCoordinates.orientedLocalEquiv_pointWords]
  simpa only [SourceRecognition.Seventeen.ModelAmalgam.point_card] using hc

/-- The same full intersection is the literal Singer word subgroup in the second local. -/
theorem first_second_intersection_eq_singer :
    firstLocalModel ⊓ secondLocalModel =
      FourCoordinates.localSingerWords.map secondLocalModel.subtype := by
  rw [first_second_intersection_eq_point,point_singer_subgroups_eq]
end Sporadic.Janko3.AmalgamPresentation.ModelCoordinates
