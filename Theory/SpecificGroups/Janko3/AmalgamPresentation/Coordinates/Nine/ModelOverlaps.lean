module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ModelKernel
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.PairIntersection
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ThirdIntersection
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.Overlaps

/-!
# Literal third-local overlap subgroups and their full cubic kernel

The original Core 18–21 words are evaluated in the actual third local.
The same generator marking carries these subgroups onto the checked native
order-sixty and order-180 groups, retaining their intersection of order
thirty and the complete cubic kernel. No new recognition premise occurs.
-/

@[expose] public noncomputable section
set_option Elab.async false
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates

/-- The two original first-third overlap words inside the actual third local. -/
def thirdPairWords : Subgroup thirdLocalModel :=
  closure ({eval localGenerator (overlapWord 0),eval localGenerator (overlapWord 1)} : Set _)

/-- The two original second-third overlap words inside the actual third local. -/
def thirdOverlapWords : Subgroup thirdLocalModel :=
  closure ({eval localGenerator (overlapWord 2),eval localGenerator (overlapWord 3)} : Set _)

theorem thirdPairWords_map : thirdPairWords.map thirdLocalEquiv.toMonoidHom = rawPair := by
  rw [thirdPairWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({thirdLocalEquiv (eval localGenerator (overlapWord 0)),
    thirdLocalEquiv (eval localGenerator (overlapWord 1))} : Set _) = _
  rw [thirdLocalEquiv_word,thirdLocalEquiv_word]
  rfl

theorem thirdOverlapWords_map : thirdOverlapWords.map thirdLocalEquiv.toMonoidHom = rawThird := by
  rw [thirdOverlapWords,MonoidHom.map_closure,Set.image_insert_eq,Set.image_singleton]
  change closure ({thirdLocalEquiv (eval localGenerator (overlapWord 2)),
    thirdLocalEquiv (eval localGenerator (overlapWord 3))} : Set _) = _
  rw [thirdLocalEquiv_word,thirdLocalEquiv_word]
  rfl

theorem thirdPairWords_card : Nat.card thirdPairWords = 60 := by
  rw [←card_map_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective,
    thirdPairWords_map,rawPair_card]

theorem thirdOverlapWords_card : Nat.card thirdOverlapWords = 180 := by
  rw [←card_map_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective,
    thirdOverlapWords_map,rawThird_card]

theorem thirdPairWords_inf_thirdOverlapWords_card :
    Nat.card (thirdPairWords ⊓ thirdOverlapWords : Subgroup thirdLocalModel) = 30 := by
  rw [←card_map_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective,
    Subgroup.map_inf _ _ _ thirdLocalEquiv.injective,thirdPairWords_map,thirdOverlapWords_map,rawPair_inf_rawThird_card]

theorem cubicKernel_le_thirdPairWords : cubicKernel ≤ thirdPairWords := by
  apply (map_le_map_iff_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective).mp
  rw [cubicKernel_map,thirdPairWords_map]
  exact kernel_le_rawPair

theorem cubicKernel_le_thirdOverlapWords : cubicKernel ≤ thirdOverlapWords := by
  apply (map_le_map_iff_of_injective (f := thirdLocalEquiv.toMonoidHom) thirdLocalEquiv.injective).mp
  rw [cubicKernel_map,thirdOverlapWords_map]
  exact kernel_le_rawThird

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

private def overlapIndex (i : Fin 4) : Fin 22 :=
  ⟨18+i.val,Nat.add_lt_add_left i.isLt 18⟩

private def reindexWord (w : Word Bool) : Word (Fin 6) :=
  w.map (fun a => (if a.1 then 5 else 4,a.2))

private theorem tail_word : ∀ i : Fin 4,
    (relatorWord (overlapIndex i)).drop (if i.val < 2 then 11 else 12) =
      FreeGroup.invRev (reindexWord (overlapWord i)) := by
  decide +kernel

private theorem eval_reindex (w : Word Bool) :
    eval modelGenerator (reindexWord w) = thirdLocalModel.subtype (eval localGenerator w) := by
  rw [eval_hom]
  induction w with
  | nil => rfl
  | cons a w ih =>
    rcases a with ⟨b,sgn⟩
    cases b <;> cases sgn <;>
      simp only [reindexWord,List.map_cons,eval_cons,Bool.false_eq_true,↓reduceIte,
        localGenerator,Subgroup.subtype_apply] at ih ⊢ <;> rw [ih]

private theorem overlap_core_eq (i : Fin 4) :
    thirdLocalModel.subtype (eval localGenerator (overlapWord i)) =
      (eval modelGenerator ((relatorWord ⟨18+i.val,by omega⟩).drop (if i.val < 2 then 11 else 12)))⁻¹ := by
  change _ = (eval modelGenerator ((relatorWord (overlapIndex i)).drop _))⁻¹
  rw [tail_word,eval_invRev,inv_inv,eval_reindex]


private theorem first_letters : ∀ i : Fin 4, i.val < 2 →
    ∀ a ∈ (relatorWord (overlapIndex i)).take 11, a.1 = 0 ∨ a.1 = 1 := by
  decide +kernel

private theorem second_letters : ∀ i : Fin 4, 2 ≤ i.val →
    ∀ a ∈ (relatorWord (overlapIndex i)).take 12, a.1 = 2 ∨ a.1 = 3 := by
  decide +kernel

private theorem third_pair_in_first (i : Fin 2) :
    thirdLocalModel.subtype (eval localGenerator (overlapWord ⟨i.val,by omega⟩)) ∈ firstLocalModel := by
  rw [overlap_core_eq]
  have he := modelGenerator_satisfies ⟨18+i.val,by omega⟩
  have hs := eq_inv_of_mul_eq_one_left (show
    eval modelGenerator ((relatorWord ⟨18+i.val,by omega⟩).take 11) *
      eval modelGenerator ((relatorWord ⟨18+i.val,by omega⟩).drop 11) = 1 by
        rw [←eval_append,List.take_append_drop]
        exact he)
  have hlt : i.val < 2 := i.isLt
  rw [if_pos hlt,←hs]
  have hg (j : Fin 6) (hj : j = 0 ∨ j = 1) : modelGenerator j ∈ firstLocalModel := by
    rcases hj with rfl | rfl <;> apply Subgroup.subset_closure <;> simp
  have hall : ∀ a ∈ ((relatorWord ⟨18+i.val,by omega⟩).take 11),
      a.1 = 0 ∨ a.1 = 1 := first_letters ⟨i.val,by omega⟩ i.isLt
  generalize hw : ((relatorWord ⟨18+i.val,by omega⟩).take 11) = w
  have ha : ∀ a ∈ w, a.1 = 0 ∨ a.1 = 1 := hw ▸ hall
  clear hw
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply firstLocalModel.mul_mem _ (ih (by intro b hb; exact ha b (by simp [hb])))
    have hm := hg a.1 (ha a (by simp))
    split
    · exact hm
    · exact firstLocalModel.inv_mem hm

/-- The third-local word subgroup is the full literal first-third intersection. -/
theorem thirdPairWords_ambient : thirdPairWords.map thirdLocalModel.subtype =
    firstLocalModel ⊓ thirdLocalModel := by
  have hle : thirdPairWords.map thirdLocalModel.subtype ≤ firstLocalModel ⊓ thirdLocalModel := by
    refine le_inf ?_ (map_subtype_le _)
    rw [thirdPairWords,MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨x,hx,rfl⟩
    rcases hx with rfl | rfl
    · exact third_pair_in_first 0
    · exact third_pair_in_first 1
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective thirdLocalModel.subtype_injective,thirdPairWords_card]
  exact first_third_intersection_card_le

private theorem third_overlap_in_second (i : Fin 2) :
    thirdLocalModel.subtype (eval localGenerator (overlapWord ⟨2+i.val,by omega⟩)) ∈ secondLocalModel := by
  rw [overlap_core_eq]
  have he := modelGenerator_satisfies ⟨18+(2+i.val),by omega⟩
  have hs := eq_inv_of_mul_eq_one_left (show
    eval modelGenerator ((relatorWord ⟨18+(2+i.val),by omega⟩).take 12) *
      eval modelGenerator ((relatorWord ⟨18+(2+i.val),by omega⟩).drop 12) = 1 by
        rw [←eval_append,List.take_append_drop]
        exact he)
  have hlt : ¬ 2+i.val < 2 := by omega
  rw [if_neg hlt,←hs]
  have hg (j : Fin 6) (hj : j = 2 ∨ j = 3) : modelGenerator j ∈ secondLocalModel := by
    rcases hj with rfl | rfl <;> apply Subgroup.subset_closure <;> simp
  have hall : ∀ a ∈ ((relatorWord ⟨18+(2+i.val),by omega⟩).take 12),
      a.1 = 2 ∨ a.1 = 3 := second_letters ⟨2+i.val,by omega⟩ (by change 2 ≤ 2+i.val; omega)
  generalize hw : ((relatorWord ⟨18+(2+i.val),by omega⟩).take 12) = w
  have ha : ∀ a ∈ w, a.1 = 2 ∨ a.1 = 3 := hw ▸ hall
  clear hw
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [eval_cons]
    apply secondLocalModel.mul_mem _ (ih (by intro b hb; exact ha b (by simp [hb])))
    have hm := hg a.1 (ha a (by simp))
    split
    · exact hm
    · exact secondLocalModel.inv_mem hm

/-- The third-local order-180 word subgroup is the full literal second-third intersection. -/
theorem thirdOverlapWords_ambient : thirdOverlapWords.map thirdLocalModel.subtype =
    secondLocalModel ⊓ thirdLocalModel := by
  have hle : thirdOverlapWords.map thirdLocalModel.subtype ≤ secondLocalModel ⊓ thirdLocalModel := by
    refine le_inf ?_ (map_subtype_le _)
    rw [thirdOverlapWords,MonoidHom.map_closure]
    apply (closure_le _).mpr
    rintro _ ⟨x,hx,rfl⟩
    rcases hx with rfl | rfl
    · exact third_overlap_in_second 0
    · exact third_overlap_in_second 1
  apply eq_of_le_of_card_ge hle
  rw [card_map_of_injective thirdLocalModel.subtype_injective,thirdOverlapWords_card,
    second_third_intersection_eq_linear,card_map_of_injective secondLocalModel.subtype_injective]
  rw [←card_map_of_injective (f := FourCoordinates.orientedLocalEquiv.toMonoidHom)
    FourCoordinates.orientedLocalEquiv.injective,FourCoordinates.orientedLocalEquiv_linearWords,
    ←Nat.card_congr (MonoidHom.ofInjective
      (SemidirectProduct.inr_injective (φ := Representation.CentralCubicNaturalFour.naturalAction))).toEquiv]
  rw [Matrix.card_GL_field,Representation.SL2FourNatural.card_field]
  decide

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
