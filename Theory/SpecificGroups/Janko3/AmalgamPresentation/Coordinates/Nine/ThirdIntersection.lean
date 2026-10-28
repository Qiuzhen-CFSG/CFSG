module
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Nine.ModelMarking
public import Theory.SpecificGroups.Janko3.AmalgamPresentation.Coordinates.Four.OverlapMarking

/-!
# The full literal second-third intersection

The original order-180 word subgroup is the full linear complement in the
second affine local. This complement is maximal: any nonzero translation
and the natural linear action generate all translations. The second local
has order 2880 while the third has order 2160, so their intersection is a
proper overgroup of that complement and hence is exactly the marked one.
-/

public noncomputable section
namespace Sporadic.Janko3.AmalgamPresentation.NineCoordinates
open Subgroup Subgroup.CosetWordCertificate ModelCoordinates
open Representation.CentralCubicNaturalFour

private theorem affine_complement_maximal (H : Subgroup FourCoordinates.Affine)
    (hle : (SemidirectProduct.inr : LinearGroup →* FourCoordinates.Affine).range ≤ H)
    (hne : H ≠ ⊤) : H = (SemidirectProduct.inr : LinearGroup →* FourCoordinates.Affine).range := by
  apply le_antisymm ?_ hle
  intro x hx
  by_contra hn
  have hx0 : x.left ≠ 1 := by
    intro he
    apply hn
    refine ⟨x.right,?_⟩
    apply SemidirectProduct.ext
    · exact he.symm
    · rfl
  have hinr (g : LinearGroup) : (SemidirectProduct.inr g : FourCoordinates.Affine) ∈ H := hle ⟨g,rfl⟩
  have hinlx : (SemidirectProduct.inl x.left : FourCoordinates.Affine) ∈ H := by
    have he : (SemidirectProduct.inl x.left : FourCoordinates.Affine) =
        x * (SemidirectProduct.inr x.right)⁻¹ := by
      nth_rw 2 [←SemidirectProduct.inl_left_mul_inr_right x]
      group
    rw [he]
    exact H.mul_mem hx (H.inv_mem (hinr _))
  have hinl (v : Plane) : (SemidirectProduct.inl v : FourCoordinates.Affine) ∈ H := by
    by_cases hv : v = 1
    · rw [hv,map_one]
      exact H.one_mem
    obtain ⟨g,hg⟩ := Representation.SL2FourNatural.transitive_nonzero x.left.toAdd v.toAdd hx0 hv
    have he : naturalAction (Matrix.SpecialLinearGroup.toGL g) x.left = v :=
      congrArg Multiplicative.ofAdd hg
    rw [←he,SemidirectProduct.inl_aut]
    exact H.mul_mem (H.mul_mem (hinr _) hinlx) (hinr _)
  apply hne
  apply top_unique
  intro y _
  rw [←SemidirectProduct.inl_left_mul_inr_right y]
  exact H.mul_mem (hinl _) (hinr _)

private theorem eval_hom {A B α : Type*} [Group A] [Group B]
    (f : A →* B) (g : α → A) (w : Word α) :
    f (eval g w) = eval (fun i => f (g i)) w := by
  induction w with
  | nil => simp only [eval_nil,map_one]
  | cons a w ih =>
    cases ha : a.2 <;> simp only [eval_cons,ha,Bool.false_eq_true,↓reduceIte,map_mul,map_inv,ih]

private theorem linear_word_eq (which : Bool) :
    secondLocalModel.subtype (eval FourCoordinates.localGenerator
      (if which then FourCoordinates.linearSecondWord else FourCoordinates.linearFirstWord)) =
      (eval modelGenerator ((relatorWord (if which then 21 else 20)).drop 12))⁻¹ := by
  have he := modelGenerator_satisfies (if which then 21 else 20)
  have hs := eq_inv_of_mul_eq_one_left (show
    eval modelGenerator ((relatorWord (if which then 21 else 20)).take 12) *
      eval modelGenerator ((relatorWord (if which then 21 else 20)).drop 12) = 1 by
        rw [←eval_append,List.take_append_drop]
        exact he)
  rw [←hs,eval_hom]
  cases which <;> simp only [Bool.false_eq_true,↓reduceIte,FourCoordinates.linearFirstWord,
    FourCoordinates.linearSecondWord,relatorWord,List.take_succ_cons,List.take_zero,
    eval_cons,eval_nil,FourCoordinates.localGenerator,Subgroup.subtype_apply]

private theorem third_tail_mem (which : Bool) :
    eval modelGenerator ((relatorWord (if which then 21 else 20)).drop 12) ∈ thirdLocalModel := by
  have hg (i : Fin 6) (hi : i = 4 ∨ i = 5) : modelGenerator i ∈ thirdLocalModel := by
    rcases hi with rfl | rfl <;> apply Subgroup.subset_closure <;> simp
  have hall : ∀ which : Bool, ∀ a ∈ ((relatorWord (if which then 21 else 20)).drop 12),
      a.1 = 4 ∨ a.1 = 5 := by decide +kernel
  generalize hw : ((relatorWord (if which then 21 else 20)).drop 12) = w
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

private theorem linear_le_third :
    FourCoordinates.localLinearWords.map secondLocalModel.subtype ≤ thirdLocalModel := by
  rw [FourCoordinates.localLinearWords,MonoidHom.map_closure]
  apply (closure_le _).mpr
  rintro _ ⟨x,hx,rfl⟩
  rcases hx with rfl | rfl
  · rw [show secondLocalModel.subtype (eval FourCoordinates.localGenerator FourCoordinates.linearFirstWord) =
      (eval modelGenerator ((relatorWord 20).drop 12))⁻¹ from linear_word_eq false]
    exact thirdLocalModel.inv_mem (third_tail_mem false)
  · rw [show secondLocalModel.subtype (eval FourCoordinates.localGenerator FourCoordinates.linearSecondWord) =
      (eval modelGenerator ((relatorWord 21).drop 12))⁻¹ from linear_word_eq true]
    exact thirdLocalModel.inv_mem (third_tail_mem true)

/-- The original marked order-180 linear words fill the whole second-third intersection. -/
theorem second_third_intersection_eq_linear :
    secondLocalModel ⊓ thirdLocalModel = FourCoordinates.localLinearWords.map secondLocalModel.subtype := by
  let I := (secondLocalModel ⊓ thirdLocalModel).subgroupOf secondLocalModel
  have hle : FourCoordinates.localLinearWords ≤ I := by
    intro x hx
    exact ⟨x.property,linear_le_third (mem_map_of_mem _ hx)⟩
  have hne : I ≠ ⊤ := by
    intro he
    have hi : secondLocalModel ≤ thirdLocalModel := by
      intro x hx
      have hm : (⟨x,hx⟩ : secondLocalModel) ∈ I := he ▸ mem_top _
      exact hm.2
    have hc := Nat.card_le_card_of_injective (inclusion hi) (inclusion_injective hi)
    rw [FourCoordinates.secondLocalModel_card,thirdLocalModel_card] at hc
    omega
  have hm : I.map FourCoordinates.orientedLocalEquiv.toMonoidHom =
      (SemidirectProduct.inr : LinearGroup →* FourCoordinates.Affine).range := by
    apply affine_complement_maximal
    · rw [←FourCoordinates.orientedLocalEquiv_linearWords]
      exact map_mono hle
    · intro ht
      apply hne
      apply map_injective (f := FourCoordinates.orientedLocalEquiv.toMonoidHom) FourCoordinates.orientedLocalEquiv.injective
      rw [ht,map_top_of_surjective _ FourCoordinates.orientedLocalEquiv.surjective]
  have he : I = FourCoordinates.localLinearWords := by
    apply map_injective (f := FourCoordinates.orientedLocalEquiv.toMonoidHom) FourCoordinates.orientedLocalEquiv.injective
    rw [hm,FourCoordinates.orientedLocalEquiv_linearWords]
  have ha := congrArg (fun K : Subgroup secondLocalModel => K.map secondLocalModel.subtype) he
  simpa only [I,map_subgroupOf_eq_of_le inf_le_left] using ha

end Sporadic.Janko3.AmalgamPresentation.NineCoordinates
