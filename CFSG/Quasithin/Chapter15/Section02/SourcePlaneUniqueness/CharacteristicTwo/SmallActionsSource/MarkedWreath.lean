module
public import Theory.GroupAction.ComplementaryFourWreathAction
public import Theory.Representation.BinaryOffender.RankOneNormalClosure

/-!
# The marked natural planes and factors of the small wreath action

The two coordinate planes have order four and complementary underlying
spaces. Their pointwise centralizers are the opposite coordinate SL₂(2)
factors. The literal wreath conjugation permutes these factors, and their
transvections generate the base. Each transvection fixes eight vectors.
These calculations identify the distinguished factors in Notation15.2.9;
ChiefMarking transports them to the original chief action.

The finite certificates are confined to the order72 actor and its sixteen
vectors; the general subgroup transports use structural proofs.
Source: Aschbacher--Smith, Notation15.2.9 and15.2.21(1), printed pp.1110,1114.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
abbrev C2 := Multiplicative (ZMod 2)
abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev Actor := RegularWreathProduct SL2 C2
abbrev Space := C2 → Multiplicative (Fin 2 → ZMod 2)
abbrev VectorSpace := C2 → Fin 2 → ZMod 2
abbrev flip : C2 := Multiplicative.ofAdd 1

private instance : Fintype Actor := Fintype.ofEquiv ((C2 → SL2) × C2)
  (RegularWreathProduct.equivProd SL2 C2).symm

private instance : DecidableEq Actor := fun x y =>
  decidable_of_iff (x.left = y.left ∧ x.right = y.right) RegularWreathProduct.ext_iff.symm

/-- One original natural two-space of the imprimitive four-space. -/
def plane (i : C2) : Subgroup Space where
  carrier := {v | ∀ j, j ≠ i → v j = 1}
  one_mem' := fun _ _ => rfl
  mul_mem' := by intro x y hx hy j hj; simp [hx j hj,hy j hj]
  inv_mem' := by intro x hx j hj; simp [hx j hj]

/-- The actor supported in one coordinate. -/
def coordinate (i : C2) : SL2 →* Actor where
  toFun a := ⟨fun j => if j = i then a else 1,1⟩
  map_one' := by ext j <;> simp
  map_mul' a b := by
    ext j <;> simp only [RegularWreathProduct.mul_left,RegularWreathProduct.mul_right,
      inv_one,one_mul,Pi.mul_apply]
    split_ifs <;> simp

/-- The two commuting natural S₃ factors. -/
def factor (i : C2) : Subgroup Actor := (coordinate i).range
/-- The literal paired base in the wreath product. -/
def base : Subgroup Actor := (RegularWreathProduct.rightHom : Actor →* C2).ker

theorem coordinate_injective (i : C2) : Function.Injective (coordinate i) := by
  intro a b h
  have := congrArg (fun g : Actor => g.left i) h
  simpa [coordinate] using this

theorem mem_factor (g : Actor) (i : C2) :
    g ∈ factor i ↔ g.right = 1 ∧ ∀ j, j ≠ i → g.left j = 1 := by
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨rfl,fun j hj => by simp [coordinate,hj]⟩
  · rintro ⟨hr,hl⟩
    refine ⟨g.left i,?_⟩
    ext j
    · by_cases hj : j=i
      · subst j; simp [coordinate]
      · simp [coordinate,hj,hl j hj]
    · exact hr.symm

noncomputable def factorEquiv (i : C2) : factor i ≃* SL2 :=
  (MonoidHom.ofInjective (coordinate_injective i)).symm

theorem index_cases (i : C2) : i = 1 ∨ i = flip := by revert i; decide +kernel

theorem flip_ne_one : flip ≠ 1 := by decide

theorem opposite_ne (i : C2) : flip * i ≠ i := by
  intro h
  exact flip_ne_one (mul_right_cancel (h.trans (one_mul i).symm))

theorem plane_compl : IsCompl (plane 1) (plane flip) := by
  constructor
  · rw [disjoint_iff]
    apply bot_unique
    intro v hv
    apply mem_bot.mpr
    funext i
    rcases index_cases i with rfl | rfl
    · exact hv.2 1 (Ne.symm flip_ne_one)
    · exact hv.1 flip flip_ne_one
  · apply codisjoint_iff.mpr
    apply top_unique
    intro v _
    let a : Space := fun i => if i=1 then v i else 1
    let b : Space := fun i => if i=flip then v i else 1
    have ha : a ∈ plane 1 := by intro i hi; simp [a,hi]
    have hb : b ∈ plane flip := by intro i hi; simp [b,hi]
    have he : a*b=v := by
      funext i
      rcases index_cases i with rfl | rfl <;>
        simp [a,b,Ne.symm flip_ne_one]
    rw [←he]
    exact mul_mem ((le_sup_left : plane 1 ≤ plane 1 ⊔ plane flip) ha)
      ((le_sup_right : plane flip ≤ plane 1 ⊔ plane flip) hb)

noncomputable def planeEquiv (i : C2) : plane i ≃* Multiplicative (Fin 2 → ZMod 2) where
  toFun v := v.val i
  invFun v := ⟨fun j => if j=i then v else 1,by intro j hj; simp [hj]⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    by_cases hj : j=i
    · subst j; simp
    · simp [hj,v.property j hj]
  right_inv v := by simp
  map_mul' _ _ := rfl

theorem plane_card (i : C2) : Nat.card (plane i) = 4 := by
  rw [Nat.card_congr (planeEquiv i).toEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The literal standard natural action in the source wreath convention. -/
def action (g : Actor) (v : Space) : Space := fun i =>
  Multiplicative.ofAdd (Matrix.mulVec (g.left i).1 ((v (g.right⁻¹*i)).toAdd))

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
private theorem finite_fixing : ∀ (g : Actor) (i : C2),
    (∀ v : Space, (∀ j, j ≠ i → v j = 1) → action g v = v) ↔
      g.right = 1 ∧ ∀ j, j ≠ flip*i → g.left j = 1 := by
  decide +kernel

/-- The centralizer of one natural plane is precisely the opposite S₃ factor. -/
theorem fixes_plane_iff (g : Actor) (i : C2) :
    (∀ v ∈ plane i, action g v = v) ↔ g ∈ factor (flip*i) := by
  rw [mem_factor]
  exact finite_fixing g i

theorem factor_sup_eq_base : factor 1 ⊔ factor flip = base := by
  apply le_antisymm
  · exact sup_le (fun g hg => (mem_factor g 1).mp hg |>.1)
      (fun g hg => (mem_factor g flip).mp hg |>.1)
  · intro g hg
    have hr : g.right=1 := hg
    have he : g = coordinate 1 (g.left 1) * coordinate flip (g.left flip) := by
      ext j
      · rcases index_cases j with rfl | rfl <;>
          simp [coordinate,Ne.symm flip_ne_one]
      · simpa [coordinate] using hr
    rw [he]
    exact mul_mem ((le_sup_left : factor 1 ≤ factor 1 ⊔ factor flip) ⟨_,rfl⟩)
      ((le_sup_right : factor flip ≤ factor 1 ⊔ factor flip) ⟨_,rfl⟩)

/-- Base actors preserve each factor; outside actors exchange them. -/
theorem factor_map_conj (g : Actor) (i : C2) :
    (factor i).map (MulAut.conj g).toMonoidHom = factor (g.right*i) := by
  have he (a : SL2) :
      g * coordinate i a * g⁻¹ = coordinate (g.right*i)
        (g.left (g.right*i) * a * (g.left (g.right*i))⁻¹) := by
    ext j
    · by_cases hj : j=g.right*i
      · subst j; simp [coordinate,mul_assoc]
      · have hj' : g.right⁻¹*j ≠ i := by
          intro h; apply hj; simpa [mul_assoc] using congrArg (fun x => g.right*x) h
        simp [coordinate,hj,hj']
    · simp [coordinate]
  apply le_antisymm
  · rintro _ ⟨_,⟨a,rfl⟩,rfl⟩
    exact ⟨_,(he a).symm⟩
  · rintro _ ⟨a,rfl⟩
    refine ⟨coordinate i ((g.left (g.right*i))⁻¹*a*g.left (g.right*i)),⟨_,rfl⟩,?_⟩
    change g * _ * g⁻¹ = _
    rw [he]
    simp [mul_assoc]

/-- The two elementary transvections generate each natural SL₂(2). -/
def transvection (b : Bool) : SL2 :=
  if b then ⟨!![1,1;0,1],by decide⟩ else ⟨!![1,0;1,1],by decide⟩

theorem transvection_involution (b : Bool) :
    (transvection b)^2=1 ∧ transvection b≠1 := by
  revert b
  decide +kernel

private theorem sl2_cases : ∀ a : SL2,
    a=1 ∨ a=transvection false ∨ a=transvection true ∨
    a=transvection false*transvection true ∨ a=transvection true*transvection false ∨
    a=transvection false*transvection true*transvection false := by
  decide +kernel

/-- The transvections on the two literal planes generate the paired base. -/
theorem base_le_of_transvections (B : Subgroup Actor)
    (hB : ∀ i b, coordinate i (transvection b) ∈ B) : base ≤ B := by
  rw [←factor_sup_eq_base]
  apply sup_le <;> rintro _ ⟨a,rfl⟩
  all_goals
    rcases sl2_cases a with rfl | rfl | rfl | rfl | rfl | rfl
    · simpa only [map_one] using B.one_mem
    · exact hB _ false
    · exact hB _ true
    · rw [map_mul]; exact B.mul_mem (hB _ false) (hB _ true)
    · rw [map_mul]; exact B.mul_mem (hB _ true) (hB _ false)
    · rw [map_mul,map_mul]; exact B.mul_mem (B.mul_mem (hB _ false) (hB _ true)) (hB _ false)

set_option synthInstance.maxSize 1024 in
set_option maxRecDepth 10000 in
/-- Each marked transvection fixes an actual eight-element hyperplane. -/
theorem transvection_fixed_card : ∀ i b,
    Fintype.card {v : Space // action (coordinate i (transvection b)) v = v} = 8 := by
  decide +kernel


end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource.ChiefWreath
