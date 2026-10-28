module
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.SymmetricFourWreath.Coordinates

/-!
# Sylow subgroups of the binary symmetric-five extension

For the even-sum binary permutation module on five letters, the split extension
by `S₅` has Sylow 2-subgroups isomorphic to `D₈ wr C₂`. Four free coordinates form
two planes; the point-fixing Sylow of `S₅` flips each plane and interchanges them.
This identifies the extension with the wreath product of two dihedral groups.

The product result keeps a given 2-group direct factor literally marked: its
coordinates are unchanged, and it is the kernel of projection onto the wreath
factor. These are the model calculations used in the single-`A₅` case of
Aschbacher--Smith, *The Classification of Quasithin Groups*, (2.4.29).
-/

@[expose] public section
namespace BinaryPermutation.AlternatingFiveExtension
open Subgroup
/-- The split binary permutation extension by the full symmetric group. -/
abbrev Model := V ⋊[coreAction] Equiv.Perm (Fin 5)
instance : Finite Model := Finite.of_equiv _ SemidirectProduct.equivProd.symm
namespace SylowModel
abbrev Bit := Multiplicative (ZMod 2)
abbrev Plane := Bit × Bit
abbrev Base := Plane × Plane

def involutionHom {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1) : Bit →* G where
  toFun x := a ^ x.toAdd.val
  map_one' := by simp
  map_mul' x y := by
    change a ^ (x.toAdd + y.toAdd).val = a ^ x.toAdd.val * a ^ y.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    exact (pow_eq_pow_mod _ ha).symm

@[simp] theorem involutionHom_gen {G : Type*} [Group G] (a : G) (ha : a ^ 2 = 1) :
    involutionHom a ha (.ofAdd 1) = a := by change a ^ 1 = a; exact pow_one a

def planeAction : Bit →* MulAut Plane :=
  involutionHom (MulEquiv.prodComm : MulAut Plane) (by ext x <;> rfl)

abbrev PlaneGroup := Plane ⋊[planeAction] Bit
instance : Fintype PlaneGroup := Fintype.ofEquiv (Plane × Bit) SemidirectProduct.equivProd.symm

def rotation : PlaneGroup := ⟨(.ofAdd 1, 1), .ofAdd 1⟩
def reflection : PlaneGroup := ⟨1, .ofAdd 1⟩

theorem plane_dihedral : Nonempty (PlaneGroup ≃* DihedralGroup 4) := by
  apply dihedralGroup_equiv_of_relations (by decide) rotation reflection
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · apply (eq_top_iff' _).mpr
    intro x
    have h : ∀ x : PlaneGroup, ∃ i : ZMod 4,
        x = rotation ^ i.val ∨ x = reflection * rotation ^ i.val := by decide +kernel
    obtain ⟨i, hi | hi⟩ := h x
    · rw [hi]
      exact pow_mem (subset_closure (by simp)) _
    · rw [hi]
      exact mul_mem (subset_closure (by simp)) (pow_mem (subset_closure (by simp)) _)
  · rw [Nat.card_congr (SemidirectProduct.equivProd : PlaneGroup ≃ Plane × Bit)]
    norm_num [Plane, Bit, Nat.card_prod, Nat.card_zmod]

def coreCoordinates : Base ≃* Multiplicative (core (Fin 5)) where
  toFun x := .ofAdd ⟨![x.1.1.toAdd, x.1.2.toAdd, x.2.1.toAdd, x.2.2.toAdd,
    x.1.1.toAdd + x.1.2.toAdd + x.2.1.toAdd + x.2.2.toAdd], by
      simp only [mem_core, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
        Fin.sum_univ_zero, add_zero]
      have h : ∀ a : ZMod 2, a + a = 0 := by decide
      convert h (x.1.1.toAdd + x.1.2.toAdd + x.2.1.toAdd + x.2.2.toAdd) using 1; abel⟩
  invFun x := ((.ofAdd (x.toAdd.val 0), .ofAdd (x.toAdd.val 1)),
    (.ofAdd (x.toAdd.val 2), .ofAdd (x.toAdd.val 3)))
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    change (![x.toAdd.val 0, x.toAdd.val 1, x.toAdd.val 2, x.toAdd.val 3,
      x.toAdd.val 0 + x.toAdd.val 1 + x.toAdd.val 2 + x.toAdd.val 3] : Fin 5 → ZMod 2) = x.toAdd.val
    funext i
    have hx := x.toAdd.property
    simp only [mem_core, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hx
    fin_cases i
    all_goals try rfl
    change x.toAdd.val 0 + x.toAdd.val 1 + x.toAdd.val 2 + x.toAdd.val 3 = x.toAdd.val 4
    exact (by decide : ∀ a b c d e : ZMod 2, a + (b + (c + (d + e))) = 0 →
      a + b + c + d = e) _ _ _ _ _ hx
  map_mul' x y := by
    apply Subtype.ext
    change (![x.1.1.toAdd + y.1.1.toAdd, x.1.2.toAdd + y.1.2.toAdd,
      x.2.1.toAdd + y.2.1.toAdd, x.2.2.toAdd + y.2.2.toAdd,
      (x.1.1.toAdd + y.1.1.toAdd) + (x.1.2.toAdd + y.1.2.toAdd) +
      (x.2.1.toAdd + y.2.1.toAdd) + (x.2.2.toAdd + y.2.2.toAdd)] : Fin 5 → ZMod 2) =
      ![x.1.1.toAdd, x.1.2.toAdd, x.2.1.toAdd, x.2.2.toAdd,
        x.1.1.toAdd + x.1.2.toAdd + x.2.1.toAdd + x.2.2.toAdd] +
      ![y.1.1.toAdd, y.1.2.toAdd, y.2.1.toAdd, y.2.2.toAdd,
        y.1.1.toAdd + y.1.2.toAdd + y.2.1.toAdd + y.2.2.toAdd]
    funext i
    fin_cases i <;> dsimp
    abel

abbrev Actor := RegularWreathProduct Bit Bit
abbrev PlaneWreath := RegularWreathProduct PlaneGroup Bit
private instance : Fintype Actor := Fintype.ofEquiv _ (RegularWreathProduct.equivProd Bit Bit).symm
private instance : DecidableEq Actor := (RegularWreathProduct.equivProd Bit Bit).injective.decidableEq
private instance : Fintype PlaneWreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd PlaneGroup Bit).symm
private instance : DecidableEq PlaneWreath := (RegularWreathProduct.equivProd PlaneGroup Bit).injective.decidableEq

def actorPermutation (a : Actor) : Equiv.Perm (Fin 5) :=
  (Equiv.swap (0 : Fin 5) 1) ^ (a.left 1).toAdd.val *
    (Equiv.swap (2 : Fin 5) 3) ^ (a.left (.ofAdd 1)).toAdd.val *
    (Equiv.swap (0 : Fin 5) 2 * Equiv.swap 1 3) ^ a.right.toAdd.val

def actor : Actor →* Equiv.Perm (Fin 5) where
  toFun := actorPermutation
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

theorem actor_injective : Function.Injective actor := by decide +kernel

def coordinates : (Bit → Plane) →* V := coreCoordinates.toMonoidHom.comp
  ((Pi.evalMonoidHom _ 1).prod (Pi.evalMonoidHom _ (.ofAdd 1)))

theorem coordinates_injective : Function.Injective coordinates := by
  intro x y h
  have hh := coreCoordinates.injective h
  funext i
  have hi : i=1 ∨ i=Multiplicative.ofAdd 1 := by
    exact (by decide : ∀ i : Bit, i=1 ∨ i=Multiplicative.ofAdd 1) i
  rcases hi with rfl | rfl
  · exact congrArg Prod.fst hh
  · exact congrArg Prod.snd hh

theorem coordinate_action (a : Actor) (v : Bit → Plane) :
    coordinates (fun i => planeAction (a.left i) (v (a.right⁻¹*i))) =
      coreAction (actor a) (coordinates v) := by
  have h : ∀ (a : Actor) (v : Bit → Plane),
    coordinates (fun i => planeAction (a.left i) (v (a.right⁻¹*i))) =
      coreAction (actor a) (coordinates v) := by decide +kernel
  exact h a v

def actorProjection : PlaneWreath →* Actor where
  toFun x := ⟨fun i => (x.left i).right,x.right⟩
  map_one' := rfl
  map_mul' _ _ := rfl

def embedding : PlaneWreath →* Model where
  toFun x := ⟨coordinates (fun i => (x.left i).left),actor (actorProjection x)⟩
  map_one' := by
    apply SemidirectProduct.ext
    · exact map_one coordinates
    · exact (actor.comp actorProjection).map_one
  map_mul' x y := by
    apply SemidirectProduct.ext
    · change coordinates (fun i => (x.left i).left *
        planeAction ((x.left i).right) ((y.left (x.right⁻¹*i)).left)) =
        coordinates (fun i => (x.left i).left) *
          coreAction (actor (actorProjection x)) (coordinates (fun i => (y.left i).left))
      rw [← coordinate_action (actorProjection x)]
      exact coordinates.map_mul _ _
    · exact (actor.comp actorProjection).map_mul x y

theorem embedding_injective : Function.Injective embedding := by
  intro x y h
  have hb := coordinates_injective (congrArg SemidirectProduct.left h)
  have ha := actor_injective (congrArg SemidirectProduct.right h)
  apply RegularWreathProduct.ext
  · funext i
    apply SemidirectProduct.ext
    · exact congrFun hb i
    · exact congrArg (fun a : Actor => a.left i) ha
  · exact congrArg (fun a : Actor => a.right) ha

noncomputable def wreathEquiv : PlaneWreath ≃* SymmetricFourWreath.P :=
  RegularWreathProduct.congr (Classical.choice plane_dihedral) (MulEquiv.refl _)

theorem card_model : Nat.card Model = 1920 := by
  rw [Nat.card_congr (SemidirectProduct.equivProd : Model ≃ V × Equiv.Perm (Fin 5)),Nat.card_prod]
  have hv : Nat.card V = 16 := by
    rw [← Nat.card_congr coreCoordinates.toEquiv]
    norm_num [Base,Plane,Bit,Nat.card_prod,Nat.card_zmod]
  rw [hv,Nat.card_eq_fintype_card,Fintype.card_perm]
  decide

/-- The coordinate wreath product has the full 2-part of the model order. -/
noncomputable def standardSylow : Sylow 2 Model := Sylow.ofCard embedding.range (by
  rw [← Nat.card_congr (MonoidHom.ofInjective embedding_injective).toEquiv,
    Nat.card_congr wreathEquiv.toEquiv,SymmetricFourWreath.card_P,card_model]
  rw [show 1920 = 2 ^ 7 * 15 by decide,
    Nat.factorization_mul (by decide) (by decide), Nat.factorization_pow]
  norm_num [Nat.prime_two.factorization,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 15)])

/-- Sylow conjugacy identifies every Sylow with the coordinate model. -/
noncomputable def sylowEquiv (S : Sylow 2 Model) : S ≃* SymmetricFourWreath.P :=
  (S.equiv standardSylow).trans ((MonoidHom.ofInjective embedding_injective).symm.trans wreathEquiv)

theorem sylow_equiv_wreath (S : Sylow 2 Model) : Nonempty (S ≃* SymmetricFourWreath.P) :=
  ⟨sylowEquiv S⟩


/-- Every Sylow in the product retains the literal second factor. -/
noncomputable def sylowProdEquiv {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup 2 D) (S : Sylow 2 (Model × D)) : S ≃* SymmetricFourWreath.P × D := by
  let f := MonoidHom.fst Model D
  let U := S.mapSurjective (f := f) (fun x => ⟨(x,1),rfl⟩)
  let ek : f.ker ≃* D := {
    toFun x := x.val.2
    invFun d := ⟨(1,d),rfl⟩
    left_inv x := by apply Subtype.ext; exact Prod.ext x.property.symm rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have hk : f.ker ≤ (S : Subgroup (Model × D)) :=
    (hD.of_equiv ek.symm).le_sylow_of_normal S
  let j : S →* U × D := {
    toFun s := (⟨s.val.1,mem_map_of_mem f s.property⟩,s.val.2)
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Bijective j := by
    constructor
    · intro x y he
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z : U × D => z.1.val) he) (congrArg (fun z : U × D => z.2) he)
    · rintro ⟨x,d⟩
      obtain ⟨y,hy,he⟩ := x.property
      have hd : (1,y.2⁻¹*d) ∈ (S : Subgroup (Model × D)) := hk rfl
      refine ⟨⟨y*(1,y.2⁻¹*d),S.mul_mem hy hd⟩,?_⟩
      apply Prod.ext
      · apply Subtype.ext
        change y.1 * 1 = x.val
        exact (mul_one _).trans he
      · change y.2*(y.2⁻¹*d)=d
        exact mul_inv_cancel_left _ _
  exact (MulEquiv.ofBijective j hj).trans (MulEquiv.prodCongr (sylowEquiv U) (MulEquiv.refl D))

@[simp] theorem sylowProdEquiv_snd {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup 2 D) (S : Sylow 2 (Model × D)) (s : S) :
    (sylowProdEquiv hD S s).2 = s.val.2 := rfl

/-- The first-coordinate kernel is exactly the original second direct factor. -/
theorem sylowProdEquiv_ker_fst {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup 2 D) (S : Sylow 2 (Model × D)) :
    ((MonoidHom.fst SymmetricFourWreath.P D).comp (sylowProdEquiv hD S).toMonoidHom).ker =
      ((⊥ : Subgroup Model).prod (⊤ : Subgroup D)).subgroupOf S := by
  ext s
  change sylowEquiv _ ⟨s.val.1,mem_map_of_mem (MonoidHom.fst Model D) s.property⟩ = 1 ↔
    s.val.1 = 1 ∧ True
  rw [map_eq_one_iff _ (MulEquiv.injective _)]
  simp only [Subtype.ext_iff,Subgroup.coe_one,and_true]

theorem sylow_prod_equiv_wreath {D : Type*} [Group D] [Finite D]
    (hD : IsPGroup 2 D) (S : Sylow 2 (Model × D)) :
    ∃ e : S ≃* SymmetricFourWreath.P × D,
      ((MonoidHom.fst SymmetricFourWreath.P D).comp e.toMonoidHom).ker =
        ((⊥ : Subgroup Model).prod (⊤ : Subgroup D)).subgroupOf S ∧
      ∀ s : S, (e s).2 = s.val.2 :=
  ⟨sylowProdEquiv hD S,sylowProdEquiv_ker_fst hD S,sylowProdEquiv_snd hD S⟩


end SylowModel
end BinaryPermutation.AlternatingFiveExtension
