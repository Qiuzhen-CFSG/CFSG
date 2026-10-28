module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.Models
public import Theory.SpecificGroups.PSL3Two.Cardinality
public import Theory.GroupTheory.PrimeRankCubeFree
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# The factor-swap extension of the binary three-by-three tensor action

The literal whole-group conclusion in G.9.3(14) requires an additional
exclusion: the tensor action extends faithfully to the factor-swap
semidirect product. This module constructs that extension on the exact
`threeTensor` space, identifies its proper normal base equivariantly, and
proves that its order is 56448 and every odd-prime rank is at most two.
Consequently its action cannot be quasiequivalent to `threeTensor` as an
action of the entire extension.

The proofs use binary pure-tensor rigidity for faithfulness, the explicit
flip for equivariance, and the absence of odd prime cubes in the order for
the rank bound. They do not claim a complete Lean counterexample to
`ComponentHypothesis`: the component, actor and irreducibility checks are
also recorded independently by the reproducible GAP diagnostic in
`SwapExtension/source/check.g`. That diagnostic is not a proof dependency.

Source: Aschbacher--Smith, combined manuscript, G.9.1 and G.9.3,
printed pp.351,353--354,356 (PDF pp.362,364--365,367).
-/

@[expose] public noncomputable section
open scoped TensorProduct
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.SwapExtension

abbrev Space := ThreeSpace ⊗[ZMod 2] ThreeSpace
abbrev Pair := ThreeGroup × ThreeGroup
abbrev Two := Multiplicative (ZMod 2)

private theorem cases_two (c : Two) : c = 1 ∨ c = Multiplicative.ofAdd (1 : ZMod 2) := by
  change c.toAdd = 0 ∨ c.toAdd = 1
  exact (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) c.toAdd

def factorSwap : Two →* MulAut Pair where
  toFun c := if c = 1 then 1 else MulEquiv.prodComm
  map_one' := rfl
  map_mul' a b := by
    rcases cases_two a with rfl | rfl <;> rcases cases_two b with rfl | rfl <;>
      ext x <;> simp [show Multiplicative.ofAdd (1 : ZMod 2) *
        Multiplicative.ofAdd 1 = (1 : Two) by decide]

@[simp] theorem factorSwap_apply (c : Two) :
    factorSwap c = if c = 1 then 1 else MulEquiv.prodComm := rfl

abbrev Group := Pair ⋊[factorSwap] Two

instance : Finite Group := Finite.of_equiv (Pair × Two) SemidirectProduct.equivProd.symm

def tensorLinear : Pair →* (Space ≃ₗ[ZMod 2] Space) where
  toFun g := TensorProduct.congr
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) g.1)
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) g.2)
  map_one' := by apply LinearEquiv.toLinearMap_injective; ext x y; simp
  map_mul' g h := by apply LinearEquiv.toLinearMap_injective; ext x y; simp

@[simp] theorem tensorLinear_apply (g : Pair) (v : Space) :
    tensorLinear g v = threeTensor g v := rfl

def flip : Space ≃ₗ[ZMod 2] Space := TensorProduct.comm _ _ _

@[simp] theorem flip_tmul (x y : ThreeSpace) :
    flip (x ⊗ₜ[ZMod 2] y) = y ⊗ₜ[ZMod 2] x := rfl

theorem flip_mul_self : flip * flip = 1 := by apply LinearEquiv.toLinearMap_injective; ext x y; rfl

@[simp] theorem flip_inv : flip⁻¹ = flip := by
  exact inv_eq_of_mul_eq_one_right flip_mul_self

def flipAction : Two →* (Space ≃ₗ[ZMod 2] Space) where
  toFun c := if c = 1 then 1 else flip
  map_one' := rfl
  map_mul' a b := by
    rcases cases_two a with rfl | rfl <;> rcases cases_two b with rfl | rfl <;>
      simp [show Multiplicative.ofAdd (1 : ZMod 2) *
        Multiplicative.ofAdd 1 = (1 : Two) by decide, flip_mul_self]

@[simp] theorem flipAction_apply (c : Two) :
    flipAction c = if c = 1 then 1 else flip := rfl

private theorem compatible (c : Two) :
    tensorLinear.comp (factorSwap c).toMonoidHom =
      (MulAut.conj (flipAction c)).toMonoidHom.comp tensorLinear := by
  rcases cases_two c with rfl | rfl
  · apply MonoidHom.ext
    intro g
    change tensorLinear g = 1 * tensorLinear g * (1 : Space ≃ₗ[ZMod 2] Space)⁻¹
    simp
  · apply MonoidHom.ext
    intro g
    apply LinearEquiv.toLinearMap_injective
    ext x y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, factorSwap_apply,
      flipAction_apply, show Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : Two) by decide,
      if_false, MulAut.conj_apply, flip_inv]
    rfl

def linearAction : Group →* (Space ≃ₗ[ZMod 2] Space) :=
  SemidirectProduct.lift tensorLinear flipAction (by exact compatible)

def action : Representation (ZMod 2) Group Space where
  toFun g := (linearAction g).toLinearMap
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

@[simp] theorem action_base (g : Pair) (v : Space) :
    action (SemidirectProduct.inl g) v = threeTensor g v := rfl

@[simp] theorem action_swap (v : Space) :
    action (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) v = flip v := by
  change (tensorLinear 1 * flipAction (Multiplicative.ofAdd (1 : ZMod 2))) v = _
  simp only [map_one, flipAction_apply,
    show Multiplicative.ofAdd (1 : ZMod 2) ≠ (1 : Two) by decide, if_false, one_mul]


private def coordinate (i j : Fin 3) : Space →ₗ[ZMod 2] ZMod 2 :=
  (TensorProduct.lid (ZMod 2) (ZMod 2)).toLinearMap.comp
    (TensorProduct.map (LinearMap.proj i) (LinearMap.proj j))

private theorem binary_eq_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  exact (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) a ha

private theorem pure_eq {x y x' y' : ThreeSpace} (hx : x ≠ 0) (hy : y ≠ 0)
    (he : x ⊗ₜ[ZMod 2] y = x' ⊗ₜ[ZMod 2] y') : x = x' ∧ y = y' := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := not_forall.mp (fun hh => hx (funext hh))
  obtain ⟨j, hj⟩ : ∃ j, y j ≠ 0 := not_forall.mp (fun hh => hy (funext hh))
  have hi := binary_eq_one hi
  have hj := binary_eq_one hj
  have hij := congrArg (coordinate i j) he
  change x i * y j = x' i * y' j at hij
  rw [hi, hj, one_mul] at hij
  have hi' : x' i = 1 := binary_eq_one (by
    intro hz
    rw [hz, zero_mul] at hij
    exact one_ne_zero hij)
  have hj' : y' j = 1 := binary_eq_one (by
    intro hz
    rw [hz, mul_zero] at hij
    exact one_ne_zero hij)
  constructor
  · funext a
    have hh := congrArg (coordinate a j) he
    change x a * y j = x' a * y' j at hh
    simpa [hj, hj'] using hh
  · funext b
    have hh := congrArg (coordinate i b) he
    change x i * y b = x' i * y' b at hh
    simpa [hi, hi'] using hh

private def e (i : Fin 3) : ThreeSpace := Pi.single i 1

private theorem e_ne_zero (i : Fin 3) : e i ≠ 0 := by
  intro h
  have he := congrFun h i
  simp [e] at he

private theorem equiv_ne_zero (f : ThreeSpace ≃ₗ[ZMod 2] ThreeSpace)
    {x : ThreeSpace} (hx : x ≠ 0) : f x ≠ 0 := by
  intro he
  exact hx (f.injective (he.trans f.map_zero.symm))

theorem tensorLinear_injective : Function.Injective tensorLinear := by
  intro a b hab
  apply Prod.ext
  · apply BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) |>.injective
    apply LinearEquiv.ext
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have he := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f (x ⊗ₜ[ZMod 2] e 0)) hab
      exact (pure_eq
        (equiv_ne_zero (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) a.1) hx)
        (equiv_ne_zero (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) a.2)
          (e_ne_zero 0)) he).1
  · apply BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) |>.injective
    apply LinearEquiv.ext
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · have he := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f (e 0 ⊗ₜ[ZMod 2] y)) hab
      exact (pure_eq
        (equiv_ne_zero (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) a.1)
          (e_ne_zero 0))
        (equiv_ne_zero (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide) a.2) hy) he).2

/-- The flip is an additional linear operator, not an element of the tensor image. -/
theorem flip_not_tensor (g : Pair) : tensorLinear g ≠ flip := by
  intro hh
  have h00 := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f (e 0 ⊗ₜ[ZMod 2] e 0)) hh
  have h10 := congrArg (fun f : Space ≃ₗ[ZMod 2] Space => f (e 1 ⊗ₜ[ZMod 2] e 0)) hh
  have h0 := (pure_eq (e_ne_zero 0) (e_ne_zero 0) h00.symm).2
  have h1 := (pure_eq (e_ne_zero 0) (e_ne_zero 1) h10.symm).2
  have he : e 0 = e 1 := h0.trans h1.symm
  have hc := congrFun he 0
  simp [e] at hc

/-- The tensor action extends faithfully across the factor swap. -/
theorem linearAction_injective : Function.Injective linearAction := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  change g = 1
  have he : tensorLinear g.left * flipAction g.right = 1 := hg
  by_cases hc : g.right = 1
  · have hg0 : g.right = 1 := hc
    have hleft : g.left = 1 := tensorLinear_injective (by
      simpa only [flipAction_apply, if_pos hc, mul_one, map_one] using he)
    exact SemidirectProduct.ext hleft hg0
  · have ht : tensorLinear g.left = flip := by
      have he' : tensorLinear g.left * flip = 1 := by simpa only [flipAction_apply, if_neg hc] using he
      exact (eq_inv_of_mul_eq_one_left he').trans flip_inv
    exact (flip_not_tensor g.left ht).elim

theorem action_faithful : Function.Injective action := by
  intro a b hab
  apply linearAction_injective
  exact LinearEquiv.toLinearMap_injective hab


/-- The actual base subgroup of the extension. -/
def base : Subgroup Group := (SemidirectProduct.inl : Pair →* Group).range

/-- The base is normal, being the kernel of the projection to the swap group. -/
instance base_normal : base.Normal := by
  change (SemidirectProduct.inl : Pair →* Group).range.Normal
  rw [SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

def baseEquiv : Pair ≃* base := MonoidHom.ofInjective SemidirectProduct.inl_injective

theorem base_proper : base ≠ ⊤ := by
  intro he
  have hm : SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) ∈ base :=
    he ▸ Subgroup.mem_top _
  obtain ⟨g, hg⟩ := hm
  have hc := congrArg SemidirectProduct.right hg
  change (1 : Two) = Multiplicative.ofAdd (1 : ZMod 2) at hc
  exact (by decide : (1 : Two) ≠ Multiplicative.ofAdd (1 : ZMod 2)) hc

/-- On the proper normal base, the action is exactly the prescribed tensor model. -/
theorem base_quasiequivalent : Quasiequivalent (action.comp base.subtype) threeTensor := by
  refine ⟨baseEquiv.symm, LinearEquiv.refl _ _, ?_⟩
  intro g v
  obtain ⟨x, rfl⟩ := baseEquiv.surjective g
  change action (SemidirectProduct.inl x) v = threeTensor (baseEquiv.symm (baseEquiv x)) v
  rw [MulEquiv.symm_apply_apply]
  rfl

/-- The advertised model's binary degree survives the extension. -/
theorem degree : Module.finrank (ZMod 2) Space = 9 := threeTensor_degree

theorem three_card : Nat.card ThreeGroup = 168 := by
  rw [Nat.card_congr (BinaryLinear.OuterCyclic.projectiveEquivSL (n := 3) (by decide)).toEquiv]
  exact Matrix.PSL3Two.card_SL

theorem group_card : Nat.card Group = 56448 := by
  rw [SemidirectProduct.card, Nat.card_prod, three_card]
  have hc : Nat.card Two = 2 := by
    change Nat.card (ZMod 2) = 2
    simpa only [Nat.card_eq_fintype_card] using ZMod.card 2
  rw [hc]

/-- A numerical order obstruction to identifying this extension with its base. -/
theorem not_equiv_pair : IsEmpty (Group ≃* Pair) := by
  refine ⟨fun e => ?_⟩
  have he := Nat.card_congr e.toEquiv
  rw [group_card, Nat.card_prod, three_card] at he
  norm_num at he

/-- The order already bounds every odd-prime rank by two. -/
theorem stronglyQuasithin : IsStronglyQuasithin Group := by
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  apply primeRank_le_two_of_cube_not_dvd
  rw [group_card]
  intro hc
  have hd : p ∣ 2 ^ 7 * 3 ^ 2 * 7 ^ 2 := by
    have hh : p ∣ p ^ 3 := dvd_pow_self p (by decide)
    exact (hh.trans hc).trans (by norm_num)
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · have he : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
      subst p
      norm_num at ho
    · have he : p = 3 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd)
      subst p
      norm_num at hc
  · have he : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp (hp.dvd_of_dvd_pow hd)
    subst p
    norm_num at hc

theorem not_quasiequivalent : ¬ Quasiequivalent action threeTensor := by
  rintro ⟨e, _, _⟩
  exact not_equiv_pair.false e

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.NaturalRecognition.SwapExtension
