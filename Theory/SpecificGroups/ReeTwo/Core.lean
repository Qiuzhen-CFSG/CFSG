module

public import Theory.SpecificGroups.ReeTwo.CoreOrder
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Group.MinimalAxioms

/-!
# Binary coordinates for the Ree two centralizer core

The ordered coordinates correspond to roots 3 through 12 in Shinoda (1975),
(2.3), pp. 81–82. Multiplication collects the second word into the first;
all commutator corrections lie in the last five coordinates. The final
coordinate includes the cubic corrections from collecting those corrections.
The group laws below are polynomial identities over the field with two elements.
The ordered root powers reconstruct each coordinate tuple. This proves the
presentation map is onto; the independent order bound in `CoreOrder` then
proves it is an isomorphism. Its inverse supplies the universal homomorphism
from this concrete core to any roots satisfying the defining relations.
-/

@[expose] public section
namespace ReeTwo

/-- Ten binary coordinates, in increasing root order. -/
@[ext] structure Core where
  b0 : ZMod 2
  b1 : ZMod 2
  b2 : ZMod 2
  b3 : ZMod 2
  b4 : ZMod 2
  b5 : ZMod 2
  b6 : ZMod 2
  b7 : ZMod 2
  b8 : ZMod 2
  b9 : ZMod 2
  deriving DecidableEq

namespace Core

/-- Collected multiplication in increasing root order. -/
def mul (x y : Core) : Core where
  b0 := x.b0 + y.b0
  b1 := x.b1 + y.b1
  b2 := x.b2 + y.b2
  b3 := x.b3 + y.b3
  b4 := x.b4 + y.b4
  b5 := x.b5 + (x.b2 * y.b0) + (x.b3 * y.b0) + (x.b1 * y.b1) + y.b5
  b6 := x.b6 + (x.b3 * y.b0) + (x.b4 * y.b0) + (x.b2 * y.b1) + y.b6
  b7 := x.b7 + (x.b4 * y.b0) + (x.b4 * y.b1) + (x.b3 * y.b2) + y.b7
  b8 := x.b8 + (x.b4 * y.b1) + (x.b4 * y.b2) + (x.b3 * y.b3) + y.b8
  b9 := x.b9 + x.b3 * y.b0 + x.b2 * x.b4 * y.b0 + x.b3 * x.b4 * y.b0 +
    x.b8 * y.b0 + x.b2 * x.b3 * y.b1 + x.b4 * y.b1 + x.b1 * x.b4 * y.b1 +
    x.b7 * y.b1 + x.b4 * y.b0 * y.b1 + x.b2 * y.b2 + x.b6 * y.b3 +
    x.b3 * y.b0 * y.b3 + x.b4 * y.b0 * y.b3 + x.b2 * y.b1 * y.b3 +
    x.b5 * y.b4 + x.b2 * y.b0 * y.b4 + x.b3 * y.b0 * y.b4 +
    x.b1 * y.b1 * y.b4 + y.b9

instance : Mul Core := ⟨mul⟩
instance : One Core := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

theorem mul_assoc (x y z : Core) : (x * y) * z = x * (y * z) := by
  change mul (mul x y) z = mul x (mul y z)
  apply Core.ext <;> simp only [mul] <;> ring_nf
  all_goals reduce_mod_char

theorem one_mul (x : Core) : 1 * x = x := by
  change mul ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩ x = x
  apply Core.ext <;> simp [mul]

instance : Inv Core := ⟨fun x => (x * x) * x⟩

theorem inv_mul_cancel (x : Core) : x⁻¹ * x = 1 := by
  change mul (mul (mul x x) x) x = ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  apply Core.ext <;> simp only [mul]
  all_goals ring_nf
  all_goals reduce_mod_char

instance : Group Core := Group.ofLeftAxioms mul_assoc one_mul inv_mul_cancel

/-- Read the ten coordinates as a function on the root indices. -/
def coords (x : Core) : CoreRoot → ZMod 2 :=
  ![x.b0, x.b1, x.b2, x.b3, x.b4, x.b5, x.b6, x.b7, x.b8, x.b9]

/-- Form a core element from its ten coordinates. -/
def ofCoords (v : CoreRoot → ZMod 2) : Core :=
  ⟨v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9⟩

/-- The coordinates are independent binary parameters. -/
def coordinateEquiv : Core ≃ (CoreRoot → ZMod 2) where
  toFun := coords
  invFun := ofCoords
  left_inv _ := rfl
  right_inv v := by funext i; fin_cases i <;> rfl

@[simp] theorem coords_ofCoords (v : CoreRoot → ZMod 2) : coords (ofCoords v) = v :=
  coordinateEquiv.apply_symm_apply v

@[simp] theorem ofCoords_coords (x : Core) : ofCoords (coords x) = x := rfl

instance : Fintype Core := Fintype.ofEquiv _ coordinateEquiv.symm

@[simp] theorem card : Nat.card Core = 1024 := by
  rw [Nat.card_congr coordinateEquiv, Nat.card_fun, Nat.card_zmod]
  simp [CoreRoot]

/-- The canonical element of root `i + 3`. -/
def root (i : CoreRoot) : Core := ofCoords (fun j => if j = i then 1 else 0)

set_option maxRecDepth 4096 in
/-- The coordinates satisfy all squares and right commutators of the presentation. -/
theorem relations : CoreRelations root where
  square := by decide
  commutator := by decide

/-- A root with arbitrary binary parameter occupies just that coordinate. -/
theorem root_pow (i : CoreRoot) (t : ZMod 2) :
    root i ^ t.val = ofCoords (fun j => if j = i then t else 0) := by
  exact (by decide : ∀ (i : CoreRoot) (t : ZMod 2),
    root i ^ t.val = ofCoords (fun j => if j = i then t else 0)) i t

/-- The increasing product of the ten root powers is the coordinate normal form. -/
theorem normal_form (x : Core) :
    root 0 ^ x.b0.val * root 1 ^ x.b1.val * root 2 ^ x.b2.val *
      root 3 ^ x.b3.val * root 4 ^ x.b4.val * root 5 ^ x.b5.val *
      root 6 ^ x.b6.val * root 7 ^ x.b7.val * root 8 ^ x.b8.val *
      root 9 ^ x.b9.val = x := by
  simp only [root_pow]
  change mul (mul (mul (mul (mul (mul (mul (mul (mul (_) _) _) _) _) _) _) _) _) _ = x
  apply Core.ext <;> simp [mul, ofCoords]

/-- An ordered binary word in any ten chosen roots. -/
def normalWord {H : Type*} [Group H] (x : CoreRoot → H) (v : CoreRoot → ZMod 2) : H :=
  x 0 ^ (v 0).val * x 1 ^ (v 1).val * x 2 ^ (v 2).val * x 3 ^ (v 3).val *
    x 4 ^ (v 4).val * x 5 ^ (v 5).val * x 6 ^ (v 6).val * x 7 ^ (v 7).val *
    x 8 ^ (v 8).val * x 9 ^ (v 9).val

@[simp] theorem map_normalWord {H K : Type*} [Group H] [Group K]
    (f : H →* K) (x : CoreRoot → H) (v : CoreRoot → ZMod 2) :
    f (normalWord x v) = normalWord (fun i => f (x i)) v := by
  simp only [normalWord, map_mul, map_pow]

@[simp] theorem normalWord_root (v : CoreRoot → ZMod 2) : normalWord root v = ofCoords v :=
  normal_form (ofCoords v)

/-- Every element has exactly one ordered binary root word. -/
theorem normal_form_unique (x : Core) : ∃! v, normalWord root v = x := by
  refine ⟨coords x, by simp, ?_⟩
  intro v hv
  simpa using congrArg coords hv

/-- The homomorphism from the presentation into the finite coordinate model. -/
def fromPresentation : PresentedCore →* Core := corePresentationHom relations

@[simp] theorem fromPresentation_root (i : CoreRoot) :
    fromPresentation (presentedRoot i) = root i := corePresentationHom_root relations i

/-- Every coordinate tuple is the image of its ordered word in the presentation. -/
theorem fromPresentation_surjective : Function.Surjective fromPresentation := by
  intro x
  refine ⟨presentedRoot 0 ^ x.b0.val * presentedRoot 1 ^ x.b1.val *
    presentedRoot 2 ^ x.b2.val * presentedRoot 3 ^ x.b3.val *
    presentedRoot 4 ^ x.b4.val * presentedRoot 5 ^ x.b5.val *
    presentedRoot 6 ^ x.b6.val * presentedRoot 7 ^ x.b7.val *
    presentedRoot 8 ^ x.b8.val * presentedRoot 9 ^ x.b9.val, ?_⟩
  simpa only [map_mul, map_pow, fromPresentation_root] using normal_form x

/-- Surjectivity and the independently proved presentation bound give injectivity. -/
theorem fromPresentation_bijective : Function.Bijective fromPresentation :=
  fromPresentation_surjective.bijective_of_nat_card_le
    (by simpa only [card] using presentedCore_finite_card.2)

/-- The finite coordinate group realizes precisely the given presentation. -/
noncomputable def presentationEquiv : PresentedCore ≃* Core :=
  MulEquiv.ofBijective fromPresentation fromPresentation_bijective

@[simp] theorem presentationEquiv_root (i : CoreRoot) :
    presentationEquiv (presentedRoot i) = root i := fromPresentation_root i

@[simp] theorem presentationEquiv_symm_root (i : CoreRoot) :
    presentationEquiv.symm (root i) = presentedRoot i := by
  rw [← presentationEquiv_root, presentationEquiv.symm_apply_apply]

/-- The presentation has the same unique ordered binary normal forms. -/
theorem presented_normal_form_unique (p : PresentedCore) :
    ∃! v, normalWord presentedRoot v = p := by
  have hm (v : CoreRoot → ZMod 2) :
      presentationEquiv (normalWord presentedRoot v) = ofCoords v := by
    change presentationEquiv.toMonoidHom (normalWord presentedRoot v) = _
    simp
  refine ⟨coords (presentationEquiv p), ?_, ?_⟩
  · apply presentationEquiv.injective
    rw [hm, ofCoords_coords]
  · intro v hv
    have he := congrArg presentationEquiv hv
    rw [hm] at he
    simpa using congrArg coords he

/-- The unique homomorphism taking canonical roots to any roots with these relations. -/
noncomputable def lift {H : Type*} [Group H] {x : CoreRoot → H}
    (h : CoreRelations x) : Core →* H :=
  (corePresentationHom h).comp presentationEquiv.symm.toMonoidHom

@[simp] theorem lift_root {H : Type*} [Group H] {x : CoreRoot → H}
    (h : CoreRelations x) (i : CoreRoot) : lift h (root i) = x i := by
  simp [lift]

/-- Evaluation of the universal homomorphism is the ordered root word. -/
theorem lift_apply {H : Type*} [Group H] {x : CoreRoot → H}
    (h : CoreRelations x) (g : Core) : lift h g = normalWord x (coords g) := by
  have he := congrArg (lift h) (normalWord_root (coords g))
  simpa only [map_normalWord, lift_root, ofCoords_coords] using he.symm

/-- The ten canonical roots determine homomorphisms from the coordinate core. -/
@[ext] theorem hom_ext {H : Type*} [Group H] {f g : Core →* H}
    (h : ∀ i, f (root i) = g (root i)) : f = g := by
  have he : f.comp fromPresentation = g.comp fromPresentation :=
    corePresentationHom_ext (fun i => by simpa using h i)
  ext x
  obtain ⟨p, rfl⟩ := fromPresentation_surjective x
  exact DFunLike.congr_fun he p

/-- The universal homomorphism is unique, with no generation assumption on the target. -/
theorem lift_unique {H : Type*} [Group H] {x : CoreRoot → H}
    (h : CoreRelations x) (f : Core →* H) (hf : ∀ i, f (root i) = x i) : f = lift h := by
  apply hom_ext
  intro i
  rw [hf, lift_root]

end Core

@[simp] theorem presentedCore_card : Nat.card PresentedCore = 1024 :=
  (Nat.card_congr Core.presentationEquiv.toEquiv).trans Core.card

end ReeTwo
