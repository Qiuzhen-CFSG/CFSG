module
public import Theory.GroupAction.RegularWreathFunctionModule
public import Theory.Representation.FourGroupMatrixCoordinates
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic.Model
public import Mathlib.GroupTheory.PGroup

/-!
# The second plane of a binary wreath point stabilizer

For the natural action of SL₂(2) wr C₂, the stabilizer of a nonzero vector
supported on one plane preserves both planes. Its action on the other plane
is onto SL₂(2), with two-group kernel, and the literal second direct factor
has relative index two. The proofs use the actual coordinate action; only
the six-element plane fixer is checked by finite kernel reduction.

Source application: Aschbacher--Smith, 14.6.17, printed pp.1035--1036.
-/

@[expose] public section
namespace BinaryWreathPointStabilizer
open Subgroup
abbrev Plane := Multiplicative (Fin 2 → ZMod 2)
abbrev Index := Multiplicative (ZMod 2)
abbrev MatrixActor := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
abbrev Actor := RegularWreathProduct MatrixActor Index
abbrev Vector := Index → Plane
attribute [local instance] FourGroupMatrixCoordinates.naturalAction
local instance : MulDistribMulAction Actor Vector :=
  RegularWreathProduct.functionModule _ _ _

def Supported (i : Index) (v : Vector) : Prop := ∀ j, j ≠ i → v j = 1

theorem value_ne_one {i : Index} {v : Vector} (hv : Supported i v) (hne : v ≠ 1) :
    v i ≠ 1 := by
  intro he
  apply hne
  funext j
  by_cases hj : j = i
  · simpa [hj] using he
  · exact hv j hj

theorem fixed_no_shift {i : Index} {v : Vector} (hv : Supported i v) (hne : v ≠ 1)
    (a : Actor) (ha : a • v = v) : a.right = 1 := by
  by_contra hn
  have hi : a.right⁻¹ * i ≠ i := by
    intro he
    exact hn (inv_eq_one.mp (mul_right_cancel (he.trans (one_mul i).symm)))
  have he := congrFun ha i
  change a.left i • v (a.right⁻¹ * i) = v i at he
  rw [hv _ hi, smul_one] at he
  exact value_ne_one hv hne he.symm

/-- The action of the full point stabilizer on the other coordinate plane. -/
def secondActor {i : Index} {v : Vector} (hv : Supported i v) (hne : v ≠ 1)
    (j : Index) : MulAction.stabilizer Actor v →* MatrixActor where
  toFun a := a.val.left j
  map_one' := rfl
  map_mul' a b := by
    change a.val.left j * b.val.left (a.val.right⁻¹ * j) = a.val.left j * b.val.left j
    rw [fixed_no_shift hv hne a.val a.property, inv_one, one_mul]

theorem secondActor_surjective {i : Index} {v : Vector} (hv : Supported i v)
    (hne : v ≠ 1) {j : Index} (hji : j ≠ i) :
    Function.Surjective (secondActor hv hne j) := by
  intro b
  let a : Actor := ⟨fun k => if k = j then b else 1, 1⟩
  have ha : a • v = v := by
    funext k
    change (if k = j then b else 1) • v (1⁻¹ * k) = v k
    simp only [inv_one, one_mul]
    by_cases hk : k = j
    · subst k
      rw [if_pos rfl, hv j hji, smul_one]
    · rw [if_neg hk, one_smul]
  exact ⟨⟨a,ha⟩, if_pos rfl⟩

private theorem plane_fixer_square : ∀ (a : MatrixActor) (v : Plane),
    v ≠ 1 → a • v = v → a ^ 2 = 1 := by decide +kernel

/-- Only an involution on the first plane remains in the second action's kernel. -/
theorem secondActor_kernel {i : Index} {v : Vector} (hv : Supported i v)
    (hne : v ≠ 1) {j : Index} (hji : j ≠ i) :
    IsPGroup 2 (secondActor hv hne j).ker := by
  intro a
  refine ⟨1, ?_⟩
  simp only [pow_one, pow_two]
  apply Subtype.ext
  apply Subtype.ext
  apply RegularWreathProduct.ext
  · funext k
    have hs := fixed_no_shift hv hne a.val.val a.val.property
    change a.val.val.left k * a.val.val.left (a.val.val.right⁻¹ * k) = 1
    rw [hs, inv_one, one_mul]
    have hk : k = i ∨ k = j := by
      have hh : ∀ i j k : Index, j ≠ i → k = i ∨ k = j := by decide
      exact hh i j k hji
    rcases hk with hk | hk
    · subst k
      have he := congrFun a.val.property i
      change a.val.val.left i • v (a.val.val.right⁻¹ * i) = v i at he
      rw [hs, inv_one, one_mul] at he
      simpa only [pow_two] using plane_fixer_square _ _ (value_ne_one hv hne) he
    · subst k
      have he : a.val.val.left j = 1 := a.property
      rw [he, one_mul]
  · change a.val.val.right * a.val.val.right = 1
    rw [fixed_no_shift hv hne a.val.val a.val.property, one_mul]

/-- The second direct factor, as a literal subgroup of the wreath product. -/
def secondFactor (i : Index) : Subgroup Actor where
  carrier a := a.right = 1 ∧ a.left i = 1
  one_mem' := ⟨rfl,rfl⟩
  mul_mem' := by
    rintro a b ⟨ha,ha'⟩ ⟨hb,hb'⟩
    constructor
    · change a.right * b.right = 1
      rw [ha,hb,one_mul]
    · change a.left i * b.left (a.right⁻¹ * i) = 1
      rw [ha,inv_one,one_mul,ha',hb',one_mul]
  inv_mem' := by
    rintro a ⟨ha,ha'⟩
    constructor
    · change a.right⁻¹ = 1
      rw [ha,inv_one]
    · change (a.left (a.right * i))⁻¹ = 1
      rw [ha,one_mul,ha',inv_one]

theorem secondFactor_le_stabilizer {i : Index} {v : Vector} (hv : Supported i v) :
    secondFactor i ≤ MulAction.stabilizer Actor v := by
  intro a ha
  change a • v = v
  funext k
  change a.left k • v (a.right⁻¹ * k) = v k
  rw [ha.1,inv_one,one_mul]
  by_cases hk : k = i
  · subst k
    rw [ha.2,one_smul]
  · rw [hv k hk,smul_one]

private theorem plane_fixer_card : ∀ v : Plane, v ≠ 1 →
    Fintype.card (MulAction.stabilizer MatrixActor v) = 2 := by decide +kernel

/-- Projection onto the first point fixer detects the index-two factor. -/
theorem secondFactor_relIndex {i : Index} {v : Vector} (hv : Supported i v)
    (hne : v ≠ 1) :
    (secondFactor i).relIndex (MulAction.stabilizer Actor v) = 2 := by
  let f : MulAction.stabilizer Actor v →* MulAction.stabilizer MatrixActor (v i) :=
    (secondActor hv hne i).codRestrict _ (fun a => by
      have he := congrFun a.property i
      change a.val.left i • v (a.val.right⁻¹ * i) = v i at he
      rwa [fixed_no_shift hv hne a.val a.property,inv_one,one_mul] at he)
  have hf : Function.Surjective f := by
    intro b
    let a : Actor := ⟨fun k => if k = i then b.val else 1,1⟩
    have ha : a • v = v := by
      funext k
      change (if k = i then b.val else 1) • v (1⁻¹ * k) = v k
      simp only [inv_one,one_mul]
      by_cases hk : k = i
      · subst k
        rw [if_pos rfl]
        exact b.property
      · rw [if_neg hk,one_smul]
    exact ⟨⟨a,ha⟩,Subtype.ext (if_pos rfl)⟩
  have he : f.ker = (secondFactor i).subgroupOf (MulAction.stabilizer Actor v) := by
    ext a
    change f a = 1 ↔ a.val.right = 1 ∧ a.val.left i = 1
    rw [and_iff_right (fixed_no_shift hv hne a.val a.property)]
    exact Subtype.ext_iff
  change ((secondFactor i).subgroupOf (MulAction.stabilizer Actor v)).index = 2
  rw [← he,index_ker,MonoidHom.range_eq_top.mpr hf,card_top,Nat.card_eq_fintype_card]
  exact plane_fixer_card (v i) (value_ne_one hv hne)

end BinaryWreathPointStabilizer
