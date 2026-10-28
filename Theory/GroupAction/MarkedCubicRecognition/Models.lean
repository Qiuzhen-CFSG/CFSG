module
public import Theory.GroupAction.MarkedCubicClassTwo.Defs
public import Theory.SpecificGroups.HeisenbergPrime.Recognition
public import Mathlib.GroupTheory.NoncommCoprod
public import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Ring

/-!
# Fixed marked cubic models

The Heisenberg multiplication has cross term `a*y`. Thus negating `b,c`
or `a,c` gives commuting involutory automorphisms. Their two cyclic
homomorphisms define the exact E₄ action and the fixed extraspecial
extension. The first marked cubic line is the b axis; the second is the
a axis. The elementary model carries the corresponding independent
inversions. Homomorphisms from the Heisenberg model are determined by
these two cubic generators.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.6.16, printed p.308 (1 March 2004 manuscript).
-/

@[expose] public section
namespace MarkedCubicRecognition

abbrev C2 := Multiplicative (ZMod 2)
abbrev C3 := Multiplicative (ZMod 3)
abbrev Four := C2 × C2
abbrev Nine := C3 × C3

def first : Four := (Multiplicative.ofAdd 1, 1)
def second : Four := (1, Multiplicative.ofAdd 1)

def cyclicHom {P : Type*} [Group P] {n : ℕ} [NeZero n]
    (x : P) (hx : x ^ n = 1) : Multiplicative (ZMod n) →* P where
  toFun z := x ^ z.toAdd.val
  map_one' := by simp
  map_mul' z w := by
    change x ^ (z.toAdd + w.toAdd).val = x ^ z.toAdd.val * x ^ w.toAdd.val
    rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

theorem cyclicHom_generator {P : Type*} [Group P] {n : ℕ} [NeZero n]
    (hn : 1 < n) (x : P) (hx : x ^ n = 1) :
    cyclicHom x hx (Multiplicative.ofAdd 1) = x := by
  change x ^ (1 : ZMod n).val = x
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hn, pow_one]

theorem cyclicHom_range {P : Type*} [Group P] {n : ℕ} [NeZero n]
    (hn : 1 < n) (x : P) (hx : x ^ n = 1) :
    (cyclicHom x hx).range = Subgroup.zpowers x := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) _
  · apply Subgroup.zpowers_le.mpr
    exact ⟨Multiplicative.ofAdd 1, cyclicHom_generator hn x hx⟩

def fourHom {P : Type*} [Group P] (x y : P)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : Commute x y) : Four →* P :=
  MonoidHom.noncommCoprod (cyclicHom x hx) (cyclicHom y hy)
    (fun _ _ => hxy.pow_pow _ _)

@[simp] theorem fourHom_first {P : Type*} [Group P] (x y : P)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : Commute x y) :
    fourHom x y hx hy hxy first = x := by simp [fourHom, first, cyclicHom, ZMod.val_one]

@[simp] theorem fourHom_second {P : Type*} [Group P] (x y : P)
    (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : Commute x y) :
    fourHom x y hx hy hxy second = y := by simp [fourHom, second, cyclicHom, ZMod.val_one]

/-- Fix the a coordinate and invert the b and central coordinates. -/
def leftFlip : MulAut (HeisenbergPrime 3) where
  toFun z := ⟨z.a, -z.b, -z.c⟩
  invFun z := ⟨z.a, -z.b, -z.c⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring

/-- Fix the b coordinate and invert the a and central coordinates. -/
def rightFlip : MulAut (HeisenbergPrime 3) where
  toFun z := ⟨-z.a, z.b, -z.c⟩
  invFun z := ⟨-z.a, z.b, -z.c⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp
  map_mul' z w := by ext <;> simp <;> ring

theorem leftFlip_sq : leftFlip ^ 2 = 1 := by
  ext z <;> simp [pow_two, leftFlip]

theorem rightFlip_sq : rightFlip ^ 2 = 1 := by
  ext z <;> simp [pow_two, rightFlip]

theorem flips_commute : Commute leftFlip rightFlip := by
  apply MulEquiv.ext
  intro z
  ext <;> simp [leftFlip, rightFlip]

/-- The prescribed E₄ action, with the first actor inverting the b axis. -/
def heisenbergAction : Four →* MulAut (HeisenbergPrime 3) :=
  fourHom leftFlip rightFlip leftFlip_sq rightFlip_sq flips_commute

@[simp] theorem heisenbergAction_first : heisenbergAction first = leftFlip :=
  fourHom_first ..

@[simp] theorem heisenbergAction_second : heisenbergAction second = rightFlip :=
  fourHom_second ..

/-- The fixed extraspecial extension appearing in F.6.16. -/
abbrev HeisenbergExtension := HeisenbergPrime 3 ⋊[heisenbergAction] Four

/-- The first marked cubic subgroup is the b coordinate line. -/
def leftAxis : C3 →* HeisenbergPrime 3 where
  toFun z := ⟨0, z.toAdd, 0⟩
  map_one' := rfl
  map_mul' z w := by ext <;> simp

/-- The second marked cubic subgroup is the a coordinate line. -/
def rightAxis : C3 →* HeisenbergPrime 3 where
  toFun z := ⟨z.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' z w := by ext <;> simp

def leftGenerator : HeisenbergPrime 3 := ⟨0, 1, 0⟩
def rightGenerator : HeisenbergPrime 3 := ⟨1, 0, 0⟩

theorem heisenberg_hom_ext {P : Type*} [Group P]
    (f g : HeisenbergPrime 3 →* P)
    (hx : f leftGenerator = g leftGenerator)
    (hy : f rightGenerator = g rightGenerator) : f = g := by
  have ht : f.eqLocus g = ⊤ :=
    HeisenbergPrime.subgroup_eq_top_of_noncommuting
      (HeisenbergPrime.card (p := 3)) (f.eqLocus g)
      ⟨leftGenerator, hx⟩ ⟨rightGenerator, hy⟩ (by
        intro he
        have hh := congrArg (fun z : f.eqLocus g => z.val.c) he
        norm_num [leftGenerator, rightGenerator] at hh)
  exact MonoidHom.ext fun z => show z ∈ f.eqLocus g from ht ▸ Subgroup.mem_top z

@[simp] theorem leftAxis_generator : leftAxis (Multiplicative.ofAdd 1) = leftGenerator := rfl
@[simp] theorem rightAxis_generator : rightAxis (Multiplicative.ofAdd 1) = rightGenerator := rfl

def nineLeftFlip : MulAut Nine :=
  MulEquiv.prodCongr (MulEquiv.inv C3) (MulEquiv.refl C3)

def nineRightFlip : MulAut Nine :=
  MulEquiv.prodCongr (MulEquiv.refl C3) (MulEquiv.inv C3)

theorem nineLeftFlip_sq : nineLeftFlip ^ 2 = 1 := by
  apply MulEquiv.ext
  intro z
  change (z.1⁻¹⁻¹, z.2) = z
  simp

theorem nineRightFlip_sq : nineRightFlip ^ 2 = 1 := by
  apply MulEquiv.ext
  intro z
  change (z.1, z.2⁻¹⁻¹) = z
  simp

theorem nineFlips_commute : Commute nineLeftFlip nineRightFlip := by
  apply MulEquiv.ext
  intro z
  rfl

def nineAction : Four →* MulAut Nine :=
  fourHom nineLeftFlip nineRightFlip nineLeftFlip_sq nineRightFlip_sq nineFlips_commute

abbrev NineExtension := Nine ⋊[nineAction] Four

end MarkedCubicRecognition
