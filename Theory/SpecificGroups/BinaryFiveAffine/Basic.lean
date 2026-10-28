module
public import Theory.Representation.BinaryPermutation
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
# The binary five-point affine model

We use the literal augmentation core of the binary permutation module and its
permutation action. The semidirect product retains the marked pair vector
`e₀+e₁`; its vector subgroup and the last-three coordinate subgroup provide
the source-facing coordinates for the involution centralizer calculation in
Aschbacher–Smith 13.9.10, printed p.973.
-/
@[expose] public section
namespace BinaryFiveAffine
open BinaryPermutation
abbrev V := Multiplicative (core (Fin 5))
abbrev S := Equiv.Perm (Fin 5)
instance coreDecidable : DecidablePred (· ∈ core (Fin 5)) := fun v =>
  inferInstanceAs (Decidable ((∑ i, v i) = 0))
instance vFintype : Fintype V := inferInstanceAs (Fintype (core (Fin 5)))

def action : S →* MulAut V where
  toFun g := {
    toFun v := Multiplicative.ofAdd (coreRepresentation (Fin 5) g v.toAdd)
    invFun v := Multiplicative.ofAdd (coreRepresentation (Fin 5) g⁻¹ v.toAdd)
    left_inv v := by apply Subtype.ext; funext i; simp
    right_inv v := by apply Subtype.ext; funext i; simp
    map_mul' v w := by apply Subtype.ext; funext i; rfl }
  map_one' := by ext v i; rfl
  map_mul' g h := by ext v i; rfl

@[simp] theorem action_apply (g : S) (v : V) (i : Fin 5) :
    (action g v).toAdd.val i = v.toAdd.val (g⁻¹ i) := rfl

abbrev W := V ⋊[action] S
instance wFintype : Fintype W := Fintype.ofEquiv (V × S) SemidirectProduct.equivProd.symm

def pair01 : V := Multiplicative.ofAdd
  ⟨((Pi.single (0 : Fin 5) (1 : ZMod 2) : Fin 5 → ZMod 2) + Pi.single (1 : Fin 5) 1), by decide +kernel⟩
@[simp] theorem pair01_apply (k : Fin 5) : pair01.toAdd.val k =
    (Pi.single (0 : Fin 5) (1 : ZMod 2) + Pi.single (1 : Fin 5) 1 : Fin 5 → ZMod 2) k := rfl

def t : W := SemidirectProduct.inl pair01
def vectorGroup : Subgroup W := (SemidirectProduct.inl : V →* W).range
@[simp] theorem mem_vectorGroup (w : W) : w ∈ vectorGroup ↔ w.right = 1 := by
  constructor
  · rintro ⟨v, rfl⟩; rfl
  · intro h
    exact ⟨w.left, SemidirectProduct.ext rfl h.symm⟩

def centralizer : Subgroup W := Subgroup.centralizer ({t} : Set W)

theorem mem_centralizer_iff (w : W) : w ∈ centralizer ↔ action w.right pair01 = pair01 := by
  change w ∈ Subgroup.centralizer ({t} : Set W) ↔ _
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hh
    have hl := congrArg SemidirectProduct.left hh
    change w.left * action w.right pair01 = pair01 * w.left at hl
    rw [mul_comm pair01] at hl
    exact mul_left_cancel hl
  · intro h
    apply SemidirectProduct.ext
    · simp [t, h, mul_comm]
    · simp [t]

theorem inl_mem_centralizer (v : V) : SemidirectProduct.inl v ∈ centralizer := by
  rw [mem_centralizer_iff]; simp

theorem t_mem_centralizer : t ∈ centralizer := inl_mem_centralizer _

def lastThree : Subgroup V := {
  carrier := {v | v.toAdd.val 0 = 0 ∧ v.toAdd.val 1 = 0}
  one_mem' := by simp
  mul_mem' := by intro a b ha hb; change (a.toAdd.val 0 = 0 ∧ a.toAdd.val 1 = 0) at ha; change (b.toAdd.val 0 = 0 ∧ b.toAdd.val 1 = 0) at hb; change ((a*b).toAdd.val 0 = 0 ∧ (a*b).toAdd.val 1 = 0); simp [Pi.add_apply, ha.1,ha.2,hb.1,hb.2]
  inv_mem' := by intro a ha; change (a.toAdd.val 0 = 0 ∧ a.toAdd.val 1 = 0) at ha; change ((a⁻¹).toAdd.val 0 = 0 ∧ (a⁻¹).toAdd.val 1 = 0); simp [ha.1,ha.2] }

def weight (v : V) : ℕ := (Finset.univ.filter fun i => v.toAdd.val i ≠ 0).card

theorem lastThree_weight (v : V) (hv : v ∈ lastThree) (hne : v ≠ 1) : weight v = 2 := by
  change v.toAdd.val 0 = 0 ∧ v.toAdd.val 1 = 0 at hv
  have h : ∀ a : Fin 5 → ZMod 2, (∑ i, a i) = 0 → a 0 = 0 → a 1 = 0 →
      a ≠ 0 → (Finset.univ.filter fun i => a i ≠ 0).card = 2 := by decide +kernel
  exact h v.toAdd.val v.toAdd.property hv.1 hv.2 (fun hh => hne (Subtype.ext hh))

end BinaryFiveAffine
