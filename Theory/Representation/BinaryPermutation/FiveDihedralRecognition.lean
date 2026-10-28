module
public import Theory.Representation.BinaryPermutation
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.NoncommCoprod
public import Theory.ElementaryAbelian.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Two dihedral factors from the binary five-point core

Let the image of a group on its marked binary five-point core be generated
by the disjoint transpositions (0 1) and (2 3). Suppose the action kernel is
the product of that core with a disjoint central subgroup, and an elementary
abelian two-subgroup supplements the kernel. Then the group is the direct
product of the central subgroup and two dihedral groups of order eight.

The supplement supplies commuting involution lifts of the transpositions.
The first four core coordinates are independent and form two swapped planes;
each plane with its lift has the dihedral presentation. The resulting map
is injective by the action kernel and disjointness, and surjective by the
prescribed image and kernel. No abstract splitting or recognition premise
is used.

Source: Aschbacher–Smith, Quasithin Groups, Lemma 5.1.7(1), printed p.633,
the decomposition S = Q_C × D_1 × D_2 after S = QQ^g and Φ(Q) = 1.
-/

open Subgroup BinaryPermutation
namespace FiveCoreDihedralSquare
abbrev Bit := Multiplicative (ZMod 2)
abbrev Plane := Bit × Bit
abbrev Base := Plane × Plane
abbrev Actor := Bit × Bit

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

def baseAction : Actor →* MulAut Base where
  toFun a := MulEquiv.prodCongr (planeAction a.1) (planeAction a.2)
  map_one' := by ext x <;> simp [MulEquiv.prodCongr]
  map_mul' a b := by ext x <;> simp [map_mul, MulEquiv.prodCongr]

abbrev PlaneGroup := Plane ⋊[planeAction] Bit
abbrev Model := Base ⋊[baseAction] Actor

def splitPlanes : Model ≃* PlaneGroup × PlaneGroup where
  toFun x := (⟨x.left.1, x.right.1⟩, ⟨x.left.2, x.right.2⟩)
  invFun x := ⟨(x.1.left, x.2.left), (x.1.right, x.2.right)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

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

def permutation : Actor →* Equiv.Perm (Fin 5) :=
  MonoidHom.noncommCoprod
    (involutionHom (Equiv.swap (0 : Fin 5) 1) (by decide))
    (involutionHom (Equiv.swap (2 : Fin 5) 3) (by decide))
    (by
      intro a b
      exact Commute.pow_pow (by
        change Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3 =
          Equiv.swap 2 3 * Equiv.swap 0 1
        decide +kernel) _ _)

theorem coordinate_action (a : Actor) (v : Base) :
    coreCoordinates (baseAction a v) = Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (permutation a) (coreCoordinates v).toAdd) := by
  have h : ∀ (a : Actor) (v : Base), coreCoordinates (baseAction a v) = Multiplicative.ofAdd
      (coreRepresentation (Fin 5) (permutation a) (coreCoordinates v).toAdd) := by
    decide +kernel
  exact h a v

theorem permutation_injective : Function.Injective permutation := by decide +kernel

theorem permutation_range : permutation.range =
    closure ({Equiv.swap 0 1, Equiv.swap 2 3} : Set (Equiv.Perm (Fin 5))) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    change Equiv.swap (0 : Fin 5) 1 ^ a.1.toAdd.val * Equiv.swap 2 3 ^ a.2.toAdd.val ∈ _
    exact mul_mem (pow_mem (subset_closure (by simp)) _)
      (pow_mem (subset_closure (by simp)) _)
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨(.ofAdd 1, 1), by decide +kernel⟩
    · have hx : x = Equiv.swap 2 3 := hx
      subst x
      exact ⟨(1, .ofAdd 1), by decide +kernel⟩
end FiveCoreDihedralSquare

namespace FiveCoreDihedralSquare
open Subgroup BinaryPermutation

private theorem recognize_from_section {S : Type*} [Group S]
    (V C : Subgroup S) (hCZ : C ≤ center S) (hd : Disjoint V C)
    (q : S →* Equiv.Perm (Fin 5)) (hr : q.range = permutation.range)
    (hk : q.ker = V ⊔ C)
    (m : Multiplicative (core (Fin 5)) ≃* V)
    (he : ∀ (s : S) (x : core (Fin 5)),
      (m (.ofAdd (coreRepresentation (Fin 5) (q s) x)) : S) =
        s * (m (.ofAdd x) : S) * s⁻¹)
    (j : Actor →* S) (hj : ∀ a, q (j a) = permutation a) :
    Nonempty (S ≃* C × (DihedralGroup 4 × DihedralGroup 4)) := by
  let v : Base →* S := V.subtype.comp (m.toMonoidHom.comp coreCoordinates.toMonoidHom)
  have hv (x : Base) : v x ∈ V := (m (coreCoordinates x)).property
  have hvq (x : Base) : q (v x) = 1 := (show V ≤ q.ker from hk ▸ le_sup_left) (hv x)
  have hcq (c : C) : q c = 1 := (show C ≤ q.ker from hk ▸ le_sup_right) c.property
  have hvj (a : Actor) : v.comp (baseAction a).toMonoidHom =
      (MulAut.conj (j a)).toMonoidHom.comp v := by
    apply MonoidHom.ext
    intro x
    change (m (coreCoordinates (baseAction a x)) : S) =
      j a * (m (coreCoordinates x) : S) * (j a)⁻¹
    rw [coordinate_action]
    have hh := he (j a) (coreCoordinates x).toAdd
    rw [hj] at hh
    exact hh
  let f : Model →* S := SemidirectProduct.lift v j hvj
  have hfq (x : Model) : q (f x) = permutation x.right := by
    change q (v x.left * j x.right) = _
    rw [map_mul, hvq, hj, one_mul]
  have hc (c : C) (x : Model) : Commute (c : S) (f x) :=
    (mem_center_iff.mp (hCZ c.property) (f x)).symm
  let F : C × Model →* S := C.subtype.noncommCoprod f hc
  have hFq (x : C × Model) : q (F x) = permutation x.2.right := by
    change q ((x.1 : S) * f x.2) = _
    rw [map_mul, hcq, hfq, one_mul]
  have hvinj : Function.Injective v :=
    V.subtype_injective.comp (m.injective.comp coreCoordinates.injective)
  have hFinj : Function.Injective F := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply (eq_bot_iff_forall _).mpr
    rintro ⟨c, x⟩ hx
    have hxF : F (c, x) = 1 := hx
    have hright : x.right = 1 := permutation_injective (by
      have hh := congrArg q hxF
      simpa only [hFq, map_one] using hh)
    have hh : (c : S) * v x.left = 1 := by
      change (c : S) * (v x.left * j x.right) = 1 at hxF
      simpa only [hright, map_one, mul_one] using hxF
    have hvC : v x.left ∈ C := by
      have heq : v x.left = (c : S)⁻¹ := by
        calc
          v x.left = (c : S)⁻¹ * ((c : S) * v x.left) := (inv_mul_cancel_left _ _).symm
          _ = (c : S)⁻¹ := by rw [hh, mul_one]
      rw [heq]
      exact C.inv_mem c.property
    have hvone : v x.left = 1 := Subgroup.disjoint_def.mp hd (hv x.left) hvC
    have hleft : x.left = 1 := hvinj (by simpa only [map_one] using hvone)
    have hc1 : c = 1 := Subtype.ext (by simpa only [hvone, mul_one, Subgroup.coe_one] using hh)
    exact Prod.ext hc1 (SemidirectProduct.ext hleft hright)
  have hFsurj : Function.Surjective F := by
    apply MonoidHom.range_eq_top.mp
    apply (eq_top_iff' _).mpr
    intro s
    have hqs : q s ∈ permutation.range := hr ▸ (show q s ∈ q.range from ⟨s, rfl⟩)
    obtain ⟨a, ha⟩ := hqs
    have hz : s * (j a)⁻¹ ∈ V ⊔ C := by
      rw [← hk]
      change q (s * (j a)⁻¹) = 1
      rw [map_mul, map_inv, hj, ha, mul_inv_cancel]
    have hVC : V ⊔ C ≤ F.range := by
      apply sup_le
      · intro u hu
        obtain ⟨x, hx⟩ := m.surjective ⟨u, hu⟩
        obtain ⟨b, hb⟩ := coreCoordinates.surjective x
        refine ⟨(1, SemidirectProduct.inl b), ?_⟩
        change 1 * (v b * j 1) = u
        rw [map_one, mul_one, one_mul]
        change (m (coreCoordinates b) : S) = u
        rw [hb]
        exact congrArg Subtype.val hx
      · intro c hcC
        exact ⟨(⟨c, hcC⟩, 1), by change c * f 1 = c; rw [map_one, mul_one]⟩
    have hjmem : j a ∈ F.range :=
      ⟨(1, SemidirectProduct.inr a), by change 1 * (v 1 * j a) = j a; rw [map_one, one_mul, one_mul]⟩
    have hm := F.range.mul_mem (hVC hz) hjmem
    simpa only [inv_mul_cancel_right] using hm
  obtain ⟨e⟩ := plane_dihedral
  exact ⟨(MulEquiv.ofBijective F ⟨hFinj, hFsurj⟩).symm.trans
    (MulEquiv.prodCongr (MulEquiv.refl C)
      (splitPlanes.trans (MulEquiv.prodCongr e e)))⟩

/-- The actual core action and elementary supplement determine both dihedral factors. -/
public theorem recognize {S : Type*} [Group S]
    (V C W : Subgroup S) [IsElementaryAbelian 2 W]
    (hCZ : C ≤ center S) (hd : Disjoint V C)
    (q : S →* Equiv.Perm (Fin 5))
    (hr : q.range = closure ({Equiv.swap 0 1, Equiv.swap 2 3} : Set (Equiv.Perm (Fin 5))))
    (hk : q.ker = V ⊔ C) (hgen : V ⊔ C ⊔ W = ⊤)
    (m : Multiplicative (core (Fin 5)) ≃* V)
    (he : ∀ (s : S) (x : core (Fin 5)),
      (m (.ofAdd (coreRepresentation (Fin 5) (q s) x)) : S) =
        s * (m (.ofAdd x) : S) * s⁻¹) :
    Nonempty (S ≃* C × (DihedralGroup 4 × DihedralGroup 4)) := by
  have hW : W.map q = q.range := by
    have h := congrArg (fun P : Subgroup S => P.map q) hgen
    rw [← hk, Subgroup.map_sup, map_ker_self, bot_sup_eq] at h
    exact h.trans q.range_eq_map.symm
  have ha0 : Equiv.swap (0 : Fin 5) 1 ∈ W.map q := by
    rw [hW, hr]
    exact subset_closure (by simp)
  have hb0 : Equiv.swap (2 : Fin 5) 3 ∈ W.map q := by
    rw [hW, hr]
    exact subset_closure (by simp)
  obtain ⟨a, haW, ha⟩ := ha0
  obtain ⟨b, hbW, hb⟩ := hb0
  have ha2 : a ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a haW
  have hb2 : b ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian b hbW
  have hab : Commute a b := setLike_mul_comm haW hbW
  let j : Actor →* S := MonoidHom.noncommCoprod (involutionHom a ha2)
    (involutionHom b hb2) (fun _ _ => hab.pow_pow _ _)
  have hj (u : Actor) : q (j u) = permutation u := by
    change q (a ^ u.1.toAdd.val * b ^ u.2.toAdd.val) =
      Equiv.swap 0 1 ^ u.1.toAdd.val * Equiv.swap 2 3 ^ u.2.toAdd.val
    rw [map_mul, map_pow, map_pow, ha, hb]
  exact recognize_from_section V C hCZ hd q (hr.trans permutation_range.symm) hk m he j hj
end FiveCoreDihedralSquare
