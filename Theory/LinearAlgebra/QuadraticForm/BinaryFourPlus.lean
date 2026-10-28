module

public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane
public import Theory.LinearAlgebra.QuadraticForm.IsometryGroup
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Tactic.NormNum

/-!
# The binary four-dimensional plus orthogonal group

On two binary planes take the orthogonal sum of x² + xy + y². Its six
nonsingular vectors are the three nonzero vectors on each axis. Two distinct
such vectors have nonsingular sum exactly when they lie on the same axis.
Consequently every linear isometry preserves or swaps the two planes.
Restriction then gives two plane automorphisms, each a permutation of three
points; conversely these permutations and the swap preserve the quadratic form.

The resulting mutually inverse group maps identify the full isometry subgroup
with the literal regular wreath product S₃ wr C₂, including its linear action.
The order 72 is a consequence of this equivalence. This is the concrete
O₄⁺(2) identification used in Aschbacher–Smith, Lemma 14.2.21, printed p.988
(PDF p.1005). No quaternion quotient or chapter interface is assumed here.
-/

public section

namespace BinaryFourPlus
abbrev V := Plane × Plane

@[expose] def q : QuadraticForm (ZMod 2) V :=
  planeQ.comp (LinearMap.fst _ _ _) + planeQ.comp (LinearMap.snd _ _ _)

theorem q_split (v : V) : q v = planeQ v.1 + planeQ v.2 := rfl

theorem q_apply (v : V) : q v = v.1 0 ^ 2 + v.1 0 * v.1 1 + v.1 1 ^ 2 +
    v.2 0 ^ 2 + v.2 0 * v.2 1 + v.2 1 ^ 2 := by
  simp only [q, planeQ, add_apply, QuadraticMap.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply, QuadraticMap.proj_apply, pow_two]
  simp only [add_assoc]

theorem q_one_iff : ∀v : V, q v = 1 ↔
    (v.1 ≠ 0 ∧ v.2 = 0) ∨ (v.1 = 0 ∧ v.2 ≠ 0) := by decide

private theorem same_axis : ∀ x y : V, q x = 1 → q y = 1 →
    (q (x+y) = 1 ∨ x = y) → (x.1 = 0 ↔ y.1 = 0) ∧ (x.2 = 0 ↔ y.2 = 0) := by
  have h₁ : ∀x y : V, q x = 1 → q y = 1 → q (x+y) = 1 →
      (x.1 = 0 ↔ y.1 = 0) := by decide
  have h₂ : ∀x y : V, q x = 1 → q y = 1 → q (x+y) = 1 →
      (x.2 = 0 ↔ y.2 = 0) := by decide
  intro x y hx hy h
  rcases h with h | rfl
  · exact ⟨h₁ x y hx hy h, h₂ x y hx hy h⟩
  · exact ⟨Iff.rfl,Iff.rfl⟩

private theorem opposite_axis : ∀ x y : V, q x = 1 → q y = 1 →
    q (x+y) = 0 → x ≠ y → (x.1 = 0 ↔ y.2 = 0) ∧ (x.2 = 0 ↔ y.1 = 0) := by
  have table : ∀x y : V, q x = 1 → q y = 1 →
      q (x+y) = if x = y then 0 else if (x.1 = 0 ↔ y.2 = 0) then 0 else 1 := by decide
  have cross (x y : V) (hx : q x = 1) (hy : q y = 1)
      (h : q (x+y) = 0) (hne : x ≠ y) : x.1 = 0 ↔ y.2 = 0 := by
    have ht := table x y hx hy
    rw [if_neg hne, h] at ht
    by_contra hn
    rw [if_neg hn] at ht
    exact zero_ne_one ht
  intro x y hx hy h hne
  exact ⟨cross x y hx hy h hne,
    (cross y x hy hx (by simpa only [add_comm] using h) hne.symm).symm⟩

private theorem first_axis_sum : ∀u v : Plane, u ≠ 0 → v ≠ 0 →
    q ((u,0)+(v,0)) = 1 ∨ u = v := by decide

private theorem cross_axis_sum : ∀u v : Plane, u ≠ 0 → v ≠ 0 →
    q ((u,0)+(0,v)) = 0 := by decide

theorem preserves_or_swaps (g : q.isometrySubgroup) :
    ((∀u : Plane, (g.val (u,0)).2 = 0) ∧ (∀u : Plane, (g.val (0,u)).1 = 0)) ∨
    ((∀u : Plane, (g.val (u,0)).1 = 0) ∧ (∀u : Plane, (g.val (0,u)).2 = 0)) := by
  have hg : ∀v, q (g.val v) = q v := (QuadraticMap.mem_isometrySubgroup q g.val).mp g.property
  let e : Plane := ![1,0]
  have he : e ≠ 0 := by decide
  have hq (u : Plane) (hu : u ≠ 0) : q (g.val (u,0)) = 1 := by
    rw [hg]
    exact (q_one_iff _).mpr (Or.inl ⟨hu,rfl⟩)
  have hq' (u : Plane) (hu : u ≠ 0) : q (g.val (0,u)) = 1 := by
    rw [hg]
    exact (q_one_iff _).mpr (Or.inr ⟨rfl,hu⟩)
  have hs (u : Plane) (hu : u ≠ 0) := same_axis (g.val (e,0)) (g.val (u,0))
    (hq e he) (hq u hu) (by
      rcases first_axis_sum e u he hu with h | h
      · exact Or.inl (by rw [← map_add, hg]; exact h)
      · exact Or.inr (by rw [h]))
  have ho (u : Plane) (hu : u ≠ 0) := opposite_axis (g.val (e,0)) (g.val (0,u))
    (hq e he) (hq' u hu) (by rw [← map_add, hg]; exact cross_axis_sum e u he hu)
    (by intro h; exact he (congrArg Prod.fst (g.val.injective h)))
  rcases (q_one_iff _).mp (hq e he) with h | h
  · left
    constructor
    · intro u
      by_cases hu : u = 0
      · subst u; change (g.val 0).2 = 0; simp
      · exact (hs u hu).2.mp h.2
    · intro u
      by_cases hu : u = 0
      · subst u; change (g.val 0).1 = 0; simp
      · exact (ho u hu).2.mp h.2
  · right
    constructor
    · intro u
      by_cases hu : u = 0
      · subst u; change (g.val 0).1 = 0; simp
      · exact (hs u hu).1.mp h.1
    · intro u
      by_cases hu : u = 0
      · subst u; change (g.val 0).2 = 0; simp
      · exact (ho u hu).1.mp h.1

private theorem linear_prod_of_preserving
    (f : V ≃ₗ[ZMod 2] V)
    (h0 : ∀v : Plane, (f (v,0)).2 = 0)
    (h1 : ∀v : Plane, (f (0,v)).1 = 0) :
    ∃a b : Plane ≃ₗ[ZMod 2] Plane, ∀v : V, f v = (a v.1, b v.2) := by
  let a : Plane →ₗ[ZMod 2] Plane :=
    (LinearMap.fst _ _ _).comp (f.toLinearMap.comp (LinearMap.inl _ _ _))
  let b : Plane →ₗ[ZMod 2] Plane :=
    (LinearMap.snd _ _ _).comp (f.toLinearMap.comp (LinearMap.inr _ _ _))
  have hf (v : V) : f v = (a v.1, b v.2) := by
    have hv : v = (v.1, 0) + (0, v.2) := by ext <;> simp
    calc
      f v = f (v.1, 0) + f (0, v.2) := by rw [← map_add, ← hv]
      _ = (a v.1, b v.2) := by ext <;> simp [a, b, h0, h1]
  have ha : Function.Bijective a := by
    constructor
    · intro x y hxy
      have hh : f (x, 0) = f (y, 0) := by simp [hf, hxy]
      exact congrArg Prod.fst (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (x,0)
      exact ⟨v.1, by simpa [hf] using congrArg Prod.fst hv⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y hxy
      have hh : f (0, x) = f (0, y) := by simp [hf, hxy]
      exact congrArg Prod.snd (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (0,x)
      exact ⟨v.2, by simpa [hf] using congrArg Prod.snd hv⟩
  exact ⟨LinearEquiv.ofBijective a ha, LinearEquiv.ofBijective b hb, hf⟩

theorem exists_factors (g : q.isometrySubgroup) :
    (∃a b : Plane ≃ₗ[ZMod 2] Plane, ∀v : V, g.val v = (a v.1,b v.2)) ∨
    (∃a b : Plane ≃ₗ[ZMod 2] Plane, ∀v : V, g.val v = (a v.2,b v.1)) := by
  rcases preserves_or_swaps g with h | h
  · exact Or.inl (linear_prod_of_preserving g.val h.1 h.2)
  · obtain ⟨a,b,hf⟩ := linear_prod_of_preserving
      ((LinearEquiv.prodComm (ZMod 2) Plane Plane).trans g.val) h.2 h.1
    exact Or.inr ⟨a,b,fun v => by simpa using hf (v.2,v.1)⟩

abbrev C2 := Multiplicative (ZMod 2)
abbrev Wreath := RegularWreathProduct (Equiv.Perm (Fin 3)) C2
private abbrev LinearWreath := RegularWreathProduct (Plane ≃ₗ[ZMod 2] Plane) C2

/-- The nonidentity element interchanges the two planes. -/
@[expose] def swapIndex : C2 := Multiplicative.ofAdd 1

private theorem index_cases : ∀ i : C2, i = 1 ∨ i = swapIndex := by decide
@[simp] theorem swapIndex_ne_one : swapIndex ≠ 1 := by decide
@[simp] theorem swapIndex_inv : swapIndex⁻¹ = swapIndex := by decide
@[simp] theorem swapIndex_mul_self : swapIndex * swapIndex = 1 := by decide

private def linearWreathMap (w : LinearWreath) : V ≃ₗ[ZMod 2] V :=
  if w.right = 1 then (w.left 1).prodCongr (w.left swapIndex)
  else (LinearEquiv.prodComm (ZMod 2) Plane Plane).trans
    ((w.left 1).prodCongr (w.left swapIndex))

private def linearWreathHom : LinearWreath →* (V ≃ₗ[ZMod 2] V) where
  toFun := linearWreathMap
  map_one' := by
    apply LinearEquiv.ext
    intro v
    simp [linearWreathMap]
  map_mul' a b := by
    apply LinearEquiv.ext
    intro v
    rcases index_cases a.right with ha | ha <;>
      rcases index_cases b.right with hb | hb <;>
      simp [linearWreathMap, RegularWreathProduct.mul_left,
        RegularWreathProduct.mul_right, ha, hb, LinearEquiv.mul_apply]

private def linearWreathToIsometry : LinearWreath →* q.isometrySubgroup where
  toFun w := ⟨linearWreathHom w, by
    apply (QuadraticMap.mem_isometrySubgroup q _).mpr
    intro v
    change q (linearWreathMap w v) = q v
    rcases index_cases w.right with h | h <;>
      simp [linearWreathMap, h, q_split, plane_aut_preserves, add_comm]⟩
  map_one' := Subtype.ext linearWreathHom.map_one
  map_mul' a b := Subtype.ext (linearWreathHom.map_mul a b)

private theorem linearWreathToIsometry_injective : Function.Injective linearWreathToIsometry := by
  apply (injective_iff_map_eq_one linearWreathToIsometry).mpr
  intro w hw
  have hf : linearWreathMap w = 1 := congrArg Subtype.val hw
  rcases index_cases w.right with h | h
  · apply RegularWreathProduct.ext
    · funext i
      apply LinearEquiv.ext
      intro u
      rcases index_cases i with rfl | rfl
      · have hh := congrArg (fun f : V ≃ₗ[ZMod 2] V => (f (u,0)).1) hf
        simpa [linearWreathMap, h] using hh
      · have hh := congrArg (fun f : V ≃ₗ[ZMod 2] V => (f (0,u)).2) hf
        simpa [linearWreathMap, h] using hh
    · exact h
  · have hh := congrArg (fun f : V ≃ₗ[ZMod 2] V => (f (![1,0],0)).1 0) hf
    simp [linearWreathMap,h] at hh

private theorem linearWreathToIsometry_surjective : Function.Surjective linearWreathToIsometry := by
  intro g
  rcases exists_factors g with ⟨a,b,h⟩ | ⟨a,b,h⟩
  · refine ⟨⟨(fun i => if i = 1 then a else b), 1⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change linearWreathMap _ v = g.val v
    simp [linearWreathMap, h]
  · refine ⟨⟨(fun i => if i = 1 then a else b), swapIndex⟩, ?_⟩
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    change linearWreathMap _ v = g.val v
    simp [linearWreathMap, h]

/-- Extend the two permutations linearly, then interchange the input planes
if the shift is nontrivial. The base permutation is indexed by the output plane. -/
def wreathToIsometry : Wreath →* q.isometrySubgroup :=
  linearWreathToIsometry.comp
    (RegularWreathProduct.congr planeAutEquiv (MulEquiv.refl C2)).symm.toMonoidHom

theorem wreathToIsometry_bijective : Function.Bijective wreathToIsometry :=
  ⟨linearWreathToIsometry_injective.comp
      (RegularWreathProduct.congr planeAutEquiv (MulEquiv.refl C2)).symm.injective,
    linearWreathToIsometry_surjective.comp
      (RegularWreathProduct.congr planeAutEquiv (MulEquiv.refl C2)).symm.surjective⟩

/-- The full isometry group of the explicit plus form is S₃ wreath C₂.
The forward map is the inverse of the explicit linear wreath action. -/
@[expose] noncomputable def isometryEquivWreath : q.isometrySubgroup ≃* Wreath :=
  (MulEquiv.ofBijective wreathToIsometry wreathToIsometry_bijective).symm

@[simp] theorem isometryEquivWreath_symm_apply (w : Wreath) :
    isometryEquivWreath.symm w = wreathToIsometry w := rfl

@[simp] theorem wreathToIsometry_equiv (g : q.isometrySubgroup) :
    wreathToIsometry (isometryEquivWreath g) = g :=
  isometryEquivWreath.symm_apply_apply g

@[simp] theorem equiv_wreathToIsometry (w : Wreath) :
    isometryEquivWreath (wreathToIsometry w) = w :=
  isometryEquivWreath.apply_symm_apply w

/-- Compatibility with the literal linear action on the ordered pair of planes. -/
theorem wreathToIsometry_apply (w : Wreath) (v : V) :
    (wreathToIsometry w).val v =
      if w.right = 1 then
        (planeLinear (w.left 1) v.1, planeLinear (w.left swapIndex) v.2)
      else (planeLinear (w.left 1) v.2, planeLinear (w.left swapIndex) v.1) := by
  change linearWreathMap
    ⟨(fun i => planeLinear (w.left i)), w.right⟩ v = _
  unfold linearWreathMap
  split <;> rfl

/-- Vector coordinates use the same indexing as Mathlib's regular wreath product. -/
@[expose] def coordinate (v : V) (i : C2) : Plane := if i = 1 then v.1 else v.2

theorem wreathToIsometry_coordinate (w : Wreath) (v : V) (i : C2) :
    coordinate ((wreathToIsometry w).val v) i =
      planeLinear (w.left i) (coordinate v (w.right⁻¹ * i)) := by
  rw [wreathToIsometry_apply]
  rcases index_cases w.right with h | h <;> rcases index_cases i with rfl | rfl <;>
    simp [coordinate, h]

/-- The identification intertwines every isometry with the standard coordinate action. -/
theorem isometryEquivWreath_action (g : q.isometrySubgroup) (v : V) (i : C2) :
    coordinate (g.val v) i = planeLinear ((isometryEquivWreath g).left i)
      (coordinate v ((isometryEquivWreath g).right⁻¹ * i)) := by
  simpa only [wreathToIsometry_equiv] using
    wreathToIsometry_coordinate (isometryEquivWreath g) v i

/-- The order follows from the action-compatible group equivalence. -/
theorem card_isometrySubgroup : Nat.card q.isometrySubgroup = 72 := by
  rw [Nat.card_congr isometryEquivWreath.toEquiv, RegularWreathProduct.card, Nat.card_perm]
  norm_num [Nat.factorial]

/-- Number the three nonzero vectors in each of the two anisotropic planes. -/
@[expose] def nonsingularVector (p : Fin 3 × C2) : V :=
  if p.2 = 1 then (nonzeroVector p.1, 0) else (0, nonzeroVector p.1)

theorem nonsingularVector_q : ∀p : Fin 3 × C2, q (nonsingularVector p) = 1 := by decide

private theorem nonsingularVector_bijective :
    Function.Bijective (fun p : Fin 3 × C2 =>
      (⟨nonsingularVector p, nonsingularVector_q p⟩ : {v : V // q v = 1})) := by
  constructor <;> decide

/-- The six nonsingular vectors, with their actual vector coordinates. -/
@[expose] noncomputable def nonsingularEquiv : (Fin 3 × C2) ≃ {v : V // q v = 1} :=
  Equiv.ofBijective (fun p : Fin 3 × C2 =>
    (⟨nonsingularVector p, nonsingularVector_q p⟩ : {v : V // q v = 1}))
    (by exact nonsingularVector_bijective)

@[simp] theorem nonsingularEquiv_apply (p : Fin 3 × C2) :
    (nonsingularEquiv p).val = nonsingularVector p := rfl

theorem card_nonsingular : Nat.card {v : V // q v = 1} = 6 := by
  rw [Nat.card_congr nonsingularEquiv.symm, Nat.card_prod]
  norm_num

/-- The polar-pairing graph on the six nonsingular vectors consists of two triangles. -/
theorem polar_nonsingular : ∀p r : Fin 3 × C2,
    q.polarBilin (nonsingularVector p) (nonsingularVector r) =
      if p.2 = r.2 ∧ p.1 ≠ r.1 then 1 else 0 := by decide

/-- On the six nonsingular vectors this is exactly the regular wreath permutation action. -/
theorem wreathToIsometry_nonsingular (w : Wreath) (p : Fin 3 × C2) :
    (wreathToIsometry w).val (nonsingularVector p) =
      nonsingularVector (w.left (w.right * p.2) p.1, w.right * p.2) := by
  rw [wreathToIsometry_apply]
  rcases index_cases w.right with h | h <;> rcases index_cases p.2 with hi | hi <;>
    simp [nonsingularVector, h, hi]

/-- The diagonal plane is totally singular, witnessing the plus geometry. -/
theorem diagonal_singular : ∀u : Plane, q (u,u) = 0 := by decide

/-- The polar form has trivial radical. -/
theorem polar_separates : ∀v : V, (∀u : V, q.polarBilin v u = 0) → v = 0 := by decide

end BinaryFourPlus
