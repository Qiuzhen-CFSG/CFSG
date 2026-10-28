module

public import Theory.ElementaryAbelian.Basic
public import Mathlib.Algebra.CharP.Two
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Even-field upper-unitriangular geometry

The coordinates `(a,b,c)` denote the literal matrix
`!![1,a,c; 0,1,b; 0,0,1]`. The two root planes have respectively `b=0`
and `a=0`, and their intersection is the center. In characteristic two,
squaring detects `ab`; commuting detects `ab' - a'b`. These identities
classify elementary abelian subgroups and noncentral involution centralizers.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
§5.3.5--5.3.7, printed p. 660 (PDF p. 677). Ambient fusion is separate.
The matrix realization adapts Gerald Höhn's
`Atlas/LinearGroups/UpperUnitriangularThree.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`, to CFSG coordinates and Lean 4.33.
The ATLAS Research and Attribution License 1.0 applies to that portion;
see `LICENSES/ATLAS.txt` and `docs/atlas-porting.md`.
-/

@[expose] public section
noncomputable section
namespace Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F]

@[ext] structure U (F : Type*) where
  x : F
  y : F
  c : F

instance : Mul (U F) where
  mul a b := ⟨a.x + b.x, a.y + b.y, a.c + b.c + a.x * b.y⟩
instance : One (U F) where
  one := ⟨0, 0, 0⟩
instance : Inv (U F) where
  inv a := ⟨-a.x, -a.y, a.x * a.y - a.c⟩
instance : Group (U F) where
  mul_assoc a b c := by
    refine U.ext (add_assoc _ _ _) (add_assoc _ _ _) ?_
    change (a.c + b.c + a.x * b.y) + c.c + (a.x + b.x) * c.y =
      a.c + (b.c + c.c + b.x * c.y) + a.x * (b.y + c.y)
    ring
  one_mul a := by
    refine U.ext (zero_add _) (zero_add _) ?_
    change 0 + a.c + 0 * a.y = a.c
    ring
  mul_one a := by
    refine U.ext (add_zero _) (add_zero _) ?_
    change a.c + 0 + a.x * 0 = a.c
    ring
  inv_mul_cancel a := by
    refine U.ext (neg_add_cancel _) (neg_add_cancel _) ?_
    change (a.x * a.y - a.c) + a.c + -a.x * a.y = 0
    ring

def coordinates : U F ≃ F × F × F where
  toFun a := (a.x, a.y, a.c)
  invFun a := ⟨a.1, a.2.1, a.2.2⟩

instance [Finite F] : Finite (U F) := Finite.of_equiv _ (coordinates F).symm

omit [Field F] in
theorem card_U [Finite F] : Nat.card (U F) = Nat.card F ^ 3 := by
  rw [Nat.card_congr (coordinates F), Nat.card_prod, Nat.card_prod]
  ring

@[simp] theorem mul_x (a b : U F) : (a * b).x = a.x + b.x := rfl
@[simp] theorem mul_y (a b : U F) : (a * b).y = a.y + b.y := rfl
@[simp] theorem mul_c (a b : U F) : (a * b).c = a.c + b.c + a.x * b.y := rfl
@[simp] theorem one_x : (1 : U F).x = 0 := rfl
@[simp] theorem one_y : (1 : U F).y = 0 := rfl
@[simp] theorem one_c : (1 : U F).c = 0 := rfl

def axis₁ : Multiplicative (F × F) →* U F where
  toFun p := ⟨p.toAdd.1, 0, p.toAdd.2⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp

def axis₂ : Multiplicative (F × F) →* U F where
  toFun p := ⟨0, p.toAdd.1, p.toAdd.2⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp

def central : Multiplicative F →* U F where
  toFun c := ⟨0, 0, c.toAdd⟩
  map_one' := rfl
  map_mul' a b := by apply U.ext <;> simp


def V₁ : Subgroup (U F) := (axis₁ F).range
def V₂ : Subgroup (U F) := (axis₂ F).range
def Z : Subgroup (U F) := (central F).range

theorem axis₁_injective : Function.Injective (axis₁ F) := by
  intro a b h
  exact Prod.ext (congrArg U.x h) (congrArg U.c h)
theorem axis₂_injective : Function.Injective (axis₂ F) := by
  intro a b h
  exact Prod.ext (congrArg U.y h) (congrArg U.c h)
theorem central_injective : Function.Injective (central F) := by
  intro a b h
  exact congrArg U.c h

def plane₁Equiv : Multiplicative (F × F) ≃* V₁ F :=
  MonoidHom.ofInjective (axis₁_injective F)
def plane₂Equiv : Multiplicative (F × F) ≃* V₂ F :=
  MonoidHom.ofInjective (axis₂_injective F)
def centralEquiv : Multiplicative F ≃* Z F :=
  MonoidHom.ofInjective (central_injective F)

@[simp] theorem mem_V₁ (a : U F) : a ∈ V₁ F ↔ a.y = 0 := by
  constructor
  · rintro ⟨p, rfl⟩; rfl
  · intro h; exact ⟨Multiplicative.ofAdd (a.x, a.c), U.ext rfl h.symm rfl⟩
@[simp] theorem mem_V₂ (a : U F) : a ∈ V₂ F ↔ a.x = 0 := by
  constructor
  · rintro ⟨p, rfl⟩; rfl
  · intro h; exact ⟨Multiplicative.ofAdd (a.y, a.c), U.ext h.symm rfl rfl⟩
@[simp] theorem mem_Z (a : U F) : a ∈ Z F ↔ a.x = 0 ∧ a.y = 0 := by
  constructor
  · rintro ⟨p, rfl⟩; exact ⟨rfl, rfl⟩
  · rintro ⟨h,k⟩; exact ⟨Multiplicative.ofAdd a.c, U.ext h.symm k.symm rfl⟩

theorem card_V₁ : Nat.card (V₁ F) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (plane₁Equiv F).toEquiv]
  change Nat.card (F × F) = _
  rw [Nat.card_prod, pow_two]
theorem card_V₂ : Nat.card (V₂ F) = Nat.card F ^ 2 := by
  rw [← Nat.card_congr (plane₂Equiv F).toEquiv]
  change Nat.card (F × F) = _
  rw [Nat.card_prod, pow_two]
theorem card_Z : Nat.card (Z F) = Nat.card F :=
  (Nat.card_congr (centralEquiv F).toEquiv).symm

theorem mul_comm_iff (a b : U F) : a * b = b * a ↔ a.x * b.y = b.x * a.y := by
  constructor
  · intro h
    have := congrArg U.c h
    simpa only [mul_c, add_comm b.c a.c, add_right_inj] using this
  · intro h
    apply U.ext <;> simp [add_comm, h]

theorem Z_eq_center : Z F = Subgroup.center (U F) := by
  ext a
  rw [mem_Z, Subgroup.mem_center_iff]
  constructor
  · rintro ⟨h,k⟩ b
    apply (mul_comm_iff F b a).mpr
    simp [h,k]
  · intro h
    have h₁ := (mul_comm_iff F _ _).mp (h (⟨0,1,0⟩ : U F))
    have h₂ := (mul_comm_iff F _ _).mp (h (⟨1,0,0⟩ : U F))
    simpa using And.intro h₁.symm h₂

instance : (Z F).Normal := Z_eq_center F ▸ inferInstance

def abelianization : U F →* Multiplicative (F × F) where
  toFun a := Multiplicative.ofAdd (a.x, a.y)
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ker_abelianization : (abelianization F).ker = Z F := by
  ext a
  change (a.x, a.y) = (0,0) ↔ _
  simp

instance quotient_isMulCommutative : IsMulCommutative (U F ⧸ Z F) := by
  let e := QuotientGroup.congr (Z F) (abelianization F).ker (MulEquiv.refl (U F))
    (by simpa using (ker_abelianization F).symm)
  refine ⟨⟨fun a b => e.injective ?_⟩⟩
  apply QuotientGroup.kerLift_injective (abelianization F)
  simp only [map_mul, mul_comm]

section Even
variable [CharP F 2]

theorem square_eq_one_iff (a : U F) : a ^ 2 = 1 ↔ a.x = 0 ∨ a.y = 0 := by
  rw [pow_two]
  constructor
  · intro h
    have := congrArg U.c h
    simpa [CharTwo.add_self_eq_zero, mul_eq_zero] using this
  · intro h
    apply U.ext <;> simp [CharTwo.add_self_eq_zero, mul_eq_zero.mpr h]

instance : IsElementaryAbelian 2 (Multiplicative (F × F)) where
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    rw [pow_two]
    change a.toAdd + a.toAdd = 0
    exact Prod.ext (CharTwo.add_self_eq_zero _) (CharTwo.add_self_eq_zero _)

instance : IsElementaryAbelian 2 (V₁ F) where
  toIsMulCommutative := ⟨⟨fun a b => (plane₁Equiv F).symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Subtype.ext
    exact (square_eq_one_iff F a).mpr (Or.inr ((mem_V₁ F a).mp a.property))

instance : IsElementaryAbelian 2 (V₂ F) where
  toIsMulCommutative := ⟨⟨fun a b => (plane₂Equiv F).symm.injective (by
    simp only [map_mul, mul_comm])⟩⟩
  exponent_dvd_p := by
    apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Subtype.ext
    exact (square_eq_one_iff F a).mpr (Or.inl ((mem_V₂ F a).mp a.property))

/-- Even exponent alone forces a subgroup into one root plane. -/
theorem le_plane_of_exponent_two (A : Subgroup (U F))
    (hA : ∀ a ∈ A, a ^ 2 = 1) : A ≤ V₁ F ∨ A ≤ V₂ F := by
  by_cases h : A ≤ V₁ F
  · exact Or.inl h
  · right
    obtain ⟨a, ha, hay⟩ := SetLike.not_le_iff_exists.mp h
    have hay : a.y ≠ 0 := by simpa using hay
    have hax : a.x = 0 := ((square_eq_one_iff F a).mp (hA a ha)).resolve_right hay
    intro b hb
    rw [mem_V₂]
    by_contra hbx
    have hby : b.y = 0 := ((square_eq_one_iff F b).mp (hA b hb)).resolve_left hbx
    have hab := (square_eq_one_iff F (a * b)).mp (hA _ (A.mul_mem ha hb))
    simp [hax, hby, hbx, hay] at hab

theorem elementary_le_plane (A : Subgroup (U F)) [IsElementaryAbelian 2 A] :
    A ≤ V₁ F ∨ A ≤ V₂ F :=
  le_plane_of_exponent_two F A (fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha)

/-- The centralizer of a noncentral involution is exactly one root plane. -/
theorem centralizer_involution (a : U F) (ha : a ^ 2 = 1) (hz : a ∉ Z F) :
    Subgroup.centralizer ({a} : Set (U F)) = V₁ F ∨
      Subgroup.centralizer ({a} : Set (U F)) = V₂ F := by
  have hz : ¬ (a.x = 0 ∧ a.y = 0) := by simpa using hz
  rcases (square_eq_one_iff F a).mp ha with hx | hy
  · right
    have hy : a.y ≠ 0 := fun h => hz ⟨hx,h⟩
    ext b
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      mul_comm_iff, mem_V₂, hx, zero_mul]
    rw [eq_comm, mul_eq_zero]
    simp only [hy, or_false]
  · left
    have hx : a.x ≠ 0 := fun h => hz ⟨h,hy⟩
    ext b
    simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq,
      mul_comm_iff, mem_V₁, hy, mul_zero, mul_eq_zero, hx, false_or]

end Even

/-- Literal upper-unitriangular matrices, inside SL₃(F). -/
def matrix (a : U F) : Matrix (Fin 3) (Fin 3) F :=
  !![1, a.x, a.c; 0, 1, a.y; 0, 0, 1]

def specialLinear : U F →* Matrix.SpecialLinearGroup (Fin 3) F where
  toFun a := ⟨matrix F a, by simp [matrix, Matrix.det_fin_three]⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [matrix]
  map_mul' a b := by
    apply Subtype.ext
    change matrix F (a * b) = matrix F a * matrix F b
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrix, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem specialLinear_injective : Function.Injective (specialLinear F) := by
  intro a b h
  exact U.ext (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F => g 0 1) h)
    (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F => g 1 2) h)
    (congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F => g 0 2) h)

def matrixEquiv : U F ≃* (specialLinear F).range :=
  MonoidHom.ofInjective (specialLinear_injective F)

/-- Marked transport uses an actual equivalence onto the ambient subgroup. -/
def markedHom {G : Type*} [Group G] (S : Subgroup G) (e : U F ≃* S) : U F →* G :=
  S.subtype.comp e.toMonoidHom

theorem markedHom_injective {G : Type*} [Group G] (S : Subgroup G) (e : U F ≃* S) :
    Function.Injective (markedHom F S e) := Subtype.val_injective.comp e.injective

theorem range_markedHom {G : Type*} [Group G] (S : Subgroup G) (e : U F ≃* S) :
    (markedHom F S e).range = S := by
  ext x
  constructor
  · rintro ⟨a,rfl⟩; exact (e a).property
  · intro hx
    exact ⟨e.symm ⟨x,hx⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩

/-- Centralizers are transported relatively to the specified overgroup. -/
theorem map_centralizer {G : Type*} [Group G] (f : U F →* G)
    (hf : Function.Injective f) (a : U F) :
    (Subgroup.centralizer ({a} : Set (U F))).map f =
      f.range ⊓ Subgroup.centralizer ({f a} : Set G) := by
  ext x
  constructor
  · rintro ⟨b,hb,rfl⟩
    refine ⟨⟨b,rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    simpa only [map_mul] using congrArg f
      (Subgroup.mem_centralizer_singleton_iff.mp hb)
  · rintro ⟨⟨b,rfl⟩,hb⟩
    refine ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr (hf ?_), rfl⟩
    simpa only [map_mul] using Subgroup.mem_centralizer_singleton_iff.mp hb

/-- This is the relative geometry input used in the core alternative. -/
theorem marked_involution_geometry [CharP F 2] {G : Type*} [Group G]
    (S : Subgroup G) (e : U F ≃* S) (x : G) (hx : x ∈ S) (hpow : x ^ 2 = 1)
    (hz : x ∉ (Z F).map (markedHom F S e)) :
    S ⊓ Subgroup.centralizer ({x} : Set G) = (V₁ F).map (markedHom F S e) ∨
    S ⊓ Subgroup.centralizer ({x} : Set G) = (V₂ F).map (markedHom F S e) := by
  let f := markedHom F S e
  obtain ⟨a,ha⟩ : ∃ a, f a = x := by
    rw [← range_markedHom F S e] at hx
    exact hx
  subst x
  have hp : a ^ 2 = 1 := markedHom_injective F S e (by simpa using hpow)
  have hza : a ∉ Z F := fun h => hz ⟨a,h,rfl⟩
  have hc := map_centralizer F f (markedHom_injective F S e) a
  rw [range_markedHom F S e] at hc
  rcases centralizer_involution F a hp hza with h | h
  · left; rw [← hc,h]
  · right; rw [← hc,h]

theorem root_planes_inter : V₁ F ⊓ V₂ F = Z F := by
  ext a
  simp only [Subgroup.mem_inf, mem_V₁, mem_V₂, mem_Z, and_comm]

theorem Z_exponent_two [CharP F 2] (a : U F) (ha : a ∈ Z F) : a ^ 2 = 1 :=
  (square_eq_one_iff F a).mpr (Or.inl ((mem_Z F a).mp ha).1)

end Matrix.PSL3Even.UnipotentGeometry
