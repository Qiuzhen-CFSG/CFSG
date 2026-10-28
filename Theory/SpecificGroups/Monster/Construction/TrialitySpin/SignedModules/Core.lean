module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push

/-!
# Real modules of signed permutation sets

For a fixed-point-free involution on a finite set, anti-invariant real
functions form the signed permutation module. The vector attached to `x` is
`1_x - 1_{-x}`; evaluating on one representative of each pair gives a basis.
The form is one half of the sum of coordinate products, so this basis is
orthonormal. Every permutation commuting with the involution acts by inverse
pullback. The action on signed points is faithful, not merely faithful modulo
signs.

A preceding two-point orbit quotient implements the additional `k` relation
in the Parker spin construction. Its kernel criterion fixes each actual
`k`-orbit. No claimed kernel subgroup is included in the hypotheses.

Source: Aschbacher, *Sporadic Groups*, Exercise 4.3 and Lemma 14.6,
and the signed spaces preceding Lemma 27.3, printed pp. 146–147.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace Sporadic.Monster.Construction.TrialitySpin.SignedModules

/-- A permutation whose orbits have at most two points. -/
structure Pairing (X : Type*) where
  flip : Equiv.Perm X
  involutive : Function.Involutive flip

namespace Pairing
variable {X Y : Type*} (p : Pairing X) (q : Pairing Y)

def setoid : Setoid X where
  r x y := x = y ∨ x = p.flip y
  iseqv := ⟨fun _ => Or.inl rfl, by
    intro x y h
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (by rw [h, p.involutive]), by
    intro x y z hxy hyz
    rcases hxy with rfl | rfl
    · exact hyz
    · rcases hyz with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (p.involutive _)⟩

abbrev Orbit := Quotient p.setoid

def orbit (x : X) : p.Orbit := Quotient.mk p.setoid x

@[simp] theorem orbit_eq (x y : X) : p.orbit x = p.orbit y ↔ x = y ∨ x = p.flip y :=
  Quotient.eq

@[simp] theorem orbit_flip (x : X) : p.orbit (p.flip x) = p.orbit x :=
  (p.orbit_eq _ _).2 (Or.inr rfl)

theorem orbit_surjective : Function.Surjective p.orbit := Quotient.mk_surjective

instance [Finite X] : Finite p.Orbit := Finite.of_surjective _ p.orbit_surjective

def transport (e : X ≃ Y) (h : ∀ x, e (p.flip x) = q.flip (e x)) :
    p.Orbit ≃ q.Orbit where
  toFun := Quotient.map e (by
    intro x y hxy
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (h y))
  invFun := Quotient.map e.symm (by
    intro x y hxy
    rcases hxy with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (by apply e.injective; simp [h]))
  left_inv := by
    intro x
    induction x using Quotient.inductionOn with
    | h x =>
      change p.orbit (e.symm (e x)) = p.orbit x
      rw [e.symm_apply_apply]
  right_inv := by
    intro y
    induction y using Quotient.inductionOn with
    | h y =>
      change q.orbit (e (e.symm y)) = q.orbit y
      rw [e.apply_symm_apply]

@[simp] theorem transport_orbit (e : X ≃ Y)
    (h : ∀ x, e (p.flip x) = q.flip (e x)) (x : X) :
    p.transport q e h (p.orbit x) = q.orbit (e x) := rfl

/-- A choice of orientation for each two-point orbit, used only for a basis. -/
def orientedPoint (a : p.Orbit × Bool) : X :=
  if a.2 then p.flip a.1.out else a.1.out

@[simp] theorem orbit_orientedPoint (a : p.Orbit × Bool) :
    p.orbit (p.orientedPoint a) = a.1 := by
  rcases a with ⟨a, b⟩
  cases b
  · exact Quotient.out_eq a
  · exact (p.orbit_flip a.out).trans (Quotient.out_eq a)

theorem orientedPoint_bijective (hf : ∀ x, p.flip x ≠ x) :
    Function.Bijective p.orientedPoint := by
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hac : a = c := by
      simpa only [orbit_orientedPoint] using congrArg p.orbit h
    subst c
    congr 1
    cases b <;> cases d <;> simp_all [orientedPoint, Ne.symm (hf _)]
  · intro x
    have h : p.orbit x = p.orbit (p.orbit x).out := by
      exact (Quotient.out_eq _).symm
    rcases (p.orbit_eq _ _).1 h with h | h
    · exact ⟨(p.orbit x, false), h.symm⟩
    · exact ⟨(p.orbit x, true), h.symm⟩

def orientationEquiv (hf : ∀ x, p.flip x ≠ x) : p.Orbit × Bool ≃ X :=
  Equiv.ofBijective p.orientedPoint (p.orientedPoint_bijective hf)

theorem card_eq_twice [Finite X] (hf : ∀ x, p.flip x ≠ x) :
    Nat.card X = Nat.card p.Orbit * 2 := by
  rw [← Nat.card_congr (p.orientationEquiv hf), Nat.card_prod]
  simp

end Pairing

/-- A genuine set of signed points: the negative of a point is distinct from it. -/
structure SignedSet (X : Type*) extends Pairing X where
  fixedPointFree : ∀ x, flip x ≠ x

namespace SignedSet
variable {X Y : Type*} (s : SignedSet X) (t : SignedSet Y)

/-- Real functions with the source's relation `v(-x) = -v(x)`. -/
def space : Submodule ℝ (X → ℝ) where
  carrier := {f | ∀ x, f (s.flip x) = -f x}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg x; simpa only [Pi.add_apply, hf x, hg x] using (neg_add (f x) (g x)).symm
  smul_mem' := by intro a f hf x; simp [hf x]

abbrev Space := s.space

@[simp] theorem negative_apply (v : s.Space) (x : X) :
    v.val (s.flip x) = -v.val x := v.property x

/-- The signed vector attached to a point, with coefficient one at that point. -/
def delta (x : X) : s.Space := ⟨fun y =>
    (if y = x then 1 else 0) - (if y = s.flip x then 1 else 0), by
  intro y
  have h₁ : s.flip y = x ↔ y = s.flip x := by
    constructor
    · intro h; rw [← h, s.involutive]
    · intro h; rw [h, s.involutive]
  have h₂ : s.flip y = s.flip x ↔ y = x := s.flip.injective.eq_iff
  simp only [h₁, h₂]
  ring⟩

@[simp] theorem delta_apply (x y : X) :
    (s.delta x).val y = (if y = x then 1 else 0) -
      (if y = s.flip x then 1 else 0) := rfl

@[simp] theorem delta_self (x : X) : (s.delta x).val x = 1 := by
  simp [Ne.symm (s.fixedPointFree x)]

@[simp] theorem delta_flip (x : X) : s.delta (s.flip x) = -s.delta x := by
  apply Subtype.ext
  funext y
  simp only [delta_apply, s.involutive x, Submodule.coe_neg, Pi.neg_apply]
  ring

theorem delta_injective : Function.Injective s.delta := by
  intro x y h
  have he := congrArg (fun v : s.Space => v.val x) h
  by_contra hxy
  simp only [delta_self, delta_apply, if_neg hxy, zero_sub] at he
  split_ifs at he <;> norm_num at he

/-- Pullback by the inverse permutation, so vectors are transported forward. -/
def transport (e : X ≃ Y) (he : ∀ x, e (s.flip x) = t.flip (e x)) :
    s.Space ≃ₗ[ℝ] t.Space where
  toFun f := ⟨fun y => f.val (e.symm y), by
    intro y
    have h : e.symm (t.flip y) = s.flip (e.symm y) := by
      apply e.injective
      simp [he]
    change f.val (e.symm (t.flip y)) = -f.val (e.symm y)
    rw [h, s.negative_apply]⟩
  invFun f := ⟨fun x => f.val (e x), by
    intro x
    change f.val (e (s.flip x)) = -f.val (e x)
    rw [he, t.negative_apply]⟩
  left_inv f := by apply Subtype.ext; funext x; exact congrArg f.val (e.symm_apply_apply x)
  right_inv f := by apply Subtype.ext; funext y; exact congrArg f.val (e.apply_symm_apply y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem transport_apply (e : X ≃ Y)
    (he : ∀ x, e (s.flip x) = t.flip (e x)) (f : s.Space) (y : Y) :
    (s.transport t e he f).val y = f.val (e.symm y) := rfl

@[simp] theorem transport_delta (e : X ≃ Y)
    (he : ∀ x, e (s.flip x) = t.flip (e x)) (x : X) :
    s.transport t e he (s.delta x) = t.delta (e x) := by
  apply Subtype.ext
  funext y
  simp only [transport_apply, delta_apply]
  rw [show e.symm y = x ↔ y = e x from e.symm_apply_eq,
    show e.symm y = s.flip x ↔ y = e (s.flip x) from e.symm_apply_eq, he]

theorem transport_eq_refl_iff (e : Equiv.Perm X)
    (he : ∀ x, e (s.flip x) = s.flip (e x)) :
    s.transport s e he = LinearEquiv.refl ℝ s.Space ↔ e = Equiv.refl X := by
  constructor
  · intro h
    apply Equiv.ext
    intro x
    apply s.delta_injective
    have hv := congrArg (fun a : s.Space ≃ₗ[ℝ] s.Space => a (s.delta x)) h
    simpa only [transport_delta, LinearEquiv.refl_apply, Equiv.refl_apply] using hv
  · intro h
    subst e
    rfl

/-- Evaluation on one representative of each pair is a linear coordinate system. -/
def coordinateEquiv : s.Space ≃ₗ[ℝ] (s.toPairing.Orbit → ℝ) where
  toFun v a := v.val a.out
  invFun f := ⟨fun x => if x = (s.toPairing.orbit x).out then
      f (s.toPairing.orbit x) else -f (s.toPairing.orbit x), by
    intro x
    change (if s.flip x = (s.toPairing.orbit (s.flip x)).out then
        f (s.toPairing.orbit (s.flip x)) else -f (s.toPairing.orbit (s.flip x))) =
      -(if x = (s.toPairing.orbit x).out then
        f (s.toPairing.orbit x) else -f (s.toPairing.orbit x))
    rw [s.toPairing.orbit_flip]
    generalize hq : s.toPairing.orbit x = q
    have h : s.toPairing.orbit x = s.toPairing.orbit q.out :=
      hq.trans (Quotient.out_eq q).symm
    rcases (s.toPairing.orbit_eq _ _).1 h with h | h
    · simp [h, s.fixedPointFree q.out]
    · simp [h, s.involutive q.out, s.fixedPointFree q.out]⟩
  left_inv v := by
    apply Subtype.ext
    funext x
    change (if x = (s.toPairing.orbit x).out then
      v.val (s.toPairing.orbit x).out else -v.val (s.toPairing.orbit x).out) = v.val x
    split_ifs with h
    · exact congrArg v.val h.symm
    · have hx : s.toPairing.orbit x = s.toPairing.orbit (s.toPairing.orbit x).out :=
        (Quotient.out_eq _).symm
      have hx' := ((s.toPairing.orbit_eq _ _).1 hx).resolve_left h
      exact (s.negative_apply v _).symm.trans (congrArg v.val hx'.symm)
  right_inv f := by
    funext a
    change (if a.out = (s.toPairing.orbit a.out).out then
      f (s.toPairing.orbit a.out) else -f (s.toPairing.orbit a.out)) = f a
    rw [show s.toPairing.orbit a.out = a from Quotient.out_eq a]
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem coordinateEquiv_apply (v : s.Space) (a : s.toPairing.Orbit) :
    s.coordinateEquiv v a = v.val a.out := rfl

instance finiteDimensional [Finite X] : FiniteDimensional ℝ s.Space := by
  let := Fintype.ofFinite X
  exact inferInstanceAs (FiniteDimensional ℝ s.space)

theorem finrank_eq [Finite X] : Module.finrank ℝ s.Space = Nat.card s.toPairing.Orbit := by
  let := Fintype.ofFinite s.toPairing.Orbit
  rw [s.coordinateEquiv.finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]

theorem twice_finrank [Finite X] : Module.finrank ℝ s.Space * 2 = Nat.card X := by
  rw [s.finrank_eq]
  exact (s.toPairing.card_eq_twice s.fixedPointFree).symm

/-- A basis, chosen from the signed vectors, indexed by the unsigned pairs. -/
def basis [Finite X] : Module.Basis s.toPairing.Orbit ℝ s.Space := by
  let := Fintype.ofFinite s.toPairing.Orbit
  exact (Pi.basisFun ℝ s.toPairing.Orbit).map s.coordinateEquiv.symm

@[simp] theorem basis_eq_delta [Finite X] (a : s.toPairing.Orbit) :
    s.basis a = s.delta a.out := by
  let := Fintype.ofFinite s.toPairing.Orbit
  apply s.coordinateEquiv.injective
  funext b
  change s.coordinateEquiv (s.coordinateEquiv.symm ((Pi.basisFun ℝ _) a)) b = _
  rw [s.coordinateEquiv.apply_symm_apply]
  simp only [Pi.basisFun_apply, Pi.single_apply, coordinateEquiv_apply, delta_apply]
  by_cases hab : a = b
  · subst b
    simp [Ne.symm (s.fixedPointFree a.out)]
  · have h₁ : b.out ≠ a.out := by
      intro h
      apply hab
      have := congrArg s.toPairing.orbit h
      simpa only [Pairing.orbit, Quotient.out_eq] using this.symm
    have h₂ : b.out ≠ s.flip a.out := by
      intro h
      apply hab
      have := congrArg s.toPairing.orbit h
      rw [s.toPairing.orbit_flip] at this
      exact (Quotient.out_eq a).symm.trans (this.symm.trans (Quotient.out_eq b))
    simp [Ne.symm hab, h₁, h₂]

/-- The orthonormal normalization: one half of the sum over all signed points. -/
def form [Fintype X] : LinearMap.BilinForm ℝ s.Space where
  toFun v :=
    { toFun := fun w => (1 / 2 : ℝ) * ∑ x, v.val x * w.val x
      map_add' := by intro v w; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by intro a w; simp [Finset.mul_sum, mul_left_comm] }
  map_add' := by
    intro v w
    ext u
    simp [add_mul, Finset.sum_add_distrib, mul_add]
  map_smul' := by
    intro a v
    ext w
    simp [Finset.mul_sum, mul_assoc, mul_left_comm]

@[simp] theorem form_apply [Fintype X] (v w : s.Space) :
    s.form v w = (1 / 2 : ℝ) * ∑ x, v.val x * w.val x := rfl

theorem form_symmetric [Fintype X] (v w : s.Space) : s.form v w = s.form w v := by
  simp only [form_apply, mul_comm]

theorem form_nonneg [Fintype X] (v : s.Space) : 0 ≤ s.form v v :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ => mul_self_nonneg (v.val x))

theorem form_pos [Fintype X] (v : s.Space) (hv : v ≠ 0) : 0 < s.form v v := by
  apply mul_pos (by norm_num : (0 : ℝ) < 1 / 2)
  apply (Finset.sum_pos_iff_of_nonneg (fun x _ => mul_self_nonneg (v.val x))).2
  have hx : ∃ x, v.val x ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    apply Subtype.ext
    exact funext h
  obtain ⟨x, hx⟩ := hx
  exact ⟨x, Finset.mem_univ _, mul_self_pos.2 hx⟩

theorem transport_isometry [Fintype X] [Fintype Y] (e : X ≃ Y)
    (he : ∀ x, e (s.flip x) = t.flip (e x)) (v w : s.Space) :
    t.form (s.transport t e he v) (s.transport t e he w) = s.form v w := by
  simp only [form_apply, transport_apply]
  rw [e.symm.sum_comp (fun x => v.val x * w.val x)]

/-- Pairing against a signed vector evaluates the corresponding coordinate. -/
theorem form_delta [Fintype X] (x : X) (v : s.Space) :
    s.form (s.delta x) v = v.val x := by
  simp only [form_apply, delta_apply, sub_mul, Finset.sum_sub_distrib, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true, negative_apply]
  ring

theorem basis_orthonormal [Fintype X] (a b : s.toPairing.Orbit) :
    s.form (s.basis a) (s.basis b) = if a = b then 1 else 0 := by
  rw [basis_eq_delta, form_delta]
  have h := congrFun (congrArg s.coordinateEquiv (s.basis_eq_delta b)) a
  let := Fintype.ofFinite s.toPairing.Orbit
  change s.coordinateEquiv (s.coordinateEquiv.symm ((Pi.basisFun ℝ _) b)) a =
    (s.delta b.out).val a.out at h
  rw [s.coordinateEquiv.apply_symm_apply] at h
  rw [basis_eq_delta, ← h, Pi.basisFun_apply, Pi.single_apply]

/-- Every commuting permutation acts linearly on the signed module. -/
def representation {G : Type*} [Group G] (ρ : G →* Equiv.Perm X)
    (hρ : ∀ g x, ρ g (s.flip x) = s.flip (ρ g x)) :
    Representation ℝ G s.Space where
  toFun g := (s.transport s (ρ g) (hρ g)).toLinearMap
  map_one' := by
    ext v x
    change v.val ((ρ 1).symm x) = v.val x
    rw [map_one]
    rfl
  map_mul' g h := by
    ext v x
    change v.val ((ρ (g * h)).symm x) = v.val ((ρ h).symm ((ρ g).symm x))
    rw [map_mul]
    rfl

@[simp] theorem representation_delta {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (hρ : ∀ g x, ρ g (s.flip x) = s.flip (ρ g x))
    (g : G) (x : X) : s.representation ρ hρ g (s.delta x) = s.delta (ρ g x) :=
  s.transport_delta s (ρ g) (hρ g) x

theorem representation_kernel_iff {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (hρ : ∀ g x, ρ g (s.flip x) = s.flip (ρ g x)) (g : G) :
    s.representation ρ hρ g = 1 ↔ ρ g = 1 := by
  constructor
  · intro h
    apply Equiv.ext
    intro x
    apply s.delta_injective
    have hv := congrArg (fun f : Module.End ℝ s.Space => f (s.delta x)) h
    simpa only [representation_delta, Module.End.one_apply, Equiv.Perm.one_apply] using hv
  · intro h
    ext v x
    change v.val ((ρ g).symm x) = v.val x
    rw [h]
    rfl

theorem representation_monomial [Finite X] {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (hρ : ∀ g x, ρ g (s.flip x) = s.flip (ρ g x))
    (g : G) (a : s.toPairing.Orbit) :
    ∃ b, s.representation ρ hρ g (s.basis a) = s.basis b ∨
      s.representation ρ hρ g (s.basis a) = -s.basis b := by
  refine ⟨s.toPairing.orbit (ρ g a.out), ?_⟩
  simp only [basis_eq_delta, representation_delta]
  have hx : s.toPairing.orbit (ρ g a.out) =
      s.toPairing.orbit (s.toPairing.orbit (ρ g a.out)).out := (Quotient.out_eq _).symm
  rcases (s.toPairing.orbit_eq _ _).1 hx with h | h
  · exact Or.inl (congrArg s.delta h)
  · exact Or.inr ((congrArg s.delta h).trans (s.delta_flip _))

theorem flip_transport (v : s.Space) :
    s.transport s s.flip (fun _ => rfl) v = -v := by
  apply Subtype.ext
  funext x
  change v.val (s.flip.symm x) = -v.val x
  have h : s.flip.symm x = s.flip x := by
    apply s.flip.injective
    rw [s.flip.apply_symm_apply, s.involutive x]
  rw [h, s.negative_apply]

end SignedSet
namespace Pairing
variable {X : Type*} (p : Pairing X) (z : SignedSet X)

/-- First identify the two `k`-related points; the sign involution descends.
The separation condition is exactly that the sign has no fixed orbit. -/
def signedQuotient (hcomm : ∀ x, z.flip (p.flip x) = p.flip (z.flip x))
    (hsep : ∀ x, z.flip x ≠ p.flip x) : SignedSet p.Orbit where
  flip := p.transport p z.flip hcomm
  involutive := by
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      change p.orbit (z.flip (z.flip x)) = p.orbit x
      rw [z.involutive x]
  fixedPointFree := by
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      intro h
      change p.orbit (z.flip x) = p.orbit x at h
      rcases (p.orbit_eq _ _).1 h with h | h
      · exact z.fixedPointFree x h
      · exact hsep x h

@[simp] theorem signedQuotient_flip_orbit
    (hcomm : ∀ x, z.flip (p.flip x) = p.flip (z.flip x))
    (hsep : ∀ x, z.flip x ≠ p.flip x) (x : X) :
    (p.signedQuotient z hcomm hsep).flip (p.orbit x) = p.orbit (z.flip x) := rfl

/-- The induced permutation representation on the actual two-point orbits. -/
def orbitRepresentation {G : Type*} [Group G] (ρ : G →* Equiv.Perm X)
    (hρ : ∀ g x, ρ g (p.flip x) = p.flip (ρ g x)) : G →* Equiv.Perm p.Orbit where
  toFun g := p.transport p (ρ g) (hρ g)
  map_one' := by
    apply Equiv.ext
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      change p.orbit (ρ 1 x) = p.orbit x
      rw [map_one]
      rfl
  map_mul' g h := by
    apply Equiv.ext
    intro a
    induction a using Quotient.inductionOn with
    | h x =>
      change p.orbit (ρ (g * h) x) = p.orbit (ρ g (ρ h x))
      rw [map_mul]
      rfl

@[simp] theorem orbitRepresentation_apply {G : Type*} [Group G]
    (ρ : G →* Equiv.Perm X) (hρ : ∀ g x, ρ g (p.flip x) = p.flip (ρ g x))
    (g : G) (x : X) : p.orbitRepresentation ρ hρ g (p.orbit x) = p.orbit (ρ g x) := rfl

theorem orbitRepresentation_commutes {G : Type*} [Group G]
    (hcomm : ∀ x, z.flip (p.flip x) = p.flip (z.flip x))
    (hsep : ∀ x, z.flip x ≠ p.flip x)
    (ρ : G →* Equiv.Perm X) (hk : ∀ g x, ρ g (p.flip x) = p.flip (ρ g x))
    (hz : ∀ g x, ρ g (z.flip x) = z.flip (ρ g x)) (g : G) (a : p.Orbit) :
    p.orbitRepresentation ρ hk g ((p.signedQuotient z hcomm hsep).flip a) =
      (p.signedQuotient z hcomm hsep).flip (p.orbitRepresentation ρ hk g a) := by
  induction a using Quotient.inductionOn with
  | h x =>
    change p.orbit (ρ g (z.flip x)) = p.orbit (z.flip (ρ g x))
    rw [hz]

/-- The signed representation after identifying the `k`-orbits. -/
def signedRepresentation {G : Type*} [Group G]
    (hcomm : ∀ x, z.flip (p.flip x) = p.flip (z.flip x))
    (hsep : ∀ x, z.flip x ≠ p.flip x)
    (ρ : G →* Equiv.Perm X) (hk : ∀ g x, ρ g (p.flip x) = p.flip (ρ g x))
    (hz : ∀ g x, ρ g (z.flip x) = z.flip (ρ g x)) :
    Representation ℝ G (p.signedQuotient z hcomm hsep).Space :=
  (p.signedQuotient z hcomm hsep).representation (p.orbitRepresentation ρ hk)
    (p.orbitRepresentation_commutes z hcomm hsep ρ hk hz)

/-- Triviality means fixing each `k`-orbit, with no permitted sign reversal. -/
theorem signedRepresentation_kernel_iff {G : Type*} [Group G]
    (hcomm : ∀ x, z.flip (p.flip x) = p.flip (z.flip x))
    (hsep : ∀ x, z.flip x ≠ p.flip x)
    (ρ : G →* Equiv.Perm X) (hk : ∀ g x, ρ g (p.flip x) = p.flip (ρ g x))
    (hz : ∀ g x, ρ g (z.flip x) = z.flip (ρ g x)) (g : G) :
    p.signedRepresentation z hcomm hsep ρ hk hz g = 1 ↔
      ∀ x, ρ g x = x ∨ ρ g x = p.flip x := by
  change (p.signedQuotient z hcomm hsep).representation _ _ g = 1 ↔ _
  rw [SignedSet.representation_kernel_iff]
  constructor
  · intro h x
    apply (p.orbit_eq _ _).1
    exact congrArg (fun e : Equiv.Perm p.Orbit => e (p.orbit x)) h
  · intro h
    apply Equiv.ext
    intro a
    induction a using Quotient.inductionOn with
    | h x => exact (p.orbit_eq _ _).2 (h x)

end Pairing
end Sporadic.Monster.Construction.TrialitySpin.SignedModules
