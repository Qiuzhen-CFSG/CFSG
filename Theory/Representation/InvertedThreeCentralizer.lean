module
public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Tactic

/-!
# Involutions centralizing an inverted order-three operator

Let an F₂ vector space X have order sixteen. If t satisfies t²+t+1=0
and the involution b inverts t, the b-fixed space W has order four and
X=W⊕tW. Thus restriction to W determines every endomorphism commuting
with t. A nonidentity involution a commuting with t and b restricts to a
nonidentity involution of W. In dimension two over F₂, its commuting
involutions are precisely one and itself, and it has two fixed vectors.

The proof constructs the direct sum using v=x+bx and u=x+tv. The final
two-dimensional matrix assertions are checked by kernel reduction over all
sixteen matrices. This finite calculation supplies the action-theoretic part
of S=AᵢS₀ in Stellmacher (1.6), journal p. 18; see
`refs/latex/stellmacher-n-group.tex`. It has no ambient minimality hypotheses.
-/

namespace Representation

private theorem charTwo_add_self {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (x : X) : x + x = 0 := by
  have h := @two_smul (ZMod 2) X _ _ _ x
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, zero_smul] at h
  exact h.symm

private theorem fixedInvolution_decomposition
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) :
    ∀ x : X, ∃ u v : X, b u = u ∧ b v = v ∧ x = u + t v := by
  have hquad (x : X) : t (t x) + t x + x = 0 := by
    exact LinearMap.congr_fun ht x
  have hbb (x : X) : b (b x) = x := by
    exact LinearMap.congr_fun hb x
  have hbt' (x : X) : b (t x) = t (t (b x)) := by
    exact LinearMap.congr_fun hbt x
  have hsum (x : X) : t (t x) + t x = x := by
    have h := hquad x
    have hzero := charTwo_add_self x
    exact add_right_cancel (show (t (t x) + t x) + x = x + x by rw [h, hzero])
  intro x
  let v := x + b x
  have hv : b v = v := by simp [v, hbb, add_comm]
  refine ⟨x + t v, v, ?_, hv, ?_⟩
  · rw [map_add, hbt', hv]
    have hh : t (t v) = v + t v := by
      apply add_right_cancel (b := t v)
      rw [hsum]
      simp only [add_assoc, charTwo_add_self, add_zero]
    rw [hh]
    dsimp [v]
    have hxx := charTwo_add_self (b x)
    calc
      b x + (x + b x + t (x + b x)) =
          x + t (x + b x) + (b x + b x) := by abel
      _ = x + t (x + b x) := by rw [hxx, add_zero]
  · rw [add_assoc, charTwo_add_self, add_zero]

private theorem fixedInvolution_card
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) (hX : Nat.card X = 16) :
    Nat.card (LinearMap.ker (b - 1)) = 4 := by
  let W := LinearMap.ker (b - 1)
  have hW (x : W) : b (x : X) = x := by
    have hx := x.property
    change b (x : X) - (x : X) = 0 at hx
    exact sub_eq_zero.mp hx
  let e : W × W →ₗ[ZMod 2] X :=
    { toFun := fun uv => (uv.1 : X) + t (uv.2 : X)
      map_add' := by intros; simp; abel
      map_smul' := by intros; simp }
  have heinj : Function.Injective e := by
    apply (injective_iff_map_eq_zero e.toAddMonoidHom).2
    rintro ⟨u, v⟩ huv
    have hquad : t (t (v : X)) + t (v : X) + (v : X) = 0 :=
      LinearMap.congr_fun ht v
    have hbtv : b (t (v : X)) = t (t (v : X)) := by
      have h := LinearMap.congr_fun hbt (v : X)
      change b (t (v : X)) = t (t (b (v : X))) at h
      simpa only [hW] using h
    have hbuv := congrArg b huv
    change b ((u : X) + t (v : X)) = b 0 at hbuv
    rw [map_add, map_zero, hW, hbtv] at hbuv
    change (u : X) + t (v : X) = 0 at huv
    have htu : t (v : X) = u := by
      exact add_left_cancel (show (u : X) + t (v : X) = (u : X) + u by
        rw [huv, charTwo_add_self])
    have htt : t (t (v : X)) = u := by
      exact add_left_cancel (show (u : X) + t (t (v : X)) = (u : X) + u by
        rw [hbuv, charTwo_add_self])
    have hvzero : (v : X) = 0 := by
      rw [htt, htu, charTwo_add_self, zero_add] at hquad
      exact hquad
    have huzero : (u : X) = 0 := by simpa [hvzero] using htu.symm
    exact Prod.ext (Subtype.ext huzero) (Subtype.ext hvzero)
  have hesurj : Function.Surjective e := by
    intro x
    obtain ⟨u, v, hu, hv, hx⟩ := fixedInvolution_decomposition t b ht hb hbt x
    refine ⟨(⟨u, ?_⟩, ⟨v, ?_⟩), hx.symm⟩
    · change b u - u = 0
      rw [hu, sub_self]
    · change b v - v = 0
      rw [hv, sub_self]
  have hc := Nat.card_congr (Equiv.ofBijective e ⟨heinj, hesurj⟩)
  rw [Nat.card_prod, hX] at hc
  change Nat.card W = 4
  nlinarith

private theorem fixedInvolution_ext
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (t b a c : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b)
    (hat : a * t = t * a) (hct : c * t = t * c)
    (hac : ∀ x, b x = x → a x = c x) : a = c := by
  ext x
  obtain ⟨u, v, hu, hv, rfl⟩ := fixedInvolution_decomposition t b ht hb hbt x
  have hatv : a (t v) = t (a v) := LinearMap.congr_fun hat v
  have hctv : c (t v) = t (c v) := LinearMap.congr_fun hct v
  rw [map_add, map_add, hatv, hctv, hac u hu, hac v hv]

private theorem matrix_two_commuting_involutions :
    ∀ a c : Matrix (Fin 2) (Fin 2) (ZMod 2),
    a * a = 1 → c * c = 1 → a * c = c * a → a ≠ 1 → c = 1 ∨ c = a := by
  decide +kernel

private theorem matrix_two_involution_fixed_card :
    ∀ a : Matrix (Fin 2) (Fin 2) (ZMod 2),
    a * a = 1 → a ≠ 1 →
      Fintype.card {x : Fin 2 → ZMod 2 // a.mulVec x = x} = 2 := by
  decide +kernel

private def restrictFixed
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X]
    (b a : Module.End (ZMod 2) X) (hab : a * b = b * a) :
    Module.End (ZMod 2) (LinearMap.ker (b - 1)) where
  toFun x := ⟨a x, by
    change b (a (x : X)) - a (x : X) = 0
    have hx : b (x : X) = x := sub_eq_zero.mp x.property
    have h : a (b (x : X)) = b (a (x : X)) := LinearMap.congr_fun hab x
    rw [← h, hx, sub_self]⟩
  map_add' x y := Subtype.ext (a.map_add x y)
  map_smul' k x := Subtype.ext (a.map_smul k x)

public theorem invertedThree_cardSixteen_involution_centralizer
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (t b a : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) (hX : Nat.card X = 16)
    (ha : a * a = 1) (hane : a ≠ 1)
    (hat : a * t = t * a) (hab : a * b = b * a) :
    (∀ c : Module.End (ZMod 2) X, c * c = 1 →
      c * t = t * c → c * b = b * c → c * a = a * c → c = 1 ∨ c = a) ∧
    Nat.card {x : X // a x = x ∧ b x = x} = 2 := by
  classical
  let W := LinearMap.ker (b - 1)
  have hWcard : Nat.card W = 4 := fixedInvolution_card t b ht hb hbt hX
  have hdim : Module.finrank (ZMod 2) W = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hWcard
    norm_num at hWcard
    exact Nat.pow_right_injective (by omega : 1 < 2) hWcard
  let bas : Module.Basis (Fin 2) (ZMod 2) W :=
    Module.finBasisOfFinrankEq (ZMod 2) W hdim
  let m := LinearMap.toMatrixAlgEquiv bas
  let ar : Module.End (ZMod 2) W := restrictFixed b a hab
  have har : ar * ar = 1 := by
    ext x
    exact congrArg Subtype.val (show ar (ar x) = x from
      Subtype.ext (LinearMap.congr_fun ha (x : X)))
  have harne : ar ≠ 1 := by
    intro h
    apply hane
    apply fixedInvolution_ext t b a 1 ht hb hbt hat (by simp)
    intro x hx
    have hxW : x ∈ W := by change b x - x = 0; rw [hx, sub_self]
    exact congrArg Subtype.val (LinearMap.congr_fun h (⟨x, hxW⟩ : W))
  have hmane : m ar ≠ 1 := by
    intro h
    exact harne (m.injective (by simpa only [map_one] using h))
  have hma : m ar * m ar = 1 := by rw [← map_mul, har, map_one]
  constructor
  · intro c hc hct hcb hca
    let cr : Module.End (ZMod 2) W := restrictFixed b c hcb
    have hcr : cr * cr = 1 := by
      ext x
      exact LinearMap.congr_fun hc (x : X)
    have hcra : ar * cr = cr * ar := by
      ext x
      exact (LinearMap.congr_fun hca (x : X)).symm
    have hmc : m cr * m cr = 1 := by rw [← map_mul, hcr, map_one]
    have hmac : m ar * m cr = m cr * m ar := by rw [← map_mul, ← map_mul, hcra]
    rcases matrix_two_commuting_involutions (m ar) (m cr) hma hmc hmac hmane with h | h
    · left
      have hcrone : cr = 1 := m.injective (by simpa only [map_one] using h)
      apply fixedInvolution_ext t b c 1 ht hb hbt hct (by simp)
      intro x hx
      have hxW : x ∈ W := by change b x - x = 0; rw [hx, sub_self]
      exact congrArg Subtype.val (LinearMap.congr_fun hcrone (⟨x, hxW⟩ : W))
    · right
      have hcreq : cr = ar := m.injective h
      apply fixedInvolution_ext t b c a ht hb hbt hct hat
      intro x hx
      have hxW : x ∈ W := by change b x - x = 0; rw [hx, sub_self]
      exact congrArg Subtype.val (LinearMap.congr_fun hcreq (⟨x, hxW⟩ : W))
  · have hmm := matrix_two_involution_fixed_card (m ar) hma hmane
    let e1 : {x : X // a x = x ∧ b x = x} ≃ {w : W // ar w = w} :=
      { toFun := fun x => ⟨⟨x, by change b (x : X) - x = 0; rw [x.property.2, sub_self]⟩,
          Subtype.ext x.property.1⟩
        invFun := fun w => ⟨w, ⟨congrArg Subtype.val w.property,
          sub_eq_zero.mp w.val.property⟩⟩
        left_inv := by intro x; rfl
        right_inv := by intro w; rfl }
    have hcoord (w : W) : (m ar).mulVec (bas.equivFun w) = bas.equivFun (ar w) := by
      exact LinearMap.toMatrix_mulVec_repr bas bas ar w
    have hequiv (w : W) : ar w = w ↔ (m ar).mulVec (bas.equivFun w) = bas.equivFun w := by
      rw [hcoord]
      exact bas.equivFun.injective.eq_iff.symm
    let e2 := Equiv.subtypeEquiv (p := fun w : W => ar w = w)
      (q := fun x : Fin 2 → ZMod 2 => (m ar).mulVec x = x)
      bas.equivFun.toEquiv hequiv
    calc
      Nat.card {x : X // a x = x ∧ b x = x} =
          Nat.card {w : W // ar w = w} := Nat.card_congr e1
      _ = Nat.card {x : Fin 2 → ZMod 2 // (m ar).mulVec x = x} := Nat.card_congr e2
      _ = 2 := by rw [Nat.card_eq_fintype_card]; exact hmm

/-- An involution inverting the fixed-point-free order-three operator on a
sixteen-element F₂ vector space has exactly four fixed vectors. -/
public theorem invertedThree_cardSixteen_fixed_card_four
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (t b : Module.End (ZMod 2) X)
    (ht : t ^ 2 + t + 1 = 0) (hb : b * b = 1)
    (hbt : b * t = t ^ 2 * b) (hX : Nat.card X = 16) :
    Nat.card (LinearMap.ker (b - 1)) = 4 :=
  fixedInvolution_card t b ht hb hbt hX

end Representation
