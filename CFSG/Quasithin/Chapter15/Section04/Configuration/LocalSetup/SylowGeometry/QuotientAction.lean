module
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.Frattini.PGroup
public import Theory.PGroupCore
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases
public import Theory.GroupAction.OrderNineFactorExchange
public import CFSG.Quasithin.Chapter1.Section03.Basic

/-!
# The irreducible quotient action for the moved factor product

The embedding input in 15.4.20 concerns `X`, acted on by the larger
contrary Sylow subgroup `U`; it is not a membership assertion about
`K=⟨X^I₀⟩`. On actual order-nine coordinates, independent inversion and
interchange imply that every invariant subgroup is trivial or the whole
group. The proof extracts the two coordinate axes and uses the three
possible values of each coordinate.

The coordinate isomorphism also proves that the quotient is elementary
abelian, has order nine, and has trivial Frattini subgroup. Transport through
the canonical Frattini quotient proves irreducibility for its actual induced
action. The final adapter uses conjugation on `X`, the literal `X/O₂(X)`,
and the Frattini quotient of that group. The factor-exchange adapter uses
the canonical Xi definition and permits either signed interchange; the
commutator of the two actors supplies inversion inside the Frattini subgroup.
The actual factor and actor witnesses must still be supplied from the full
15.4.12 quotient and factor-permutation data. This module does not claim any
classification alternative.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Definition 1.3.1 (p.508), Proposition 1.3.4 (p.509), and the proof of
Lemma 15.4.20 (p.1164).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup
open Subgroup

private theorem signed_swap_invariant (D : Subgroup (Multiplicative (ZMod 3 × ZMod 3)))
    (hflip : ∀ a b : ZMod 3, Multiplicative.ofAdd (a,b) ∈ D →
      Multiplicative.ofAdd (-a,b) ∈ D)
    (hswap : ∀ a b : ZMod 3, Multiplicative.ofAdd (a,b) ∈ D →
      Multiplicative.ofAdd (b,a) ∈ D) : D = ⊥ ∨ D = ⊤ := by
  classical
  by_cases hD : D = ⊥
  · exact Or.inl hD
  right
  have hproj (a b : ZMod 3) (hv : Multiplicative.ofAdd (a,b) ∈ D) :
      Multiplicative.ofAdd (a,0) ∈ D := by
    have h := D.mul_mem (D.inv_mem hv) (hflip a b hv)
    change Multiplicative.ofAdd (-a + -a, -b + b) ∈ D at h
    have he : (-a + -a, -b + b) = (a,0) :=
      (by decide : ∀ a b : ZMod 3, (-a + -a, -b + b) = (a,0)) a b
    rwa [he] at h
  have hvalues (a : ZMod 3) : a = 0 ∨ a = 1 ∨ a = -1 := by
    revert a
    decide
  have hgen (a : ZMod 3) (ha : a ≠ 0) (h : Multiplicative.ofAdd (a,0) ∈ D) :
      Multiplicative.ofAdd ((1 : ZMod 3),0) ∈ D := by
    rcases hvalues a with hzero | hone | hneg
    · exact (ha hzero).elim
    · simpa only [hone] using h
    · have hi := D.inv_mem h
      change Multiplicative.ofAdd (-a, -(0 : ZMod 3)) ∈ D at hi
      simpa only [hneg, neg_neg, neg_zero] using hi
  have hex : ∃ v ∈ D, v ≠ 1 := by
    by_contra h
    push Not at h
    exact hD (eq_bot_iff.mpr fun v hv => h v hv)
  obtain ⟨v, hv, hne⟩ := hex
  let a := v.toAdd.1
  let b := v.toAdd.2
  have hv' : Multiplicative.ofAdd (a,b) ∈ D := hv
  have hab : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (by change Multiplicative.ofAdd (a,b) = 1; rw [h.1,h.2]; rfl)
  have h10 : Multiplicative.ofAdd ((1 : ZMod 3),0) ∈ D := by
    rcases hab with ha | hb
    · exact hgen a ha (hproj a b hv')
    · exact hgen b hb (hproj b a (hswap a b hv'))
  have hx0 (x : ZMod 3) : Multiplicative.ofAdd (x,0) ∈ D := by
    rcases hvalues x with hzero | hone | hneg
    · rw [hzero]; exact D.one_mem
    · simpa only [hone] using h10
    · have hi := D.inv_mem h10
      change Multiplicative.ofAdd (-(1 : ZMod 3), -(0 : ZMod 3)) ∈ D at hi
      simpa only [hneg, neg_zero] using hi
  apply top_unique
  intro w _
  have h := D.mul_mem (hx0 w.toAdd.1) (hswap _ _ (hx0 w.toAdd.2))
  change Multiplicative.ofAdd (w.toAdd.1 + 0, 0 + w.toAdd.2) ∈ D at h
  simpa using h

/-- Independent inversion and interchange in the actual order-nine quotient
force irreducibility. The conclusion is about every invariant subgroup,
not a dimension or family tag. -/
theorem irreducible_order_nine_action {A U : Type*} [Group A] [Group U]
    (α : U →* MulAut A) (e : A ≃* Multiplicative (ZMod 3 × ZMod 3))
    (a b : U)
    (hinvert : ∀ v : A, e (α a v) = Multiplicative.ofAdd (-(e v).toAdd.1, (e v).toAdd.2))
    (hswap : ∀ v : A, e (α b v) = Multiplicative.ofAdd ((e v).toAdd.2, (e v).toAdd.1)) :
    ∀ D : Subgroup A, (∀ u : U, ∀ v ∈ D, α u v ∈ D) → D = ⊥ ∨ D = ⊤ := by
  intro D hD
  have hf : ∀ x y : ZMod 3, Multiplicative.ofAdd (x,y) ∈ D.map e.toMonoidHom →
      Multiplicative.ofAdd (-x,y) ∈ D.map e.toMonoidHom := by
    intro x y hv
    obtain ⟨v, hv, he⟩ := hv
    refine ⟨α a v, hD a v hv, ?_⟩
    change e (α a v) = _
    rw [hinvert, show e v = Multiplicative.ofAdd (x,y) from he]
    rfl
  have hs : ∀ x y : ZMod 3, Multiplicative.ofAdd (x,y) ∈ D.map e.toMonoidHom →
      Multiplicative.ofAdd (y,x) ∈ D.map e.toMonoidHom := by
    intro x y hv
    obtain ⟨v, hv, he⟩ := hv
    refine ⟨α b v, hD b v hv, ?_⟩
    change e (α b v) = _
    rw [hswap, show e v = Multiplicative.ofAdd (x,y) from he]
    rfl
  rcases signed_swap_invariant (D.map e.toMonoidHom) hf hs with hb | ht
  · exact Or.inl ((D.map_eq_bot_iff_of_injective e.injective).mp hb)
  · right
    apply top_unique
    intro v _
    have hv : e v ∈ D.map e.toMonoidHom := ht ▸ mem_top _
    obtain ⟨w, hw, hwe⟩ := hv
    exact e.injective hwe ▸ hw

/-- An actual order-nine coordinate isomorphism supplies the elementary
abelian and trivial-Frattini facts needed by Definition 1.3.1. -/
theorem order_nine_quotient_structure {A : Type*} [Group A]
    (e : A ≃* Multiplicative (ZMod 3 × ZMod 3)) :
    IsElementaryAbelian 3 A ∧ Nat.card A = 9 ∧ frattini A = ⊥ := by
  let : Finite A := Finite.of_injective e e.injective
  let hA : IsElementaryAbelian 3 A := {
    toIsMulCommutative := ⟨⟨fun x y => e.injective (by simp only [map_mul, mul_comm])⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      apply e.injective
      rw [map_pow, map_one]
      exact (by decide : ∀ v : Multiplicative (ZMod 3 × ZMod 3), v ^ 3 = 1) (e x) }
  let : Fact (IsPGroup 3 A) := ⟨IsElementaryAbelian.isPGroup 3 A⟩
  exact ⟨hA, by rw [Nat.card_congr e.toEquiv]; simp,
    frattini_eq_bot_of_isElementaryAbelian (p := 3)⟩

/-- Signed coordinates also prove irreducibility on the literal Frattini
quotient with its induced action. No replacement by an unrelated vector space
or unconnected group-family tag is made. -/
theorem irreducible_order_nine_frattini_action {A U : Type*} [Group A] [Group U]
    (α : U →* MulAut A) (e : A ≃* Multiplicative (ZMod 3 × ZMod 3))
    (a b : U)
    (hinvert : ∀ v : A, e (α a v) = Multiplicative.ofAdd (-(e v).toAdd.1, (e v).toAdd.2))
    (hswap : ∀ v : A, e (α b v) = Multiplicative.ofAdd ((e v).toAdd.2, (e v).toAdd.1)) :
    ∀ D : Subgroup (A ⧸ frattini A),
      (∀ u : U, ∀ v ∈ D, (quotientAut (frattini A) (α u)) v ∈ D) → D = ⊥ ∨ D = ⊤ := by
  let : Finite A := Finite.of_injective e e.injective
  let : IsElementaryAbelian 3 A := (order_nine_quotient_structure e).1
  let : Fact (IsPGroup 3 A) := ⟨IsElementaryAbelian.isPGroup 3 A⟩
  let f := frattiniQuotientEquivOfIsElementaryAbelian (R := A) (p := 3)
  let β := (quotientAut (frattini A)).comp α
  have hf (u : U) (v : A ⧸ frattini A) : f (β u v) = α u (f v) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini A) v
    change f (quotientAut (frattini A) (α u) (QuotientGroup.mk' (frattini A) x)) = _
    rw [quotientAut_apply_mk, frattiniQuotientEquivOfIsElementaryAbelian_mk',
      frattiniQuotientEquivOfIsElementaryAbelian_mk']
  exact irreducible_order_nine_action β (f.trans e) a b
    (fun v => by change e (f (β a v)) = _; rw [hf]; exact hinvert (f v))
    (fun v => by change e (f (β b v)) = _; rw [hf]; exact hswap (f v))

/-- The precise quotient/action clauses required for `X` under the contrary
Sylow group `U`. Both actions are induced by conjugation on `X`, then on its
two-core quotient and the latter's Frattini quotient. The raw signed-coordinate
witnesses still have to be realized from the 15.4.12 factor quotient. -/
theorem contrary_X_quotient_action {G : Type*} [Group G]
    (X U : Subgroup G) (hn : U ≤ normalizer (X : Set G))
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (a b : U)
    (hinvert : ∀ v : X ⧸ pCore 2 X,
      e (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) v) =
        Multiplicative.ofAdd (-(e v).toAdd.1, (e v).toAdd.2))
    (hswap : ∀ v : X ⧸ pCore 2 X,
      e (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn b)) v) =
        Multiplicative.ofAdd ((e v).toAdd.2, (e v).toAdd.1)) :
    IsElementaryAbelian 3 (X ⧸ pCore 2 X) ∧ Nat.card (X ⧸ pCore 2 X) = 9 ∧
      ∀ D : Subgroup ((X ⧸ pCore 2 X) ⧸ frattini (X ⧸ pCore 2 X)),
        (∀ u : U, ∀ v ∈ D,
          quotientAut (frattini (X ⧸ pCore 2 X))
            (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn u))) v ∈ D) →
          D = ⊥ ∨ D = ⊤ := by
  let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
  have hs := order_nine_quotient_structure e
  exact ⟨hs.1, hs.2.1, irreducible_order_nine_frattini_action α e a b hinvert hswap⟩

open scoped IsMulCommutative commutatorElement

/-- An independent inversion and a factor interchange force irreducibility on
the literal Frattini quotient; the interchanging actor may have order four. -/
theorem irreducible_frattini_of_factor_exchange {A U : Type*}
    [Group A] [Finite A] [IsMulCommutative A] [Group U]
    (α : U →* MulAut A) (A1 A2 : Subgroup A) (hgen : A1 ⊔ A2 = ⊤)
    (hcard1 : Nat.card A1 = 3) (hcard2 : Nat.card A2 = 3) (a b : U)
    (hinvert : ∀ x ∈ A1, α a x = x⁻¹)
    (hfix : ∀ x ∈ A2, α a x = x)
    (hexchange1 : A1.map (α b).toMonoidHom = A2)
    (hexchange2 : A2.map (α b).toMonoidHom = A1) :
    ∀ D : Subgroup (A ⧸ frattini A),
      (∀ u : U, ∀ v ∈ D, quotientAut (frattini A) (α u) v ∈ D) →
        D = ⊥ ∨ D = ⊤ := by
  intro D hD
  let q := QuotientGroup.mk' (frattini A)
  have hi : ∀ u : U, ∀ x ∈ D.comap q, α u x ∈ D.comap q := by
    intro u x hx
    change q (α u x) ∈ D
    simpa only [q, ← quotientAut_apply_mk] using hD u (q x) hx
  rcases OrderNineFactorExchange.irreducible_of_factor_exchange
    α A1 A2 hgen hcard1 hcard2 a b hinvert hfix hexchange1 hexchange2 (D.comap q) hi with hb | ht
  · left
    apply eq_bot_iff.mpr
    intro v hv
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini A) v
    have hx : x ∈ D.comap q := hv
    have hx1 : x = 1 := mem_bot.mp (hb ▸ hx)
    simp [hx1]
  · right
    apply top_unique
    intro v _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (frattini A) v
    exact (show x ∈ D.comap q from ht ▸ mem_top x)

/-- The explicit commutator belongs to the two-group's Frattini subgroup and
inverts the whole quotient. No pure-swap coordinates are required. -/
theorem frattini_inverter_of_factor_exchange {A U : Type*}
    [Group A] [IsMulCommutative A] [Group U] [Finite U]
    (hU : IsPGroup 2 U)
    (α : U →* MulAut A) (A1 A2 : Subgroup A) (hgen : A1 ⊔ A2 = ⊤)
    (a b : U) (hinvert : ∀ x ∈ A1, α a x = x⁻¹)
    (hfix : ∀ x ∈ A2, α a x = x)
    (hexchange1 : A1.map (α b).toMonoidHom = A2)
    (hexchange2 : A2.map (α b).toMonoidHom = A1) :
    ⁅a, b⁆ ∈ frattini U ∧ ∀ x : A, α ⁅a, b⁆ x = x⁻¹ := by
  let : Fact (IsPGroup 2 U) := ⟨hU⟩
  exact ⟨commutator_le_frattini_of_isPGroup (p := 2)
    (commutator_mem_commutator (mem_top a) (mem_top b)),
    OrderNineFactorExchange.commutator_inverts_of_factor_exchange
      α A1 A2 hgen a b hinvert hfix hexchange1 hexchange2⟩

/-- Construct the canonical Xi input for `X` under the contrary Sylow group
from its actual quotient factors and their inversion and exchange witnesses.
The local source assembly must construct those witnesses. -/
theorem contrary_X_mem_Xi_of_factor_exchange {G : Type*} [Group G] [Finite G]
    (X U : Subgroup G) (hn : U ≤ normalizer (X : Set G))
    (hperfect : IsPPerfect 2 X) (hH : X ⊔ U ∈ Chapter1.H G)
    (e : (X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3))
    (A1 A2 : Subgroup (X ⧸ pCore 2 X)) (hgen : A1 ⊔ A2 = ⊤)
    (hcard1 : Nat.card A1 = 3) (hcard2 : Nat.card A2 = 3) (a b : U)
    (hinvert : ∀ x ∈ A1,
      quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x⁻¹)
    (hfix : ∀ x ∈ A2,
      quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn a)) x = x)
    (hexchange1 : A1.map
      (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn b))).toMonoidHom = A2)
    (hexchange2 : A2.map
      (quotientAut (pCore 2 X) (X.normalizerMonoidHom (inclusion hn b))).toMonoidHom = A1) :
    X ∈ Chapter1.Xi G U := by
  have hs := order_nine_quotient_structure e
  let : IsElementaryAbelian 3 (X ⧸ pCore 2 X) := hs.1
  let α := (quotientAut (pCore 2 X)).comp (X.normalizerMonoidHom.comp (inclusion hn))
  refine ⟨hperfect, hn, hH, ⟨3, Nat.prime_three, by decide, Or.inl ⟨hs.1, hs.2.1⟩⟩, ?_⟩
  exact irreducible_frattini_of_factor_exchange α A1 A2 hgen hcard1 hcard2 a b
    hinvert hfix hexchange1 hexchange2


/-- The full factor action has noncommutative image: the inverting commutator
acts nontrivially on a factor of order three. In particular the image cannot
be cyclic. -/
theorem not_commutative_image_of_factor_exchange {A U : Type*}
    [Group A] [Finite A] [IsMulCommutative A] [Group U]
    (α : U →* MulAut A) (A1 A2 : Subgroup A) (hgen : A1 ⊔ A2 = ⊤)
    (hcard1 : Nat.card A1 = 3) (a b : U)
    (hinvert : ∀ x ∈ A1, α a x = x⁻¹) (hfix : ∀ x ∈ A2, α a x = x)
    (hexchange1 : A1.map (α b).toMonoidHom = A2)
    (hexchange2 : A2.map (α b).toMonoidHom = A1) :
    ¬ IsMulCommutative α.range := by
  intro hcomm
  let : IsMulCommutative α.range := hcomm
  have hab : α a * α b = α b * α a :=
    congrArg Subtype.val (mul_comm (⟨α a, ⟨a,rfl⟩⟩ : α.range) (⟨α b, ⟨b,rfl⟩⟩ : α.range))
  have hc : α ⁅a,b⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, hab]
    simp only [mul_assoc, mul_inv_cancel, one_mul]
  have hex : ∃ x ∈ A1, x ≠ 1 := by
    by_contra h
    push Not at h
    have he : A1 = ⊥ := le_antisymm (fun x hx => show x ∈ (⊥ : Subgroup A) from h x hx) bot_le
    have hcard := hcard1
    rw [he, card_bot] at hcard
    omega
  obtain ⟨x,hx,hxne⟩ := hex
  have hinv := OrderNineFactorExchange.commutator_inverts_of_factor_exchange
    α A1 A2 hgen a b hinvert hfix hexchange1 hexchange2 x
  rw [hc] at hinv
  have hx2 : x*x = 1 := eq_inv_iff_mul_eq_one.mp hinv
  have hx3 : x ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨x,hx⟩ : A1))
    rw [hcard1] at hh
    exact congrArg Subtype.val hh
  exact hxne (by simpa only [pow_succ, pow_zero, one_mul, hx2] using hx3)


end CFSG.Quasithin.Chapter15.Section04.LocalSetup
