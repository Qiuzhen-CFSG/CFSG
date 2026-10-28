module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextetCoreFactors
public import Theory.GroupTheory.TransvectionFixedCoset
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.FieldTheory.Finiteness

/-!
# Fixed cosets for the full sextet transvection action

The commutator character of each vector in V_z descends through the actual
hexacode quotient O₂(L_z)/V. Its kernel is the central involution line.
The orders 128 and 64 make the character map onto the binary dual hexacode.
Evaluation duality therefore corrects every central displacement by an
actual element of V_z, retaining the entire original action kernel.

NonFFSourceMathieuM24FixedCoset applies this to O₂(LT) and the original
centralizer closure in the fixed-subgroup step of Aschbacher–Smith 8.2.12,
printed p.722, refs/quasithin.pdf. The subsequent vanishing of the residual
centralizer is a separate requirement: the perfect sextet residual does
not contain a Sylow two-subgroup of M24.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
set_option backward.isDefEq.respectTransparency false
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem commutator_character
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (W X K : Subgroup G) (z : G) (hz : orderOf z = 2)
    (q : X →* Multiplicative M) (hq : Function.Surjective q)
    (hk : q.ker = K.subgroupOf X)
    (hK : K ≤ centralizer (W : Set G))
    (hXZ : X ≤ centralizer ({z} : Set G))
    (hWZ : W ≤ centralizer ({z} : Set G))
    (hc : ⁅X,W⁆ ≤ zpowers z) :
    ∃ f : W →* Multiplicative (Module.Dual (ZMod 2) M),
      (∀ (x : X) (w : W), ⁅(x : G),(w : G)⁆ = z ^ ((f w).toAdd (q x).toAdd).val) ∧
      ∀ w : W, f w = 1 ↔ (w : G) ∈ centralizer (X : Set G) := by
  let e : zpowers z ≃* Multiplicative (ZMod 2) :=
    mulEquivOfCyclicCardEq (by rw [Nat.card_zpowers,hz]; simp)
  have he (a : ZMod 2) : e ⟨z^a.val,pow_mem (mem_zpowers z) _⟩ = Multiplicative.ofAdd a := by
    have hne : z ≠ 1 := by intro he; simp [he] at hz
    have hn : (e ⟨z,mem_zpowers z⟩).toAdd ≠ 0 := by
      intro hh
      exact hne (congrArg Subtype.val (e.injective (hh.trans e.map_one.symm)))
    have ho : (e ⟨z,mem_zpowers z⟩).toAdd = 1 := by
      generalize (e ⟨z,mem_zpowers z⟩).toAdd = b at *
      fin_cases b <;> simp_all
    fin_cases a
    · simp
    · change e ⟨z^1,_⟩ = Multiplicative.ofAdd 1
      apply Multiplicative.toAdd.injective
      simpa only [pow_one,toAdd_ofAdd] using ho
  have hmem (x : X) (w : W) : ⁅(x : G),(w : G)⁆ ∈ zpowers z :=
    hc (commutator_mem_commutator x.property w.property)
  have hconj (a : G) (ha : a ∈ centralizer ({z} : Set G)) (b : zpowers z) :
      a*(b : G)*a⁻¹ = (b : G) := by
    have hh : a ∈ centralizer (zpowers z : Set G) := by
      simpa only [zpowers_eq_closure,centralizer_closure] using ha
    rw [←hh b b.property,mul_inv_cancel_right]
  let c (w : W) : X →* zpowers z := {
    toFun x := ⟨⁅(x : G),(w : G)⁆,hmem x w⟩
    map_one' := Subtype.ext (by simp)
    map_mul' a b := by
      apply Subtype.ext
      change ⁅(a : G)*(b : G),(w : G)⁆ = ⁅(a : G),(w : G)⁆*⁅(b : G),(w : G)⁆
      rw [commutatorElement_mul_left_eq_conj_mul,hconj a (hXZ a.property) ⟨_,hmem b w⟩]
      exact congrArg Subtype.val (mul_comm (⟨_,hmem b w⟩ : zpowers z) ⟨_,hmem a w⟩) }
  let cZ (w : W) := e.toMonoidHom.comp (c w)
  have hkc (w : W) : q.ker ≤ (cZ w).ker := by
    intro x hx
    change e (c w x) = 1
    have hh : c w x = 1 := Subtype.ext
      (commutatorElement_eq_one_iff_mul_comm.mpr (hK (hk.le hx) w w.property).symm)
    rw [hh,map_one]
  let d (w : W) := q.liftOfSurjective hq ⟨cZ w,hkc w⟩
  let da (w : W) : M →+ ZMod 2 := {
    toFun a := (d w (Multiplicative.ofAdd a)).toAdd
    map_zero' := (d w).map_one
    map_add' := (d w).map_mul }
  have hd (w : W) (x : X) : (da w).toZModLinearMap 2 (q x).toAdd = (e (c w x)).toAdd :=
    congrArg Multiplicative.toAdd (MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _)
  let f : W →* Multiplicative (Module.Dual (ZMod 2) M) := {
    toFun w := Multiplicative.ofAdd ((da w).toZModLinearMap 2)
    map_one' := by
      apply Multiplicative.toAdd.injective
      apply LinearMap.ext
      intro a
      obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd a)
      have ha : (q x).toAdd = a := congrArg Multiplicative.toAdd hx
      change (da 1).toZModLinearMap 2 a = 0
      rw [←ha,hd]
      change (e ⟨⁅(x : G),1⁆,_⟩).toAdd = 0
      simp
    map_mul' u v := by
      apply Multiplicative.toAdd.injective
      apply LinearMap.ext
      intro a
      obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd a)
      have ha : (q x).toAdd = a := congrArg Multiplicative.toAdd hx
      change (da (u*v)).toZModLinearMap 2 a =
        (da u).toZModLinearMap 2 a + (da v).toZModLinearMap 2 a
      rw [←ha,hd,hd,hd]
      have hh : c (u*v) x = c u x * c v x := by
        apply Subtype.ext
        change ⁅(x : G),(u : G)*(v : G)⁆ = ⁅(x : G),(u : G)⁆*⁅(x : G),(v : G)⁆
        rw [commutatorElement_mul_right_eq_mul_conj]
        simpa only [mul_assoc] using congrArg (fun a : G => ⁅(x : G),(u : G)⁆*a)
          (hconj u (hWZ u.property) ⟨_,hmem x v⟩)
      rw [hh,map_mul]
      rfl }
  refine ⟨f,?_,?_⟩
  · intro x w
    have hh : (⟨⁅(x : G),(w : G)⁆,hmem x w⟩ : zpowers z) =
        ⟨z^((f w).toAdd (q x).toAdd).val,pow_mem (mem_zpowers z) _⟩ := by
      apply e.injective
      rw [he]
      exact congrArg Multiplicative.ofAdd (hd w x).symm
    exact congrArg Subtype.val hh
  · intro w
    constructor
    · intro hw x hx
      apply commutatorElement_eq_one_iff_mul_comm.mp
      have hh := hd w ⟨x,hx⟩
      change (f w).toAdd (q ⟨x,hx⟩).toAdd = (e (c w ⟨x,hx⟩)).toAdd at hh
      rw [hw] at hh
      exact congrArg Subtype.val (e.injective (hh.symm.trans e.map_one.symm))
    · intro hw
      apply Multiplicative.toAdd.injective
      apply LinearMap.ext
      intro a
      obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd a)
      change (da w).toZModLinearMap 2 a = 0
      have ha : (q x).toAdd = a := congrArg Multiplicative.toAdd hx
      rw [←ha,hd]
      have hh : c w x = 1 := Subtype.ext
        (commutatorElement_eq_one_iff_mul_comm.mpr (hw x x.property))
      rw [hh,map_one]
      rfl


private theorem character_surjective
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (W X K : Subgroup G) (z : G) (hz : orderOf z = 2)
    (q : X →* Multiplicative M) (hq : Function.Surjective q)
    (hk : q.ker = K.subgroupOf X)
    (hK : K ≤ centralizer (W : Set G))
    (hXZ : X ≤ centralizer ({z} : Set G))
    (hWZ : W ≤ centralizer ({z} : Set G))
    (hc : ⁅X,W⁆ ≤ zpowers z)
    (hfix : W ⊓ centralizer (X : Set G) = zpowers z)
    (hcard : Nat.card W = 2 * Nat.card M) :
    ∃ f : W →* Multiplicative (Module.Dual (ZMod 2) M),
      Function.Surjective f ∧ f.ker = (zpowers z).subgroupOf W ∧
      ∀ (x : X) (w : W), ⁅(x : G),(w : G)⁆ = z ^ ((f w).toAdd (q x).toAdd).val := by
  obtain ⟨f,hpair,hker⟩ := commutator_character W X K z hz q hq hk hK hXZ hWZ hc
  have hfker : f.ker = (zpowers z).subgroupOf W := by
    ext w
    exact (hker w).trans ⟨fun hw => hfix.le ⟨w.property,hw⟩,
      fun hw => (hfix.ge hw).2⟩
  have hZW : zpowers z ≤ W := hfix.ge.trans inf_le_left
  have hkcard : Nat.card f.ker = 2 := by
    rw [hfker,Nat.card_congr (subgroupOfEquivOfLe hZW).toEquiv,Nat.card_zpowers,hz]
  have hcW := card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,hkcard,hcard] at hcW
  have hr : Nat.card f.range = Nat.card M := by omega
  have hdual : Nat.card (Multiplicative (Module.Dual (ZMod 2) M)) = Nat.card M := by
    change Nat.card (Module.Dual (ZMod 2) M) = Nat.card M
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := M),Subspace.dual_finrank_eq]
  let : Finite M := Finite.of_surjective (fun x : X => (q x).toAdd)
    (fun y => hq (Multiplicative.ofAdd y))
  let : Finite (Module.Dual (ZMod 2) M) := Finite.of_injective
    (fun a : Module.Dual (ZMod 2) M => (a : M → ZMod 2)) DFunLike.coe_injective
  have hftop : f.range = ⊤ := eq_of_le_of_card_ge le_top (by
    rw [Nat.card_congr (topEquiv : (⊤ : Subgroup (Multiplicative (Module.Dual (ZMod 2) M))) ≃* _).toEquiv,
      hdual,hr])
  exact ⟨f,MonoidHom.range_eq_top.mp hftop,hfker,hpair⟩

/-- Full finite transvection pairing gives a fixed representative in each fixed coset. -/
private theorem fixed_coset
    {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [FiniteDimensional (ZMod 2) M]
    (W X K : Subgroup G) (z : G) (hz : orderOf z = 2)
    (q : X →* Multiplicative M) (hq : Function.Surjective q)
    (hk : q.ker = K.subgroupOf X)
    (hK : K ≤ centralizer (W : Set G))
    (hXZ : X ≤ centralizer ({z} : Set G))
    (hWZ : W ≤ centralizer ({z} : Set G))
    (hc : ⁅X,W⁆ ≤ zpowers z)
    (hfix : W ⊓ centralizer (X : Set G) = zpowers z)
    (hcard : Nat.card W = 2 * Nat.card M)
    (d : G) (hd : ∀ x : X, ⁅(x : G),d⁆ ∈ zpowers z)
    (hKd : d ∈ centralizer (K : Set G)) :
    ∃ w ∈ W, w⁻¹*d ∈ centralizer (X : Set G) := by
  obtain ⟨f,hf,_,hpair⟩ := character_surjective W X K z hz q hq hk hK hXZ hWZ hc hfix hcard
  let e := (Module.evalEquiv (ZMod 2) M).toAddEquiv.toMultiplicative
  let b := e.toMonoidHom.comp q
  have hb : b.ker = K.subgroupOf X := by
    change (e.toMonoidHom.comp q).ker = _
    exact (MonoidHom.ker_comp_of_injective q e.toMonoidHom e.injective).trans hk
  exact transvection_fixed_coset W X K z hz f hf b (e.surjective.comp hq) hb
    hpair hXZ d hd hKd


/-- Every coset fixed modulo the central involution has a representative
fixed by the whole sextet two-core. The quotient map retains its full kernel. -/
theorem hexacode_fixed_coset
    (W X K : Subgroup G) (z : G) (hz : orderOf z = 2)
    (q : X →* Multiplicative Atlas.Codes.hexacode) (hq : Function.Surjective q)
    (hk : q.ker = K.subgroupOf X)
    (hK : K ≤ centralizer (W : Set G))
    (hXZ : X ≤ centralizer ({z} : Set G))
    (hWZ : W ≤ centralizer ({z} : Set G))
    (hc : ⁅X,W⁆ ≤ zpowers z)
    (hfix : W ⊓ centralizer (X : Set G) = zpowers z)
    (hcard : Nat.card W = 128)
    (d : G) (hd : ∀ x : X, ⁅(x : G),d⁆ ∈ zpowers z)
    (hKd : d ∈ centralizer (K : Set G)) :
    ∃ w ∈ W, w⁻¹*d ∈ centralizer (X : Set G) := by
  exact fixed_coset W X K z hz q hq hk hK hXZ hWZ hc hfix
    (by rw [hcard,Atlas.Codes.hexacode_card]) d hd hKd

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
