module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Sylow

/-!
# Class functions on cyclic Sylow subgroups and prime-group outer quotients

Let `P` be a cyclic Sylow p-subgroup, and let `f` be constant on conjugacy
classes. The automorphisms of `P` preserving its restricted values form a
subgroup of the abelian group `Aut(P)`. If this subgroup has index coprime
to q and `Out(G)` is a q-group, every automorphism of `G` preserves `f` on
all p-elements.

Sylow conjugacy first corrects an ambient automorphism by an inner one so
that it preserves `P`. A q-power of the corrected automorphism is inner,
so its restriction has a q-power in the value stabilizer. Coprimality kills
its image in the quotient of `Aut(P)`. A second Sylow conjugation handles
an arbitrary p-element. A known subgroup of value-preserving automorphisms
with coprime index suffices; the full stabilizer need not be computed.

This elementary class-function argument is useful for binary matrix traces
in the J₄ automorphism application of Aschbacher–Smith, Chapter 1, Section 3.
The actual outer-group, Sylow, and power-symmetry hypotheses remain explicit;
no group-specific trace or automorphism classification is asserted here.
-/

@[expose] public section

namespace OuterPGroupCyclicSylowClassFunction

open Subgroup
open scoped Pointwise

variable {G X : Type*} [Group G]

/-- Automorphisms of the actual subgroup preserving the restriction of `f`. -/
def functionStabilizer (P : Subgroup G) (f : G → X) : Subgroup (MulAut P) where
  carrier a := ∀ x : P, f (a x : G) = f x
  one_mem' := fun _ => rfl
  mul_mem' := by
    intro a b ha hb x
    exact (ha (b x)).trans (hb x)
  inv_mem' := by
    intro a ha x
    have h := ha (a⁻¹ x)
    simpa only [MulAut.mul_apply, MulAut.inv_apply, MulEquiv.apply_symm_apply] using h.symm

@[simp] theorem mem_functionStabilizer (P : Subgroup G) (f : G → X) (a : MulAut P) :
    a ∈ functionStabilizer P f ↔ ∀ x : P, f (a x : G) = f x := Iff.rfl

/-- Restriction of ambient automorphisms preserving the specified subgroup. -/
def restriction (P : Subgroup G) :
    MulAction.stabilizer (MulAut G) P →* MulAut P where
  toFun a := (a.val.subgroupMap P).trans (MulEquiv.subgroupCongr a.property)
  map_one' := by ext x; rfl
  map_mul' := by intro a b; ext x; rfl

@[simp] theorem restriction_apply (P : Subgroup G)
    (a : MulAction.stabilizer (MulAut G) P) (x : P) :
    (restriction P a x : G) = a.val x := rfl

variable [Finite G]

omit [Finite G] in
/-- A cyclic-subgroup-preserving automorphism fixes the restricted class function
when its outer class has prime-power order and the stabilizer index is coprime. -/
theorem eq_on_normalized_subgroup (P : Subgroup G) [IsCyclic P]
    (f : G → X) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    {q : ℕ} (houter : IsPGroup q (MulAut.Outer G))
    (hindex : Nat.Coprime (functionStabilizer P f).index q)
    (a : MulAction.stabilizer (MulAut G) P) (x : P) : f (a.val x) = f x := by
  let : IsMulCommutative (MulAut P) := IsMulCommutative.of_comm fun b c =>
    (IsCyclic.mulAutMulEquiv P).injective (by simp only [map_mul, mul_comm])
  let H := functionStabilizer P f
  let β := restriction P a
  obtain ⟨n, hn⟩ := houter (QuotientGroup.mk' (MulAut.innerSubgroup G) a.val)
  have hi : a.val ^ (q ^ n) ∈ MulAut.innerSubgroup G := by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' (MulAut.innerSubgroup G) (a.val ^ (q ^ n)) = 1
    rw [map_pow]
    exact hn
  obtain ⟨g, hg⟩ := hi
  have hp : β ^ (q ^ n) ∈ H := by
    intro y
    dsimp only [β]
    rw [← map_pow]
    change f ((a.val ^ (q ^ n)) (y : G)) = f y
    rw [← hg]
    exact hf g y
  have hpow : (QuotientGroup.mk' H β) ^ (q ^ n) = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hp
  have hc : Nat.Coprime (Nat.card (MulAut P ⧸ H)) (q ^ n) := hindex.pow_right n
  have hβ : QuotientGroup.mk' H β = 1 :=
    hc.pow_left_bijective.injective (by simpa only [one_pow] using hpow)
  have hmem : β ∈ H := (QuotientGroup.eq_one_iff _).mp hβ
  exact hmem x

/-- Every ambient automorphism preserves the class function on the chosen
cyclic Sylow subgroup. The outer prime may differ from the Sylow prime. -/
theorem eq_on_sylow {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P]
    (f : G → X) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    {q : ℕ} (houter : IsPGroup q (MulAut.Outer G))
    (hindex : Nat.Coprime (functionStabilizer (P : Subgroup G) f).index q)
    (a : MulAut G) (x : G) (hx : x ∈ P) : f (a x) = f x := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (a • P) P
  have hm : MulAut.conj g * a ∈ MulAction.stabilizer (MulAut G) (P : Subgroup G) := by
    change (MulAut.conj g * a) • (P : Subgroup G) = (P : Subgroup G)
    rw [mul_smul]
    exact congrArg Sylow.toSubgroup hg
  have h := eq_on_normalized_subgroup (P : Subgroup G) f hf houter hindex
    ⟨MulAut.conj g * a, hm⟩ ⟨x, hx⟩
  exact (hf g (a x)).symm.trans h

/-- The conclusion holds on every p-element, expressed through its actual
cyclic subgroup. -/
theorem eq_on_p_elements {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P]
    (f : G → X) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    {q : ℕ} (houter : IsPGroup q (MulAut.Outer G))
    (hindex : Nat.Coprime (functionStabilizer (P : Subgroup G) f).index q)
    (a : MulAut G) (x : G) (hx : IsPGroup p (zpowers x)) : f (a x) = f x := by
  obtain ⟨Q, hQ⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  have hm : (Q : Subgroup G).map (MulAut.conj g).toMonoidHom = P :=
    congrArg Sylow.toSubgroup hg
  have hxP : g * x * g⁻¹ ∈ P := by
    change g * x * g⁻¹ ∈ (P : Subgroup G)
    rw [← hm]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hQ (mem_zpowers x))
  have h := eq_on_sylow P f hf houter hindex a (g * x * g⁻¹) hxP
  simp only [map_mul, map_inv] at h
  exact (hf (a g) (a x)).symm.trans (h.trans (hf g x))

/-- A known subgroup of value-preserving Sylow automorphisms with coprime
index suffices for the conclusion on the chosen Sylow subgroup. -/
theorem eq_on_sylow_of_subgroup {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P]
    (f : G → X) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    {q : ℕ} (houter : IsPGroup q (MulAut.Outer G))
    (J : Subgroup (MulAut P)) (hJ : ∀ b ∈ J, ∀ x : P, f (b x : G) = f x)
    (hindex : Nat.Coprime J.index q)
    (a : MulAut G) (x : G) (hx : x ∈ P) : f (a x) = f x := by
  apply eq_on_sylow P f hf houter _ a x hx
  exact hindex.of_dvd_left (index_dvd_of_le hJ)

/-- The practical power-symmetry interface: a known subgroup of `Aut(P)`
preserving values and having coprime index gives invariance on all p-elements. -/
theorem eq_on_p_elements_of_subgroup {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) [IsCyclic P]
    (f : G → X) (hf : ∀ g x : G, f (g * x * g⁻¹) = f x)
    {q : ℕ} (houter : IsPGroup q (MulAut.Outer G))
    (J : Subgroup (MulAut P)) (hJ : ∀ b ∈ J, ∀ x : P, f (b x : G) = f x)
    (hindex : Nat.Coprime J.index q)
    (a : MulAut G) (x : G) (hx : IsPGroup p (zpowers x)) : f (a x) = f x := by
  apply eq_on_p_elements P f hf houter _ a x hx
  exact hindex.of_dvd_left (index_dvd_of_le hJ)

end OuterPGroupCyclicSylowClassFunction
