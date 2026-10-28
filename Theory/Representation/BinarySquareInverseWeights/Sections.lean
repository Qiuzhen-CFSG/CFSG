module
public import Theory.Representation.BinarySquareInverseWeights
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Algebra.ZMod

/-!
# Coordinates on a quotient by the intersection of two normal factors

A homomorphism on either factor with kernel the intersection extends across
the other factor. Together the extensions identify the literal quotient by
the intersection with the product of the two marked lines. The distinct
square/inverse module theorem then classifies invariant subgroups above the
intersection whose relative order is the field order.

This supplies the quotient transport needed for the point-parabolic argument
in MS93 (3.7), printed p.877. The source factors and their markings are inputs;
the product identification and two-factor conclusion are constructed here.
-/

public noncomputable section
open Subgroup
namespace Representation.BinarySquareInverseWeights
variable {G M : Type*} [Group G] [Group M]

/-- Extend a character of one factor across the other normal factor. -/
theorem extend_factor (A B : Subgroup G) [B.Normal] (hspan : A ⊔ B = ⊤)
    (f : A →* M) (hf : Function.Surjective f) (hk : f.ker = B.subgroupOf A) :
    ∃ r : G →* M, Function.Surjective r ∧ r.ker = B ∧
      ∀ x : A, r x = f x := by
  let p : A →* G ⧸ B := (QuotientGroup.mk' B).comp A.subtype
  have hp : Function.Surjective p := by
    intro x
    obtain ⟨y,rfl⟩ := QuotientGroup.mk'_surjective B x
    have hy : y ∈ A ⊔ B := hspan.symm ▸ mem_top y
    rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right A B le_normalizer_of_normal] at hy
    obtain ⟨a,ha,b,hb,rfl⟩ := hy
    refine ⟨⟨a,ha⟩,?_⟩
    change QuotientGroup.mk' B a = QuotientGroup.mk' B (a*b)
    have hb' : QuotientGroup.mk' B b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    rw [map_mul, hb',mul_one]
  have hpk : p.ker = f.ker := by
    rw [hk]
    ext x
    exact QuotientGroup.eq_one_iff x.val
  let r₀ : G ⧸ B →* M := p.liftOfSurjective hp ⟨f,hpk.le⟩
  have hr (x : A) : r₀ (p x) = f x := p.liftOfRightInverse_comp_apply _ _ ⟨f,hpk.le⟩ x
  have hi : Function.Injective r₀ := by
    apply (MonoidHom.ker_eq_bot_iff r₀).mp
    apply bot_unique
    intro x hx
    obtain ⟨a,rfl⟩ := hp x
    have ha : a ∈ f.ker := by simpa only [MonoidHom.mem_ker,hr] using hx
    exact show a ∈ p.ker from hpk.symm ▸ ha
  let r := r₀.comp (QuotientGroup.mk' B)
  refine ⟨r,?_,?_,fun x => hr x⟩
  · intro x
    obtain ⟨a,rfl⟩ := hf x
    exact ⟨a,hr a⟩
  · ext x
    change r₀ (QuotientGroup.mk' B x) = 1 ↔ x ∈ B
    rw [← r₀.map_one, hi.eq_iff]
    exact QuotientGroup.eq_one_iff x

variable {F : Type*} [Field F]

/-- Two normal source factors, with maps having their literal intersection
as kernel, supply coordinates on the quotient by that intersection. -/
structure PairCoordinates (A B : Subgroup G) where
  map : G →* Multiplicative (F × F)
  onto : Function.Surjective map
  first_kernel : ∀ x, (map x).toAdd.1 = 0 ↔ x ∈ A
  second_kernel : ∀ x, (map x).toAdd.2 = 0 ↔ x ∈ B

variable (A B : Subgroup G) [A.Normal] [B.Normal]

theorem pairCoordinates (hspan : A ⊔ B = ⊤)
    (fA : A →* Multiplicative F) (fB : B →* Multiplicative F)
    (hA : Function.Surjective fA) (hB : Function.Surjective fB)
    (kA : fA.ker = B.subgroupOf A) (kB : fB.ker = A.subgroupOf B) :
    ∃ c : PairCoordinates (F := F) A B,
      (∀ a : A, (c.map a).toAdd = (0,(fA a).toAdd)) ∧
      (∀ b : B, (c.map b).toAdd = ((fB b).toAdd,0)) := by
  obtain ⟨rA,hrA,krA,erA⟩ := extend_factor A B hspan fA hA kA
  obtain ⟨rB,hrB,krB,erB⟩ := extend_factor B A (sup_comm B A ▸ hspan) fB hB kB
  let p : G →* Multiplicative (F × F) := {
    toFun := fun x => Multiplicative.ofAdd ((rB x).toAdd,(rA x).toAdd)
    map_one' := by simp
    map_mul' := by intro x y; simp only [map_mul]; rfl }
  have ea (a : A) : (p a).toAdd = (0,(fA a).toAdd) := by
    change ((rB a).toAdd,(rA a).toAdd) = _
    rw [erA, show rB a = 1 from krB.symm ▸ a.property]
    rfl
  have eb (b : B) : (p b).toAdd = ((fB b).toAdd,0) := by
    change ((rB b).toAdd,(rA b).toAdd) = _
    rw [erB, show rA b = 1 from krA.symm ▸ b.property]
    rfl
  refine ⟨⟨p,?_,?_,?_⟩,ea,eb⟩
  · intro x
    obtain ⟨a,ha⟩ := hA (Multiplicative.ofAdd x.toAdd.2)
    obtain ⟨b,hb⟩ := hB (Multiplicative.ofAdd x.toAdd.1)
    refine ⟨b*a,?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_mul]
    change (p (b : G)).toAdd + (p (a : G)).toAdd = x.toAdd
    rw [ea,eb,ha,hb]
    simp
  · intro x
    change rB x = 1 ↔ x ∈ A
    exact krB ▸ Iff.rfl
  · intro x
    change rA x = 1 ↔ x ∈ B
    exact krA ▸ Iff.rfl

namespace PairCoordinates
variable {A B} (c : PairCoordinates (F := F) A B)

omit [A.Normal] [B.Normal] in
theorem kernel : c.map.ker = A ⊓ B := by
  ext x
  change (c.map x).toAdd = (0,0) ↔ x ∈ A ∧ x ∈ B
  rw [Prod.mk.injEq]
  exact and_congr (c.first_kernel x) (c.second_kernel x)

/-- The actual quotient by the intersection, not a freely chosen carrier. -/
@[expose] def quotientEquiv : (G ⧸ (A ⊓ B)) ≃* Multiplicative (F × F) :=
  (QuotientGroup.quotientMulEquivOfEq c.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective c.map c.onto)

@[simp] theorem quotientEquiv_mk (x : G) :
    c.quotientEquiv (QuotientGroup.mk' (A ⊓ B) x) = c.map x := rfl

variable [Finite F] [CharP F 2]

omit [A.Normal] [B.Normal] in
/-- Pulling back the distinct-simple-pair classification through the actual
quotient coordinates leaves exactly the two original factors. -/
theorem invariant_order_q (hq : 2 < Nat.card F) (h4 : Nat.card F ≠ 4)
    (W : Subgroup G) (hk : A ⊓ B ≤ W)
    (hcard : Nat.card (W.map c.map) = Nat.card F)
    (hstable : ∀ a : Fˣ, ∀ x ∈ W, ∃ y ∈ W,
      (c.map y).toAdd = ((a:F)^2*(c.map x).toAdd.1,(a:F)⁻¹*(c.map x).toAdd.2)) :
    W = A ∨ W = B := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let J : AddSubgroup (F × F) := (W.map c.map).toAddSubgroup
  have hJ : Nat.card J = Nat.card F := hcard
  have hact : ∀ a : Fˣ, ∀ x ∈ J, ((a:F)^2*x.1,(a:F)⁻¹*x.2) ∈ J := by
    intro a x hx
    obtain ⟨w,hw,he⟩ := hx
    change (c.map w).toAdd = x at he
    obtain ⟨y,hy,ey⟩ := hstable a w hw
    refine ⟨y,hy,?_⟩
    change (c.map y).toAdd = _
    rwa [he] at ey
  have hmem (x : G) : x ∈ W ↔ c.map x ∈ W.map c.map := by
    have hh := Subgroup.comap_map_eq_self (f := c.map) (show c.map.ker ≤ W by rw [c.kernel]; exact hk)
    exact show x ∈ W ↔ x ∈ (W.map c.map).comap c.map from hh.symm ▸ Iff.rfl
  rcases order_q_addSubgroup_axes hq h4 J hJ hact with hs | hi
  · right
    ext x
    rw [hmem]
    change (c.map x).toAdd ∈ J ↔ x ∈ B
    rw [hs]
    exact (and_iff_right (by trivial)).trans (c.second_kernel x)
  · left
    ext x
    rw [hmem]
    change (c.map x).toAdd ∈ J ↔ x ∈ A
    rw [hi]
    exact (and_iff_left (by trivial)).trans (c.first_kernel x)
end PairCoordinates
end Representation.BinarySquareInverseWeights
