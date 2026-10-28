module
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Group.Hom.Instances
public import Theory.GroupTheory.Commutator.CentralExtensionPairing
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Central commutators between natural binary SL₂ layers

Over a field of characteristic two with more than two elements, an equivariant
biadditive map from two natural planes to a natural plane is zero. Upper and
lower root elements determine the map from one scalar, and a nontrivial
split-torus scalar forces that scalar to vanish. Restriction to each pair of
summands gives the same result for any finite sum of natural planes.

The central-extension application constructs the actual commutator pairing
through the given surjective coordinates, retaining the original actor and
its quotient marking. If the central kernel embeds equivariantly in a natural
plane, the original group is abelian. This does not assert exponent two.

Source: the natural-layer commutator calculation in DGS, Groups and Graphs
(1985), (5.17), printed p.117, used in (10.9), printed p.163. The stronger
conclusion of (5.17) also requires an exponent argument.
-/

public noncomputable section
open Matrix
open scoped MatrixGroups
namespace Representation.SL2
variable {F : Type*} [Field F] [CharP F 2]
private def upper (t : F) : SL(2,F) := ⟨!![1,t;0,1], by simp [det_fin_two]⟩
private def lower (t : F) : SL(2,F) := ⟨!![1,0;t,1], by simp [det_fin_two]⟩
private def swap : SL(2,F) := ⟨!![0,1;1,0], by simp [det_fin_two, CharTwo.neg_eq]⟩
omit [CharP F 2] in
private theorem upper_vec (t x y : F) : (upper t).val *ᵥ ![x,y] = ![x+t*y,y] := by
  ext i; fin_cases i <;> simp [upper, mulVec, dotProduct, Fin.sum_univ_two]
omit [CharP F 2] in
private theorem lower_vec (t x y : F) : (lower t).val *ᵥ ![x,y] = ![x,t*x+y] := by
  ext i; fin_cases i <;> simp [lower, mulVec, dotProduct, Fin.sum_univ_two]
private theorem swap_vec (x y : F) : (swap (F := F)).val *ᵥ ![x,y] = ![y,x] := by
  ext i; fin_cases i <;> simp [swap, mulVec, dotProduct, Fin.sum_univ_two]
omit [CharP F 2] in
private theorem vec_split (x : Fin 2 → F) : x = ![x 0,0] + ![0,x 1] := by
  ext i; fin_cases i <;> simp

/-- There is no natural-valued equivariant pairing of two natural planes over a nonbinary field. -/
theorem natural_biadditive_eq_zero
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (B : (Fin 2 → F) →+ (Fin 2 → F) →+ (Fin 2 → F))
    (he : ∀ (g : SL(2,F)) x y, B (g.val *ᵥ x) (g.val *ᵥ y) = g.val *ᵥ B x y) :
    ∀ x y, B x y = 0 := by
  have h00 (x y : F) : (B ![x,0] ![y,0]) 1 = 0 := by
    have hh := congrFun (he (upper 1) ![x,0] ![y,0]) 0
    simp only [upper_vec, mul_zero, add_zero] at hh
    simpa [upper, mulVec, dotProduct, Fin.sum_univ_two] using hh
  let f : F → F → F := fun x y => (B ![x,0] ![y,0]) 0
  have hfirst (x y : F) : B ![x,0] ![y,0] = ![f x y,0] := by
    ext i; fin_cases i
    · rfl
    · exact h00 x y
  have hsecond (x y : F) : B ![0,x] ![0,y] = ![0,f x y] := by
    have hh := he swap ![x,0] ![y,0]
    rw [swap_vec,swap_vec,hfirst,swap_vec] at hh
    exact hh
  have hupper (t x y : F) : f x (t*y) = t * (B ![x,0] ![0,y]) 1 := by
    have hh := congrFun (he (upper t) ![x,0] ![0,y]) 0
    rw [upper_vec,upper_vec] at hh
    simp only [mul_zero,add_zero,zero_add] at hh
    have hs : (![t*y,y] : Fin 2 → F) = ![t*y,0] + ![0,y] := by ext i; fin_cases i <;> simp
    rw [hs,map_add,hfirst] at hh
    simp [upper,mulVec,dotProduct,Fin.sum_univ_two] at hh
    exact add_right_cancel (hh.trans (add_comm _ _))
  have hlower (t x y : F) : f (t*x) y = t * (B ![x,0] ![0,y]) 0 := by
    have hh := congrFun (he (lower t) ![x,0] ![0,y]) 1
    rw [lower_vec,lower_vec] at hh
    simp only [mul_zero,add_zero,zero_add] at hh
    have hs : (![x,t*x] : Fin 2 → F) = ![x,0] + ![0,t*x] := by ext i; fin_cases i <;> simp
    rw [hs,map_add,AddMonoidHom.add_apply,hsecond] at hh
    simp [lower,mulVec,dotProduct,Fin.sum_univ_two] at hh
    exact add_left_cancel (hh.trans (add_comm _ _))
  have hc0 (x y : F) : (B ![x,0] ![0,y]) 0 = f x y := by simpa using (hlower 1 x y).symm
  have hc1 (x y : F) : (B ![x,0] ![0,y]) 1 = f x y := by simpa using (hupper 1 x y).symm
  have hf (x y : F) : f x y = x*y*f 1 1 := by
    rw [show f x y = x * f 1 y by simpa only [mul_one,hc0] using hlower x 1 y,
      show f 1 y = y * f 1 1 by simpa only [mul_one,hc1] using hupper y 1 1]
    ring
  let d : SL(2,F) := ⟨!![a,0;0,a⁻¹],by simp [det_fin_two,ha0]⟩
  have hd (x : F) : d.val *ᵥ ![x,0] = ![a*x,0] := by
    ext i; fin_cases i <;> simp [d,mulVec,dotProduct,Fin.sum_univ_two]
  have heq := congrFun (he d ![1,0] ![1,0]) 0
  simp only [hd,hfirst] at heq
  simp only [Matrix.cons_val_zero, mul_one] at heq
  rw [hf a a] at heq
  have hz : f 1 1 = 0 := by
    have heq' : a * ((a-1)*f 1 1) = 0 := by linear_combination heq
    exact (mul_eq_zero.mp ((mul_eq_zero.mp heq').resolve_left ha0)).resolve_left (sub_ne_zero.mpr ha1)
  have hfzero (x y : F) : f x y = 0 := (hf x y).trans (by rw [hz,mul_zero])
  have hc (x y : F) : B ![x,0] ![0,y] = 0 := by
    ext i; fin_cases i
    · change (B ![x,0] ![0,y]) 0 = (0 : F)
      exact (hc0 x y).trans (hfzero x y)
    · change (B ![x,0] ![0,y]) 1 = (0 : F)
      exact (hc1 x y).trans (hfzero x y)
  have hc' (x y : F) : B ![0,x] ![y,0] = 0 := by
    have hh := he swap ![x,0] ![0,y]
    rw [swap_vec,swap_vec,hc,mulVec_zero] at hh
    exact hh
  intro x y
  rw [vec_split x,vec_split y]
  simp only [B.map_add,AddMonoidHom.add_apply,map_add,hfirst,hsecond,hc,hc',hfzero]
  ext i; fin_cases i <;> simp

/-- The vanishing extends to every pair of natural summands. -/
theorem natural_copies_biadditive_eq_zero {n : ℕ}
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (B : (Fin n → Fin 2 → F) →+ (Fin n → Fin 2 → F) →+ (Fin 2 → F))
    (he : ∀ (g : SL(2,F)) x y,
      B (fun i => g.val *ᵥ x i) (fun i => g.val *ᵥ y i) = g.val *ᵥ B x y) :
    ∀ x y, B x y = 0 := by
  classical
  have hs (g : SL(2,F)) (i : Fin n) (x : Fin 2 → F) :
      (fun j => g.val *ᵥ ((Pi.single i x : Fin n → Fin 2 → F) j)) = Pi.single i (g.val *ᵥ x) := by
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Pi.single_eq_of_ne (Ne.symm h),mulVec_zero]
  have hpair (i j : Fin n) (x y : Fin 2 → F) : B (Pi.single i x) (Pi.single j y) = 0 := by
    let s := fun i : Fin n => AddMonoidHom.single (fun _ : Fin n => Fin 2 → F) i
    let b : (Fin 2 → F) →+ (Fin 2 → F) →+ (Fin 2 → F) := {
      toFun x := (B (s i x)).comp (s j)
      map_zero' := by
        apply AddMonoidHom.ext; intro y
        change B (s i 0) (s j y) = 0
        rw [map_zero,map_zero,AddMonoidHom.zero_apply]
      map_add' := by
        intro x y
        apply AddMonoidHom.ext; intro z
        change B (s i (x+y)) (s j z) = B (s i x) (s j z) + B (s i y) (s j z)
        rw [map_add,B.map_add,AddMonoidHom.add_apply] }
    apply natural_biadditive_eq_zero a ha0 ha1 b ?_ x y
    intro g x y
    change B (Pi.single i (g.val *ᵥ x)) (Pi.single j (g.val *ᵥ y)) = _
    rw [←hs,←hs]
    exact he g (Pi.single i x) (Pi.single j y)
  intro x y
  rw [←Finset.univ_sum_single x,←Finset.univ_sum_single y]
  simp only [map_sum,AddMonoidHom.finsetSum_apply,hpair,Finset.sum_const_zero]
end Representation.SL2

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace Representation.SL2
variable {F : Type*} [Field F] [CharP F 2]
variable {Q A : Type*} [Group Q] [Group A]

/-- A central extension with marked natural layers is abelian over a nonbinary field. -/
theorem commutative_of_natural_central_extension {n : ℕ}
    (a : F) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (f : Q →* Multiplicative (Fin n → Fin 2 → F))
    (hf : Function.Surjective f) (hcentral : f.ker ≤ center Q)
    (z : f.ker →* Multiplicative (Fin 2 → F)) (hz : Function.Injective z)
    (π : A →* SL(2,F)) (hπ : Function.Surjective π)
    (φ : A →* MulAut Q)
    (he : ∀ a x, (f (φ a x)).toAdd = fun i => (π a).val *ᵥ (f x).toAdd i)
    (heZ : ∀ a (x y : f.ker), φ a x = y → (z y).toAdd = (π a).val *ᵥ (z x).toAdd) :
    IsMulCommutative Q := by
  let : IsMulCommutative f.ker := ⟨⟨fun x y => Subtype.ext (mem_center_iff.mp (hcentral y.property) x)⟩⟩
  let V := Fin n → Fin 2 → F
  obtain ⟨B,hB⟩ := CentralExtension.exists_lift_commutator_pairing
    f hf hcentral (MonoidHom.id (Multiplicative V))
  have hker (x y : V) : ((B x y).toMul : Q) ∈ f.ker := by
    obtain ⟨u,hu⟩ := hf (Multiplicative.ofAdd x)
    obtain ⟨v,hv⟩ := hf (Multiplicative.ofAdd y)
    rw [hB x y u v hu hv,MonoidHom.mem_ker,map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  let C : V →+ V →+ Additive f.ker := {
    toFun x := {
      toFun y := Additive.ofMul ⟨(B x y).toMul,hker x y⟩
      map_zero' := by
        apply Additive.toMul.injective; apply Subtype.ext
        exact congrArg (fun v : Additive (center Q) => (v.toMul : Q)) (map_zero (B x))
      map_add' y w := by
        apply Additive.toMul.injective; apply Subtype.ext
        exact congrArg (fun v : Additive (center Q) => (v.toMul : Q)) (map_add (B x) y w) }
    map_zero' := by
      apply AddMonoidHom.ext; intro y
      apply Additive.toMul.injective; apply Subtype.ext
      exact congrArg (fun v : Additive (center Q) => (v.toMul : Q))
        (show B 0 y = 0 by rw [map_zero,AddMonoidHom.zero_apply])
    map_add' x y := by
      apply AddMonoidHom.ext; intro w
      apply Additive.toMul.injective; apply Subtype.ext
      exact congrArg (fun v : Additive (center Q) => (v.toMul : Q))
        (show B (x+y) w = B x w + B y w by rw [B.map_add,AddMonoidHom.add_apply]) }
  let zA : Additive f.ker →+ (Fin 2 → F) := {
    toFun x := (z x.toMul).toAdd
    map_zero' := z.map_one
    map_add' x y := z.map_mul x.toMul y.toMul }
  let b : V →+ V →+ (Fin 2 → F) := {
    toFun x := zA.comp (C x)
    map_zero' := by apply AddMonoidHom.ext; intro y; simp
    map_add' x y := by apply AddMonoidHom.ext; intro w; simp }
  have hbe (g : SL(2,F)) (x y : V) :
      b (fun i => g.val *ᵥ x i) (fun i => g.val *ᵥ y i) = g.val *ᵥ b x y := by
    obtain ⟨a,rfl⟩ := hπ g
    obtain ⟨u,hu⟩ := hf (Multiplicative.ofAdd x)
    obtain ⟨v,hv⟩ := hf (Multiplicative.ofAdd y)
    apply heZ a (C x y).toMul (C (fun i => (π a).val *ᵥ x i) (fun i => (π a).val *ᵥ y i)).toMul
    change φ a ((B x y).toMul : Q) = ((B _ _).toMul : Q)
    rw [hB x y u v hu hv,map_commutatorElement]
    symm
    apply hB
    · apply Multiplicative.toAdd.injective
      change (f (φ a u)).toAdd = fun i => (π a).val *ᵥ x i
      rw [he,hu]
      rfl
    · apply Multiplicative.toAdd.injective
      change (f (φ a v)).toAdd = fun i => (π a).val *ᵥ y i
      rw [he,hv]
      rfl
  have hzero := natural_copies_biadditive_eq_zero a ha0 ha1 b hbe
  refine ⟨⟨fun x y => commutatorElement_eq_one_iff_mul_comm.mp ?_⟩⟩
  let x' := (f x).toAdd
  let y' := (f y).toAdd
  have hz' : z (C x' y').toMul = 1 := hzero x' y'
  have he1 : (C x' y').toMul = 1 := hz (hz'.trans z.map_one.symm)
  have hc1 := congrArg (fun t : f.ker => (t : Q)) he1
  change ((B x' y').toMul : Q) = 1 at hc1
  rwa [hB x' y' x y rfl rfl] at hc1
end Representation.SL2
