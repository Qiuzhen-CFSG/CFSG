module
public import Theory.Representation.SmallDisplacementParabolics.PairedAction
public import Mathlib.LinearAlgebra.Projection

/-!
# Recognition of the full paired binary natural action

An action permuting two complementary binary three-spaces embeds in the
regular wreath product GL₃(2) wr C₂. Construct every actor in coordinates,
then use faithfulness of the literal wreath representation to prove that
these coordinates form a homomorphism. A lower bound on the actor order
makes this embedding surjective. The resulting linear equivalence retains
the action of every original group element, including any specified swap.

The partner-chief application derives the order bound from its two disjoint
component images and their index-two normalizer.
Source: Aschbacher–Smith 15.2.27(2), printed p.1119; the elementary block
permutation construction also appears in ComplementaryFourWreathAction.
-/

public section
open Subgroup
namespace Representation.SmallDisplacementParabolics.PairedRecognition

private theorem linear_prod_of_preserving
    (f : (ThreeSpace × ThreeSpace) ≃ₗ[ZMod 2] (ThreeSpace × ThreeSpace))
    (h0 : ∀ v : ThreeSpace, (f (v, 0)).2 = 0)
    (h1 : ∀ v : ThreeSpace, (f (0, v)).1 = 0) :
    ∃ a b : ThreeSpace ≃ₗ[ZMod 2] ThreeSpace,
      ∀ v : ThreeSpace × ThreeSpace, f v = (a v.1, b v.2) := by
  let a := (LinearMap.fst (ZMod 2) ThreeSpace ThreeSpace).comp
    (f.toLinearMap.comp (LinearMap.inl (ZMod 2) ThreeSpace ThreeSpace))
  let b := (LinearMap.snd (ZMod 2) ThreeSpace ThreeSpace).comp
    (f.toLinearMap.comp (LinearMap.inr (ZMod 2) ThreeSpace ThreeSpace))
  have hf (v : ThreeSpace × ThreeSpace) : f v = (a v.1, b v.2) := by
    have hv : v = (v.1, 0) + (0, v.2) := by ext <;> simp
    calc
      f v = f (v.1, 0) + f (0, v.2) := by rw [← map_add, ← hv]
      _ = (a v.1, b v.2) := by ext <;> simp [a, b, h0, h1]
  have ha : Function.Bijective a := by
    constructor
    · intro x y hxy
      have hh : f (x, 0) = f (y, 0) := by simp only [hf, hxy]
      exact congrArg Prod.fst (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (x,0)
      exact ⟨v.1, by simpa only [hf] using congrArg Prod.fst hv⟩
  have hb : Function.Bijective b := by
    constructor
    · intro x y hxy
      have hh : f (0, x) = f (0, y) := by simp only [hf, hxy]
      exact congrArg Prod.snd (f.injective hh)
    · intro x
      obtain ⟨v,hv⟩ := f.surjective (0,x)
      exact ⟨v.2, by simpa only [hf] using congrArg Prod.snd hv⟩
  exact ⟨LinearEquiv.ofBijective a ha,LinearEquiv.ofBijective b hb,hf⟩

private def pairFunction : (ThreeSpace × ThreeSpace) ≃ₗ[ZMod 2] (PairIndex → ThreeSpace) where
  toFun v i := if i = 1 then v.1 else v.2
  invFun v := (v 1, v (Multiplicative.ofAdd 1))
  left_inv v := by simp
  right_inv v := by
    funext i
    have hi : ∀ i : PairIndex, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
    rcases hi i with rfl | rfl <;> simp
  map_add' v w := by funext i; by_cases hi : i = 1 <;> simp [hi]
  map_smul' c v := by funext i; by_cases hi : i = 1 <;> simp [hi]

private theorem paired_faithful : Function.Injective pairedRepresentation := by
  intro a b hab
  have hleft : a.left = b.left := by
    funext i
    apply LinearEquiv.ext
    intro v
    exact congrFun (LinearMap.congr_fun hab (fun _ => v)) i
  have hright : a.right = b.right := by
    by_contra hne
    have hinv : b.right⁻¹ ≠ a.right⁻¹ := fun he => hne (inv_injective he).symm
    obtain ⟨v,hv⟩ := exists_ne (0 : ThreeSpace)
    let f : PairIndex → ThreeSpace := fun i => if i = a.right⁻¹ then v else 0
    have he := congrFun (LinearMap.congr_fun hab f) (1 : PairIndex)
    change a.left 1 (f (a.right⁻¹ * 1)) = b.left 1 (f (b.right⁻¹ * 1)) at he
    rw [hleft] at he
    have hh := (b.left 1).injective he
    exact hv (by simpa only [mul_one,f,if_pos rfl,if_neg hinv] using hh)
  exact RegularWreathProduct.ext hleft hright

private theorem exists_operator
    (f : (ThreeSpace × ThreeSpace) ≃ₗ[ZMod 2] (ThreeSpace × ThreeSpace))
    (h : ((∀ v, (f (v,0)).2 = 0) ∧ (∀ v, (f (0,v)).1 = 0)) ∨
      ((∀ v, (f (v,0)).1 = 0) ∧ (∀ v, (f (0,v)).2 = 0))) :
    ∃ a : PairedActor, ∀ v, pairFunction (f v) = pairedRepresentation a (pairFunction v) := by
  have hi : ∀ i : PairIndex, i = 1 ∨ i = Multiplicative.ofAdd 1 := by decide
  rcases h with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · obtain ⟨a,b,hab⟩ := linear_prod_of_preserving f h0 h1
    refine ⟨⟨fun i => if i = 1 then a else b,1⟩,?_⟩
    intro v
    funext i
    rw [hab]
    rcases hi i with rfl | rfl <;> simp [pairFunction,pairedRepresentation_apply]
  · let s := LinearEquiv.prodComm (ZMod 2) ThreeSpace ThreeSpace
    obtain ⟨a,b,hab⟩ := linear_prod_of_preserving (s.trans f) h1 h0
    have hh (v : ThreeSpace × ThreeSpace) : f v = (a v.2,b v.1) := by
      exact hab (v.2,v.1)
    refine ⟨⟨fun i => if i = 1 then a else b,Multiplicative.ofAdd 1⟩,?_⟩
    intro v
    funext i
    rw [hh]
    have hinv : (Multiplicative.ofAdd (1 : ZMod 2))⁻¹ = Multiplicative.ofAdd 1 := by decide
    have hsq : Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd 1 = 1 := by decide
    rcases hi i with rfl | rfl <;> simp [pairFunction,pairedRepresentation_apply,hinv,hsq]

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

/-- Two complementary natural three-spaces, with the full actor order, recognize the actual wreath action. -/
theorem marked_model_of_complementary
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (U D : Submodule (ZMod 2) W) (hc : IsCompl U D)
    (e0 : U ≃ₗ[ZMod 2] ThreeSpace) (e1 : D ≃ₗ[ZMod 2] ThreeSpace)
    (hcard : Nat.card PairedActor ≤ Nat.card G)
    (hperm : ∀ g : G,
      (U.map (ρ g) = U ∧ D.map (ρ g) = D) ∨
      (U.map (ρ g) = D ∧ D.map (ρ g) = U)) :
    ∃ e : G ≃* PairedActor, ∃ E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
      (∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i))) ∧
      (∀ g : G, U.map (ρ g) = D → (e g).right ≠ 1) := by
  classical
  let d := (U.prodEquivOfIsCompl D hc).symm
  let e := d.trans (e0.prodCongr e1)
  have he0 (w : W) : w ∈ U ↔ (e w).2 = 0 := by
    change w ∈ U ↔ e1 (d w).2 = 0
    rw [e1.map_eq_zero_iff]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U D hc).symm
  have he1 (w : W) : w ∈ D ↔ (e w).1 = 0 := by
    change w ∈ D ↔ e0 (d w).1 = 0
    rw [e0.map_eq_zero_iff]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero U D hc).symm
  let E := e.trans pairFunction
  have hex (g : G) : ∃ a : PairedActor, ∀ w, E (ρ g w) = pairedRepresentation a (E w) := by
    let f := e.symm.trans ((LinearEquiv.ofBijective (ρ g) (ρ.apply_bijective g)).trans e)
    have hm {A B : Submodule (ZMod 2) W} (hh : A.map (ρ g) = B)
        {w : W} (hw : w ∈ A) : ρ g w ∈ B := hh ▸ Submodule.mem_map_of_mem hw
    have hp : ((∀ v, (f (v,0)).2 = 0) ∧ (∀ v, (f (0,v)).1 = 0)) ∨
        ((∀ v, (f (v,0)).1 = 0) ∧ (∀ v, (f (0,v)).2 = 0)) := by
      rcases hperm g with hh | hh
      · exact Or.inl ⟨fun v => (he0 _).mp (hm hh.1 ((he0 _).mpr (by simp))),
          fun v => (he1 _).mp (hm hh.2 ((he1 _).mpr (by simp)))⟩
      · exact Or.inr ⟨fun v => (he1 _).mp (hm hh.1 ((he0 _).mpr (by simp))),
          fun v => (he0 _).mp (hm hh.2 ((he1 _).mpr (by simp)))⟩
    obtain ⟨a,ha⟩ := exists_operator f hp
    exact ⟨a,fun w => by simpa only [E,f,LinearEquiv.trans_apply,LinearEquiv.symm_apply_apply,
      LinearEquiv.ofBijective_apply] using ha (e w)⟩
  choose a ha using hex
  have heq {a b : PairedActor} (hh : ∀ w : W,
      pairedRepresentation a (E w) = pairedRepresentation b (E w)) : a = b := by
    apply paired_faithful
    apply LinearMap.ext
    intro v
    obtain ⟨w,rfl⟩ := E.surjective v
    exact hh w
  let φ : G →* PairedActor := {
    toFun := a
    map_one' := heq (fun w => by rw [←ha]; simp)
    map_mul' g k := heq (fun w => by rw [←ha,map_mul,Module.End.mul_apply,ha,ha,map_mul,Module.End.mul_apply]) }
  have hinj : Function.Injective φ := by
    intro g k hh
    apply hf
    apply LinearMap.ext
    intro w
    apply E.injective
    rw [ha,ha]
    exact congrArg (fun a => pairedRepresentation a (E w)) hh
  let : Finite (BinaryLinear.OuterCyclic.LinearGroup 3) := Finite.of_injective
    (fun g : BinaryLinear.OuterCyclic.LinearGroup 3 => (g : ThreeSpace → ThreeSpace)) DFunLike.coe_injective
  have hbij := (Nat.bijective_iff_injective_and_card φ).mpr
    ⟨hinj,le_antisymm (Nat.card_le_card_of_injective φ hinj) hcard⟩
  refine ⟨MulEquiv.ofBijective φ hbij,E,(fun g w i => congrFun (ha g w) i),?_⟩
  intro g hswap hshift
  let w := e.symm ((1 : ThreeSpace),0)
  have hw : w ∈ U := (he0 w).mpr (by simp [w])
  have hgw : (e (ρ g w)).1 = 0 := (he1 _).mp
    (hswap ▸ Submodule.mem_map_of_mem hw)
  have hh := congrFun (ha g w) 1
  change pairFunction (e (ρ g w)) 1 =
    (φ g).left 1 (pairFunction (e w) ((φ g).right⁻¹ * 1)) at hh
  change (φ g).right = 1 at hshift
  rw [hshift,inv_one,one_mul] at hh
  change (e (ρ g w)).1 = (φ g).left 1 ((e w).1) at hh
  have hw1 : (e w).1 = 1 := by simp [w]
  rw [hgw,hw1] at hh
  have hz : (1 : ThreeSpace) = 0 := ((φ g).left 1).injective
    (hh.symm.trans ((φ g).left 1).map_zero.symm)
  exact one_ne_zero hz

/-- The complete paired action, forgetting only the additional coordinate marking. -/
theorem model_of_complementary
    (ρ : Representation (ZMod 2) G W) (hf : Function.Injective ρ)
    (U D : Submodule (ZMod 2) W) (hc : IsCompl U D)
    (e0 : U ≃ₗ[ZMod 2] ThreeSpace) (e1 : D ≃ₗ[ZMod 2] ThreeSpace)
    (hcard : Nat.card PairedActor ≤ Nat.card G)
    (hperm : ∀ g : G,
      (U.map (ρ g) = U ∧ D.map (ρ g) = D) ∨
      (U.map (ρ g) = D ∧ D.map (ρ g) = U)) :
    ∃ e : G ≃* PairedActor, ∃ E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace),
      ∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i)) := by
  obtain ⟨e,E,ha,_⟩ := marked_model_of_complementary ρ hf U D hc e0 e1 hcard hperm
  exact ⟨e,E,ha⟩
end Representation.SmallDisplacementParabolics.PairedRecognition
