module
public import Theory.GroupTheory.Commutator.ThirdHom
public import Theory.ElementaryAbelian.VectorSpace
public import Mathlib.GroupTheory.Abelianization.Defs
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The third commutator as an invariant binary trilinear form

Suppose a finite group's abelianization is elementary abelian at two,
its center has order two, and its central third commutator is nontrivial.
Then the actual additive abelianization carries a nonzero binary trilinear
form invariant under every automorphism of the original group.

The preceding nested homomorphism for [[x,y],z] descends through the
abelianization in each argument. Identifying the actual center with C2
and passing to additive tags gives a trilinear form over ZMod2. Its
nonzero value comes from a literal nontrivial third commutator. Every
automorphism fixes the order-two center, so naturality of commutators
proves invariance under its exact induced abelianization automorphism.
The auxiliary conversion handles the multilinear interface's arbitrary
index equality decision by equality of these instances.

This source-neutral construction supplies the obstruction to an order15
action on the four-dimensional binary Frattini quotient of the class-three
residual in the Tits recognition branch. It assumes no coordinates or
recognition theorem.
-/

open scoped commutatorElement IsMulCommutative

namespace ThirdCommutator

private def liftHom {G C : Type*} [Group G] [CommGroup C] :
    (G →* C) →* (Abelianization G →* C) where
  toFun := Abelianization.lift
  map_one' := by
    ext q
    rfl
  map_mul' := by
    intro f g
    ext q
    rfl

private def descend {G C : Type*} [Group G] [CommGroup C]
    (f : G →* (G →* (G →* C))) :
    Abelianization G →* (Abelianization G →* (Abelianization G →* C)) :=
  Abelianization.lift (liftHom.comp ((MonoidHom.compHom liftHom).comp f))

private theorem descend_apply {G C : Type*} [Group G] [CommGroup C]
    (f : G →* (G →* (G →* C))) (x y z : G) :
    descend f (Abelianization.of x) (Abelianization.of y) (Abelianization.of z) = f x y z := rfl

private def form {A C : Type*} [Group A] [IsElementaryAbelian 2 A] [CommGroup C]
    (f : A →* (A →* (A →* C))) (e : C ≃* Multiplicative (ZMod 2)) :
    MultilinearMap (ZMod 2) (fun _ : Fin 3 => Additive A) (ZMod 2) where
  toFun v := (e (f (v 0).toMul (v 1).toMul (v 2).toMul)).toAdd
  map_update_add' := by
    intro d
    cases Subsingleton.elim d (instDecidableEqFin 3)
    intro v i x y
    fin_cases i <;> simp
  map_update_smul' := by
    intro d
    cases Subsingleton.elim d (instDecidableEqFin 3)
    intro v i r x
    have hr : r = 0 ∨ r = 1 := (by decide : ∀ r : ZMod 2, r = 0 ∨ r = 1) r
    rcases hr with rfl | rfl <;> fin_cases i <;> simp


/-- A nontrivial central third commutator gives a nonzero automorphism-invariant form. -/
public theorem exists_invariant_third_commutator_trilinear
    {G : Type*} [Group G] [Finite G] [IsElementaryAbelian 2 (Abelianization G)]
    (hc : ⁅commutator G, (⊤ : Subgroup G)⁆ ≤ Subgroup.center G)
    (hZ : Nat.card (Subgroup.center G) = 2)
    (hn : ∃ x y z : G, ⁅⁅x,y⁆,z⁆ ≠ 1) :
    ∃ F : MultilinearMap (ZMod 2) (fun _ : Fin 3 => Additive (Abelianization G)) (ZMod 2),
      F ≠ 0 ∧ ∀ (a : MulAut G) (v : Fin 3 → Additive (Abelianization G)),
        F (fun i => Additive.ofMul (a.abelianizationCongr (v i).toMul)) = F v := by
  classical
  obtain ⟨f, hf⟩ := Subgroup.exists_third_commutator_hom hc
  let e : Subgroup.center G ≃* Multiplicative (ZMod 2) :=
    mulEquivOfPrimeCardEq hZ (by simp)
  let F := form (descend f) e
  have hvalue (x y z : G) :
      F ![Additive.ofMul (Abelianization.of x), Additive.ofMul (Abelianization.of y),
        Additive.ofMul (Abelianization.of z)] = (e (f x y z)).toAdd := rfl
  refine ⟨F, ?_, ?_⟩
  · intro hzero
    obtain ⟨x, y, z, hn⟩ := hn
    have hz := congrArg (fun h : MultilinearMap (ZMod 2)
      (fun _ : Fin 3 => Additive (Abelianization G)) (ZMod 2) =>
        h ![Additive.ofMul (Abelianization.of x), Additive.ofMul (Abelianization.of y),
          Additive.ofMul (Abelianization.of z)]) hzero
    rw [hvalue] at hz
    have hone : f x y z = 1 := by
      apply e.injective
      simpa using congrArg Multiplicative.ofAdd hz
    apply hn
    rw [← hf, hone]
    rfl
  · intro a v
    let : IsCyclic (Subgroup.center G) := isCyclic_of_prime_card hZ
    have hautcard : Nat.card (MulAut (Subgroup.center G)) = 1 := by
      rw [IsCyclic.card_mulAut, hZ]
      decide
    let : Subsingleton (MulAut (Subgroup.center G)) :=
      (Nat.card_eq_one_iff_unique.mp hautcard).1
    have hfixed (c : Subgroup.center G) : a (c : G) = c :=
      congrArg (fun t : MulAut (Subgroup.center G) => (t c : G))
        (show Subgroup.centerCongr a = (1 : MulAut (Subgroup.center G)) from Subsingleton.elim _ _)
    choose w hw using fun i : Fin 3 => (QuotientGroup.mk'_surjective (commutator G)) (v i).toMul
    have hv : v = fun i => Additive.ofMul (Abelianization.of (w i)) := by
      funext i
      exact Additive.toMul.injective (hw i).symm
    rw [hv]
    change (e (f (a (w 0)) (a (w 1)) (a (w 2)))).toAdd = (e (f (w 0) (w 1) (w 2))).toAdd
    congr 2
    apply Subtype.ext
    rw [hf, hf]
    have hh := hfixed (f (w 0) (w 1) (w 2))
    rw [hf] at hh
    simpa only [commutatorElement_def, map_mul, map_inv] using hh

end ThirdCommutator
