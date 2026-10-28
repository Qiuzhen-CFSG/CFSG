module
public import Theory.SpecificGroups.PSL3Three.Cardinality
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# Involutions in the Sylow two-subgroups of PSL₃(3)

In a Sylow two-subgroup there is a unique involution commuting with all its
conjugates in that Sylow subgroup. We construct a subgroup of order sixteen
in the actual SL₃(3) matrix model, check its multiplication and the involution
assertion by kernel reduction, and use its odd index to prove it is Sylow.
Sylow conjugacy and the canonical SL₃(3) ≃ PSL₃(3) transport the assertion to
any group equipped with an actual equivalence to PSL₃(3).

The concrete subgroup is semidihedral: its first eight entries are the powers
of an element a of order eight, and the remaining eight are aⁱb with b² = 1
and bab = a³. Only the displayed matrix identities, not this presentation,
are used as proof premises.

This is the model input for the PSL₃(3) case of Aschbacher–Smith 2.3.9(7)(d),
combined manuscript of 1 March 2004, printed pp.525–526. Together with the
solvable-group lemma in `Theory.GroupTheory.SolvableSylowInvolutions`, it
excludes larger characteristic-two intersections without asserting that an
involution centralizer is a maximal subgroup.
-/

@[expose] public section
namespace Matrix.PSL3Three
open Subgroup
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

private def twoElement : Fin 16 → SL :=
  ![⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
⟨!![2, 0, 0; 0, 0, 1; 0, 1, 1], by decide⟩,
⟨!![1, 0, 0; 0, 1, 1; 0, 1, 2], by decide⟩,
⟨!![2, 0, 0; 0, 1, 2; 0, 2, 0], by decide⟩,
⟨!![1, 0, 0; 0, 2, 0; 0, 0, 2], by decide⟩,
⟨!![2, 0, 0; 0, 0, 2; 0, 2, 2], by decide⟩,
⟨!![1, 0, 0; 0, 2, 2; 0, 2, 1], by decide⟩,
⟨!![2, 0, 0; 0, 2, 1; 0, 1, 0], by decide⟩,
⟨!![2, 0, 0; 0, 1, 0; 0, 1, 2], by decide⟩,
⟨!![1, 0, 0; 0, 1, 2; 0, 2, 2], by decide⟩,
⟨!![2, 0, 0; 0, 2, 2; 0, 0, 1], by decide⟩,
⟨!![1, 0, 0; 0, 0, 1; 0, 2, 0], by decide⟩,
⟨!![2, 0, 0; 0, 2, 0; 0, 2, 1], by decide⟩,
⟨!![1, 0, 0; 0, 2, 1; 0, 1, 1], by decide⟩,
⟨!![2, 0, 0; 0, 1, 1; 0, 0, 2], by decide⟩,
⟨!![1, 0, 0; 0, 0, 2; 0, 1, 0], by decide⟩]

private def productIndex : Fin 16 → Fin 16 → Fin 16 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    ![1, 2, 3, 4, 5, 6, 7, 0, 9, 10, 11, 12, 13, 14, 15, 8],
    ![2, 3, 4, 5, 6, 7, 0, 1, 10, 11, 12, 13, 14, 15, 8, 9],
    ![3, 4, 5, 6, 7, 0, 1, 2, 11, 12, 13, 14, 15, 8, 9, 10],
    ![4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11],
    ![5, 6, 7, 0, 1, 2, 3, 4, 13, 14, 15, 8, 9, 10, 11, 12],
    ![6, 7, 0, 1, 2, 3, 4, 5, 14, 15, 8, 9, 10, 11, 12, 13],
    ![7, 0, 1, 2, 3, 4, 5, 6, 15, 8, 9, 10, 11, 12, 13, 14],
    ![8, 11, 14, 9, 12, 15, 10, 13, 0, 3, 6, 1, 4, 7, 2, 5],
    ![9, 12, 15, 10, 13, 8, 11, 14, 1, 4, 7, 2, 5, 0, 3, 6],
    ![10, 13, 8, 11, 14, 9, 12, 15, 2, 5, 0, 3, 6, 1, 4, 7],
    ![11, 14, 9, 12, 15, 10, 13, 8, 3, 6, 1, 4, 7, 2, 5, 0],
    ![12, 15, 10, 13, 8, 11, 14, 9, 4, 7, 2, 5, 0, 3, 6, 1],
    ![13, 8, 11, 14, 9, 12, 15, 10, 5, 0, 3, 6, 1, 4, 7, 2],
    ![14, 9, 12, 15, 10, 13, 8, 11, 6, 1, 4, 7, 2, 5, 0, 3],
    ![15, 10, 13, 8, 11, 14, 9, 12, 7, 2, 5, 0, 3, 6, 1, 4]]

private def inverseIndex : Fin 16 → Fin 16 :=
  ![0, 7, 6, 5, 4, 3, 2, 1, 8, 13, 10, 15, 12, 9, 14, 11]

private theorem twoElement_mul (i j : Fin 16) :
    twoElement (productIndex i j) = twoElement i * twoElement j := by
  apply Subtype.ext
  revert i j
  decide

private theorem twoElement_inv (i : Fin 16) :
    twoElement (inverseIndex i) = (twoElement i)⁻¹ := by
  apply Subtype.ext
  revert i
  decide

private def twoSubgroup : Subgroup SL where
  carrier := Set.range twoElement
  one_mem' := ⟨0, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨productIndex i j, twoElement_mul i j⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact ⟨inverseIndex i, twoElement_inv i⟩

private theorem twoElement_injective : Function.Injective twoElement := by
  have h : ∀ i j : Fin 16, (twoElement i).val = (twoElement j).val → i = j := by decide
  exact fun _ _ he => h _ _ (congrArg Subtype.val he)

private theorem card_twoSubgroup : Nat.card twoSubgroup = 16 := by
  let e : Fin 16 ≃ twoSubgroup := Equiv.ofBijective
    (fun i => ⟨twoElement i, ⟨i, rfl⟩⟩)
    ⟨fun _ _ he => twoElement_injective (congrArg Subtype.val he), by
      rintro ⟨_, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  rw [← Nat.card_congr e]
  simp

private def twoSylowSL : Sylow 2 SL :=
  (IsPGroup.of_card (p := 2) (n := 4) card_twoSubgroup).toSylow (by
    have hc := twoSubgroup.card_mul_index
    rw [card_twoSubgroup, card_SL] at hc
    have hi : twoSubgroup.index = 351 := by omega
    rw [hi]
    decide)

private theorem commuting_conjugate_test (i : Fin 16) :
    twoElement i ^ 2 = 1 →
    Commute (twoElement i)
      (twoElement 1 * twoElement i * (twoElement 1)⁻¹) →
    twoElement i = 1 ∨ twoElement i = twoElement 4 := by
  have h : ∀ i : Fin 16, (twoElement i ^ 2).val = (1 : SL).val →
      (twoElement i * (twoElement 1 * twoElement i * (twoElement 1)⁻¹)).val =
        ((twoElement 1 * twoElement i * (twoElement 1)⁻¹) * twoElement i).val →
      (twoElement i).val = (1 : SL).val ∨ (twoElement i).val = (twoElement 4).val := by
    decide
  intro hp hc
  exact (h i (congrArg Subtype.val hp) (congrArg Subtype.val hc.eq)).imp
    Subtype.ext Subtype.ext

private theorem sylowSL_involution_unique (x y : twoSylowSL)
    (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxc : ∀ s : twoSylowSL, Commute x (s * x * s⁻¹))
    (hyc : ∀ s : twoSylowSL, Commute y (s * y * s⁻¹)) : x = y := by
  have hx' (x : twoSylowSL) (hx : orderOf x = 2)
      (hc : ∀ s : twoSylowSL, Commute x (s * x * s⁻¹)) : (x : SL) = twoElement 4 := by
    obtain ⟨i, hi⟩ := x.property
    have hp : x ^ 2 = 1 := by simpa only [hx] using pow_orderOf_eq_one x
    have hs := hc (⟨twoElement 1, ⟨1, rfl⟩⟩ : twoSylowSL)
    have hpow : twoElement i ^ 2 = 1 := by
      rw [hi]
      exact congrArg Subtype.val hp
    have hcomm : Commute (twoElement i)
        (twoElement 1 * twoElement i * (twoElement 1)⁻¹) := by
      rw [hi]
      exact congrArg Subtype.val hs.eq
    rcases commuting_conjugate_test i hpow hcomm with he | he
    · have hone : x = 1 := Subtype.ext (hi.symm.trans he)
      simp [hone] at hx
    · exact hi.symm.trans he
  exact Subtype.ext ((hx' x hx hxc).trans (hx' y hy hyc).symm)

/-- In any Sylow two-subgroup of the actual PSL₃(3) model, two involutions
each commuting with all their Sylow conjugates are equal. -/
theorem sylow_involution_eq_of_commuting_conjugates
    {K : Type*} [Group K] (e : K ≃* PSL) (R : Sylow 2 K)
    (x y : R) (hx : orderOf x = 2) (hy : orderOf y = 2)
    (hxc : ∀ s : R, Commute x (s * x * s⁻¹))
    (hyc : ∀ s : R, Commute y (s * y * s⁻¹)) : x = y := by
  let : Finite K := Finite.of_equiv PSL e.symm.toEquiv
  let R' := R.mapSurjective (f := e.toMonoidHom) e.surjective
  let P := twoSylowSL.mapSurjective (f := equiv.toMonoidHom) equiv.surjective
  let er : R ≃* R' := MulEquiv.subgroupMap e (R : Subgroup K)
  let ep : twoSylowSL ≃* P := MulEquiv.subgroupMap equiv (twoSylowSL : Subgroup SL)
  let f : R ≃* twoSylowSL := er.trans ((R'.equiv P).trans ep.symm)
  apply f.injective
  apply sylowSL_involution_unique
  · simpa using hx
  · simpa using hy
  · intro s
    simpa using (hxc (f.symm s)).map f.toMonoidHom
  · intro s
    simpa using (hyc (f.symm s)).map f.toMonoidHom

end Matrix.PSL3Three
end
