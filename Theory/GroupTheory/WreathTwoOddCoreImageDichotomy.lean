module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.NormNum
public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# The full-wreath odd-core kernel dichotomy

For a finite group isomorphic to `SL₂(2) ≀ C₂`, any homomorphism either kills
its odd core or has image order divisible by nine. The odd core has index
eight. The theorem uses the literal supplied homomorphism and the ordinary
prime-complement core, without action or faithfulness assumptions.

The concrete cube-root base subgroup is normal and has order nine. Its
containment in the odd core, together with coprimality and the wreath order
72, identifies it with that core. For a nonidentity base element, interchange
the coordinates if necessary; commutation with inversion in the first
coordinate isolates a nonidentity first-axis element. Its swapped conjugate
supplies the second axis. A small kernel-checked finite certificate writes
every element of the nine-element subgroup as a product of powers of these
two elements. Thus a normal subgroup of the full wreath product meeting the
core nontrivially contains the whole core.

Transport this normal-subgroup dichotomy through the supplied isomorphism
and apply it to the kernel. In the trivial-intersection case the restriction
to the core injects into the actual homomorphism range, giving the divisibility.
This uses full-wreath normality; an arbitrary quotient of a group of order
nine need not satisfy the same dichotomy.

This independent group calculation supplies the coatom-action kernel step
in the Stellmacher N-group development. No campaign module is imported.
-/

namespace Theory.GroupTheory
private abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)
private abbrev C2 := Multiplicative (ZMod 2)
private abbrev W := RegularWreathProduct SL2 C2
private instance : Fintype W := Fintype.ofEquiv ((C2 → SL2) × C2)
  (RegularWreathProduct.equivProd SL2 C2).symm
private instance : DecidableEq W := fun first second => decidable_of_iff
  (first.left = second.left ∧ first.right = second.right) RegularWreathProduct.ext_iff.symm


private theorem sl2_cube_mul : ∀ first second : SL2,
    first ^ 3 = 1 → second ^ 3 = 1 → (first * second) ^ 3 = 1 := by
  decide +kernel


private def cubeSubgroup : Subgroup W where
  carrier := {element | element.right = 1 ∧ ∀ coordinate, (element.left coordinate) ^ 3 = 1}
  one_mem' := by simp
  mul_mem' := by
    intro first second hfirst hsecond
    exact ⟨by simp [hfirst.1, hsecond.1], fun coordinate =>
      sl2_cube_mul _ _ (hfirst.2 coordinate) (hsecond.2 _)⟩
  inv_mem' := by
    intro element helement
    refine ⟨by simp [helement.1], ?_⟩
    intro coordinate
    simpa only [RegularWreathProduct.inv_left, Pi.inv_apply, inv_pow, inv_one]
      using congrArg Inv.inv (helement.2 (element.right * coordinate))

private instance : cubeSubgroup.Normal where
  conj_mem element helement conjugator := by
    obtain ⟨hright, hleft⟩ := helement
    refine ⟨by simp [hright], ?_⟩
    intro coordinate
    have hcoordinate : (conjugator * element * conjugator⁻¹).left coordinate =
        conjugator.left coordinate * element.left (conjugator.right⁻¹ * coordinate) *
          (conjugator.left coordinate)⁻¹ := by
      simp [hright]
    rw [hcoordinate, conj_pow, hleft]
    simp

private theorem cube_card : Nat.card cubeSubgroup = 9 := by
  let coordinates : cubeSubgroup ≃ (C2 → {element : SL2 // element ^ 3 = 1}) := {
    toFun := fun element coordinate => ⟨element.val.left coordinate, element.property.2 coordinate⟩
    invFun := fun values => ⟨⟨fun coordinate => (values coordinate).val, 1⟩,
      rfl, fun coordinate => (values coordinate).property⟩
    left_inv := fun element => by
      apply Subtype.ext
      exact RegularWreathProduct.ext rfl element.property.1.symm
    right_inv := fun values => rfl }
  rw [Nat.card_congr coordinates, Nat.card_fun]
  have hcard : Nat.card {element : SL2 // element ^ 3 = 1} = 3 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard]
  norm_num [Nat.card_eq_fintype_card]

private theorem wreath_card : Nat.card W = 72 := by
  rw [RegularWreathProduct.card]
  have hcard : Nat.card SL2 = 6 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  rw [hcard]
  norm_num [Nat.card_eq_fintype_card]


private theorem cube_eq_core : cubeSubgroup = pPrimeCore 2 W := by
  have hle : cubeSubgroup ≤ pPrimeCore 2 W := by
    apply le_sSup
    exact ⟨inferInstance, by rw [cube_card]; decide⟩
  have hcop := pPrimeCore_coprime_card (p := 2) (G := W)
  have hdiv := (pPrimeCore 2 W).card_subgroup_dvd_card
  rw [wreath_card] at hdiv
  have hcop8 : Nat.Coprime (Nat.card (pPrimeCore 2 W)) 8 := by
    exact hcop.symm.pow_right 3
  have hdiv9 : Nat.card (pPrimeCore 2 W) ∣ 9 := hcop8.dvd_of_dvd_mul_left hdiv
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [cube_card]; exact Nat.le_of_dvd (by decide) hdiv9)


private instance : DecidablePred (fun x : W => x∈cubeSubgroup) := fun x =>
  inferInstanceAs (Decidable (x.right=1 ∧ ∀ coordinate, (x.left coordinate)^3=1))

private def swapActor : W := ⟨fun _ => 1, Multiplicative.ofAdd 1⟩
private def firstInverter : W :=
  ⟨fun coordinate => if coordinate=1 then (⟨!![1,1;0,1],by decide⟩ : SL2) else 1,1⟩
private def activeFirst (x : W) : W :=
  if x.left 1=1 then swapActor*x*swapActor⁻¹ else x
private def firstAxis (x : W) : W :=
  activeFirst x * firstInverter * (activeFirst x)⁻¹ * firstInverter⁻¹

private theorem cube_normal_generation :
    ∀ x : cubeSubgroup, (x:W)≠1 → ∀ y : cubeSubgroup,
      ∃ i j : Fin 3, (y:W) = firstAxis x ^ i.val *
        (swapActor * firstAxis x * swapActor⁻¹) ^ j.val := by
  decide +kernel

private theorem cube_inf_normal (N : Subgroup W) (hN : N.Normal) :
    cubeSubgroup ⊓ N = ⊥ ∨ cubeSubgroup ≤ N := by
  by_cases hzero : cubeSubgroup ⊓ N = ⊥
  · exact Or.inl hzero
  right
  obtain ⟨x,hxone⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hzero
  have hactive : activeFirst (x:W) ∈ N := by
    dsimp only [activeFirst]
    split_ifs
    · exact hN.conj_mem x x.property.2 swapActor
    · exact x.property.2
  have haxis : firstAxis (x:W) ∈ N := by
    change activeFirst (x:W)*firstInverter*(activeFirst (x:W))⁻¹*firstInverter⁻¹∈N
    simpa only [mul_assoc] using N.mul_mem hactive
      (hN.conj_mem _ (N.inv_mem hactive) firstInverter)
  have hswap : swapActor*firstAxis (x:W)*swapActor⁻¹∈N :=
    hN.conj_mem _ haxis swapActor
  intro y hy
  obtain ⟨i,j,hgenerate⟩ := cube_normal_generation ⟨x,x.property.1⟩
    (fun hh => hxone (Subtype.ext hh)) ⟨y,hy⟩
  change y = firstAxis (x:W)^i.val*(swapActor*firstAxis (x:W)*swapActor⁻¹)^j.val at hgenerate
  rw [hgenerate]
  exact N.mul_mem (N.pow_mem haxis i.val) (N.pow_mem hswap j.val)

private theorem core_card_of_equiv
    {K : Type*} [Group K] [Finite K] (equiv : K ≃* W) :
    Nat.card (pPrimeCore 2 K) = 9 := by
  have hmap := pPrimeCore_map_iso 2 equiv
  calc
    Nat.card (pPrimeCore 2 K) = Nat.card ((pPrimeCore 2 K).map equiv.toMonoidHom) :=
      (Subgroup.card_map_of_injective equiv.injective).symm
    _ = 9 := by rw [hmap,← cube_eq_core,cube_card]

public theorem wreathTwo_oddCore_le_ker_or_nine_dvd_range
    {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y]
    (model : Nonempty (K ≃* RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2))))
    (f : K →* Y) :
    pPrimeCore 2 K ≤ f.ker ∨ 9 ∣ Nat.card f.range := by
  obtain ⟨equiv⟩ := model
  let N := f.ker.map equiv.toMonoidHom
  have hN : N.Normal := (inferInstance : f.ker.Normal).map _ equiv.surjective
  have hcoreMap := pPrimeCore_map_iso 2 equiv
  rcases cube_inf_normal N hN with hzero | hfull
  · right
    have hdisj : pPrimeCore 2 K ⊓ f.ker = ⊥ := by
      apply Subgroup.map_injective (f := equiv.toMonoidHom) equiv.injective
      rw [Subgroup.map_inf _ _ _ equiv.injective,Subgroup.map_bot,hcoreMap,← cube_eq_core]
      exact hzero
    let restriction : pPrimeCore 2 K →* Y := f.comp (pPrimeCore 2 K).subtype
    have hinj : Function.Injective restriction := by
      apply (MonoidHom.ker_eq_bot_iff restriction).mp
      apply le_bot_iff.mp
      intro x hx
      have hmem : (x:K)∈pPrimeCore 2 K ⊓ f.ker := ⟨x.property,hx⟩
      rw [hdisj,Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    have hcard : Nat.card restriction.range = 9 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
      exact core_card_of_equiv equiv
    have hsub : restriction.range ≤ f.range := by
      rintro y ⟨x,rfl⟩
      exact ⟨x,rfl⟩
    have hdiv := Subgroup.card_dvd_of_le hsub
    rwa [hcard] at hdiv
  · left
    apply (Subgroup.map_le_map_iff_of_injective (f := equiv.toMonoidHom) equiv.injective).mp
    rw [hcoreMap,← cube_eq_core]
    exact hfull

public theorem wreathTwo_oddCore_index_eight
    {K : Type*} [Group K] [Finite K]
    (model : Nonempty (K ≃* RegularWreathProduct
      (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (Multiplicative (ZMod 2)))) :
    (pPrimeCore 2 K).index = 8 := by
  obtain ⟨equiv⟩ := model
  have hcardK : Nat.card K = 72 := (Nat.card_congr equiv.toEquiv).trans wreath_card
  have hcardCore := core_card_of_equiv equiv
  have hcard := (pPrimeCore 2 K).card_mul_index
  rw [hcardK,hcardCore] at hcard
  omega

end Theory.GroupTheory
