module

public import Theory.Representation.ElementaryAbelianAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.PGroup

/-!
# A faithful prime-power group on sixteen vectors

A finite prime-power group acting faithfully by automorphisms on an elementary
abelian two-group of order sixteen has order nine if its order is divisible by
nine. Faithfulness embeds the actor into GL₄(2), of order 20160. The divisibility
hypothesis identifies its prime as three, and the three-part of 20160 is nine.
This general order calculation supplies the faithful-action step in
Stellmacher (9.1), `refs/latex/stellmacher-n-group.tex`, journal p.47.
-/

namespace Representation

open scoped IsMulCommutative

/-- A faithful prime-power actor on a sixteen-element elementary abelian
2-group has order nine whenever nine divides its order. -/
public theorem card_nine_of_faithful_sixteen_pGroup
    {P V : Type*} [Group P] [Group V] [Finite P] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction P V] [FaithfulSMul P V]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P)
    (hV : Nat.card V = 16) (h9 : 9 ∣ Nat.card P) :
    p = 3 ∧ Nat.card P = 9 := by
  classical
  let ρ := ofElementaryAbelianAction (A := P) (G := V) (p := 2)
  have hρinj : Function.Injective ρ.asGroupHom := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    apply Additive.ofMul.injective
    have heq := LinearMap.congr_fun (congrArg Units.val hab) (Additive.ofMul v)
    change ρ a (Additive.ofMul v) = ρ b (Additive.ofMul v) at heq
    exact heq
  have hdim : Module.finrank (ZMod 2) (Additive V) = 4 := by
    have hc : Nat.card (Additive V) = 16 := (Nat.card_congr Additive.toMul).trans hV
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num at hc
    exact Nat.pow_right_injective (by omega : 1 < 2) hc
  let b : Module.Basis (Fin 4) (ZMod 2) (Additive V) :=
    Module.finBasisOfFinrankEq (ZMod 2) (Additive V) hdim
  let φ : P →* Matrix.GeneralLinearGroup (Fin 4) (ZMod 2) :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hφinj : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hρinj
  have hdiv := Subgroup.card_dvd_of_injective φ hφinj
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [hGL] at hdiv
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hp3 : p = 3 := by
    have h3 : 3 ∣ p ^ n := hn ▸ (show 3 ∣ 9 by norm_num).trans h9
    exact (Nat.prime_eq_prime_of_dvd_pow Nat.prime_three (Fact.out : p.Prime) h3).symm
  subst p
  have hnle : n ≤ 2 := by
    by_contra hnot
    have hbad : 27 ∣ 20160 := by
      rw [hn] at hdiv
      exact (show 27 ∣ 3 ^ n from Nat.pow_dvd_pow 3 (by omega : 3 ≤ n)).trans hdiv
    norm_num at hbad
  refine ⟨rfl, ?_⟩
  interval_cases n
  · norm_num [hn] at h9
  · norm_num [hn] at h9
  · exact hn

end Representation
