module
public import Theory.Representation.SpecialLinearNatural.ParabolicRadical
public import Theory.Alternating.PrimeRank
public import Theory.GroupTheory.PrimeRankSylow
public import Theory.LinearAlgebra.BinaryFourAlternatingEight
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models

/-!
# Plane stabilizers in faithful four-dimensional binary A₇ actions

The full linear plane stabilizer has order 576: its two-core has order 16,
and its Levi quotient is S₃ × S₃. A faithful A₇ image has order 2520 and
index eight in GL₄(2). The intersection has order at least 72 by the
intersection-index bound and divides gcd(2520,576)=72, so its order is 72.
Its Sylow three-subgroup is therefore a full Sylow subgroup of A₇, giving
three-rank two. The conclusion applies to the original action and plane.

Source: Aschbacher–Smith, 13.7.6(4), printed p.939 of the combined
manuscript of 1 March 2004.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open BinaryLinear.SmallParabolicLevi BinaryLinear.OuterCyclic
namespace Representation.BinaryAlternatingSevenControl
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem parabolic_card (hd : Module.finrank (ZMod 2) V = 4)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) W = 2) :
    Nat.card (BinaryLinear.parabolic W) = 576 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  have hQ : Module.finrank (ZMod 2) (V ⧸ W) = 2 := by
    have h := W.finrank_quotient_add_finrank
    omega
  let a : W ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hW)
  let b : (V ⧸ W) ≃ₗ[ZMod 2] Space 2 := LinearEquiv.ofFinrankEq _ _ (by simpa [Space] using hQ)
  let e := (quotientTwoCoreEquivOfCoordinates W a b).trans
    (linearTwoEquivSymmetricThree.prodCongr linearTwoEquivSymmetricThree)
  have hquot : Nat.card (BinaryLinear.parabolic W ⧸ pCore 2 (BinaryLinear.parabolic W)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    decide
  have hcore : Nat.card (pCore 2 (BinaryLinear.parabolic W)) = 16 := by
    have hh : Nat.card (pCore 2 (BinaryLinear.parabolic W)) = Nat.card (BinaryLinear.radical W) := by
      rw [← map_twoCore_eq_radical W]
      exact (Subgroup.card_map_of_injective (BinaryLinear.parabolic W).subtype_injective).symm
    rw [hh, SpecialLinearNatural.card_radical, hQ, hW]
    norm_num
  rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 (BinaryLinear.parabolic W)),hquot,hcore]

/-- Every plane stabilizer in a faithful binary A₇ four-space has order 72. -/
theorem plane_stabilizer_card (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) V = 4)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) W = 2) :
    Nat.card (subspaceStabilizer τ W) = 72 := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let f : alternatingGroup (Fin 7) →* BinaryLinear.GL V :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).toMonoidHom.comp τ.asGroupHom
  have hfi : Function.Injective f :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).injective.comp
      (fun a b hab => hf (congrArg Units.val hab))
  let I := f.range
  let P := BinaryLinear.parabolic W
  let A := subspaceStabilizer τ W
  have hmap : A.map f = I ⊓ P := by
    ext g
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,rfl⟩,ha⟩
    · rintro ⟨⟨a,rfl⟩,ha⟩
      exact ⟨a,ha,rfl⟩
  have hAc : Nat.card A = Nat.card (I ⊓ P : Subgroup (BinaryLinear.GL V)) := by
    rw [← hmap]
    exact Nat.card_congr (A.equivMapOfInjective f hfi).toEquiv
  have hGL : Nat.card (BinaryLinear.GL V) = 20160 := by
    rw [Nat.card_congr (BinaryFourAlternatingEight.linearEquivAlternatingEight hd).toEquiv,
      nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hI : Nat.card I = 2520 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv, nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hP : Nat.card P = 576 := parabolic_card hd W hW
  have hi : I.index = 8 := by
    have h := I.card_mul_index
    rw [hI,hGL] at h
    omega
  have hp : P.index = 35 := by
    have h := P.card_mul_index
    rw [hP,hGL] at h
    omega
  have hbound := index_inf_le (H := I) (K := P)
  rw [hi,hp] at hbound
  have hprod := (I ⊓ P).card_mul_index
  rw [hGL] at hprod
  have hdiv : Nat.card (I ⊓ P : Subgroup (BinaryLinear.GL V)) ∣ 72 := by
    have h1 := card_dvd_of_le (show I ⊓ P ≤ I from inf_le_left)
    have h2 := card_dvd_of_le (show I ⊓ P ≤ P from inf_le_right)
    rw [hI] at h1
    rw [hP] at h2
    exact Nat.dvd_gcd h1 h2
  have hup := Nat.le_of_dvd (by decide : 0 < 72) hdiv
  have hlo : 72 ≤ Nat.card (I ⊓ P : Subgroup (BinaryLinear.GL V)) := by
    nlinarith
  exact hAc.trans (Nat.le_antisymm hup hlo)

/-- Every plane stabilizer in a faithful binary A₇ four-space has three-rank two. -/
theorem plane_stabilizer_rank (τ : Representation (ZMod 2) (alternatingGroup (Fin 7)) V)
    (hf : Function.Injective τ) (hd : Module.finrank (ZMod 2) V = 4)
    (W : Submodule (ZMod 2) V) (hW : Module.finrank (ZMod 2) W = 2) :
    primeRank 3 (subspaceStabilizer τ W) = 2 := by
  let A := subspaceStabilizer τ W
  have hA : Nat.card A = 72 := plane_stabilizer_card τ hf hd W hW
  let S : Sylow 3 A := Sylow.nonempty.some
  have hS : Nat.card S = 9 := by
    rw [Sylow.card_eq_multiplicity,hA,show 72 = 8 * 3^2 by decide,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_three.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 8)]
  let B : Subgroup (alternatingGroup (Fin 7)) := (S : Subgroup A).map A.subtype
  have hB : Nat.card B = 9 := by
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hS
  have hBi : B.index = 280 := by
    have h := B.card_mul_index
    rw [hB,nat_card_alternatingGroup] at h
    norm_num [Nat.factorial] at h
    omega
  let R : Sylow 3 (alternatingGroup (Fin 7)) :=
    (S.isPGroup'.map A.subtype).toSylow (by rw [hBi]; decide)
  have he := Theory.GroupTheory.primeRank_equiv 3
    ((S : Subgroup A).equivMapOfInjective A.subtype A.subtype_injective)
  have hr := R.primeRank_eq
  change primeRank 3 (alternatingGroup (Fin 7)) = primeRank 3 B at hr
  have ha : primeRank 3 (alternatingGroup (Fin 7)) = 2 :=
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 7 3 (by decide) (by decide)
  exact S.primeRank_eq.trans (he.trans (hr.symm.trans ha))

end Representation.BinaryAlternatingSevenControl
