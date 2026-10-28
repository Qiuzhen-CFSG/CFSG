module
public import Theory.Representation.DegreeFourFrattini

/-!
# Three-dimensional odd-characteristic two-groups

A faithful representation in degree at most three gives at most three
character weights on a self-centralizing normal abelian subgroup. The
permutation quotient is a two-group of order at most two, while the first
omega subgroup has order at most eight. Thus the Frattini quotient has
order at most sixteen. The Hall odd-normalizer consumer uses this to
exclude PSL₅(2) outer sections in the odd PSL₃ and PSU₃ models.
Source: the weight-permutation argument in Aschbacher--Smith A.3.21(c),
printed pp.55--56, applied in 4.4.10--11, p.621.
-/

public section
open scoped IsMulCommutative TensorProduct
open Subgroup
namespace Representation
variable {F P V : Type*} [Field F] [Group P] [Finite P]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V]

/-- A faithful odd-characteristic representation of degree at most three
bounds the whole two-group Frattini quotient by 16. -/
theorem card_frattini_quotient_le_sixteen_of_faithful_degree_three
    (hP : IsPGroup 2 P) (rho : Representation F P V)
    (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V ≤ 3) :
    Nat.card (P ⧸ frattini P) ≤ 16 := by
  classical
  obtain ⟨A, hAn, hAc, hCA⟩ := exists_normal_abelian_selfCentralizing hP
  let : A.Normal := hAn
  let : IsMulCommutative A := hAc
  let E := AlgebraicClosure F
  let sigma := rho.extendScalars E
  have hsigma : Function.Injective sigma :=
    (extendScalars_faithful_iff E rho).mp hrho
  have h2E : (2 : E) ≠ 0 := by
    intro h
    apply h2
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  have horderAE : (Nat.card A : E) ≠ 0 := by
    obtain ⟨k, hk⟩ := (hP.to_subgroup A).exists_card_eq
    rw [hk, Nat.cast_pow]
    exact pow_ne_zero _ h2E
  have hdimE : Module.finrank E (E ⊗[F] V) ≤ 3 := by
    simpa only [Module.finrank_baseChange] using hdim
  obtain ⟨hfinite, hweights⟩ :=
    characterWeight_card_le (sigma.comp A.subtype) horderAE
  let W := CharacterWeight (sigma.comp A.subtype)
  let : Finite W := hfinite
  let := Fintype.ofFinite W
  let i : P →* Subgroup.normalizer (A : Set P) :=
    (MonoidHom.id P).codRestrict _ (fun g => by
      rw [A.normalizer_eq_top]
      trivial)
  let f : P →* Equiv.Perm W :=
    ((automizerWeightPerm sigma A).comp A.normalizerMonoidHom.rangeRestrict).comp i
  have hker : f.ker = A := by
    have h := normalizerWeightPerm_ker sigma A hsigma horderAE
    ext g
    change i g ∈ ((automizerWeightPerm sigma A).comp
      A.normalizerMonoidHom.rangeRestrict).ker ↔ g ∈ A
    rw [h]
    change g ∈ Subgroup.centralizer (A : Set P) ↔ g ∈ A
    exact ⟨fun h => hCA h, fun h => A.le_centralizer h⟩
  have hdiv : A.index ∣ (Nat.card W).factorial := by
    rw [← hker, Subgroup.index_ker]
    have hd := f.range.card_subgroup_dvd_card
    simpa only [Nat.card_eq_fintype_card, Fintype.card_perm] using hd
  have hdiv6 : A.index ∣ 6 :=
    hdiv.trans (Nat.factorial_dvd_factorial (hweights.trans hdimE))
  have hidx6 : A.index ≤ 6 := by
    exact Nat.le_of_dvd (by decide) hdiv6
  obtain ⟨n, hncard⟩ := hP.index A
  have hnlt : n < 3 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hncard] at hh'
    norm_num at hh'
    omega
  have hi2 : A.index ≤ 2 := by
    rw [hncard] at hdiv6 ⊢
    interval_cases n <;> norm_num at *
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card O ≤ 8 := by
    exact (elementary_card_le_pow_finrank_of_involutive
      ((rho.comp A.subtype).comp O.subtype)
      ((hrho.comp A.subtype_injective).comp O.subtype_injective) h2).trans
      (pow_le_pow_right' (by decide) hdim)
  calc
    Nat.card (P ⧸ frattini P) ≤ A.index * Nat.card O :=
      hP.card_frattini_quotient_le_index_mul_omega_one A
    _ ≤ 2 * 8 := Nat.mul_le_mul hi2 hO
    _ = 16 := by norm_num


end Representation

