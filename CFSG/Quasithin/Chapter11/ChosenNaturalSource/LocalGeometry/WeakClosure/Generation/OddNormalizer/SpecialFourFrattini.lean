module
public import Theory.SpecificGroups.OddClassicalSylowFrattini
public import Theory.SpecificGroups.OddFourRank
public import Theory.SpecificGroups.SymmetricFourSylow
public import Theory.Frattini.SubgroupIndexBound

/-!
# A five-generator bound in determinant-one degree four

Choose a normal abelian self-centralizing subgroup A of the two-group P.
Its faithful permutation action on at most four character weights gives
[P:A] ≤ 8. A two-rank bound of three gives |Ω₁(A)| ≤ 8; determinant one
in degree four supplies this rank bound.
If [P:A] ≤ 4, the subgroup Frattini inequality proves |P/Φ(P)| ≤ 32.
Otherwise P/A is the dihedral Sylow subgroup of S₄ and is noncommutative.
Thus Φ(P) is not contained in A and |Φ(P)| ≥ 2|Φ(A)|, supplying the
extra factor of two missing from the crude bound of 64.

OuterOddFour applies this to the actual SL₄, SU₄ and Sp₄ covers in
odd characteristic and their literal projective quotient maps. OuterOddG2
uses the rank-three version on its faithful four-dimensional local action.
Source: Aschbacher--Smith 4.4.10--12, printed pp.621--622, using I.3.1
and the character-weight argument of A.3.21(c), printed pp.55--56.
-/

open Subgroup Representation
open scoped IsMulCommutative TensorProduct MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SpecialFourFrattini

private theorem frattini_twice_of_noncommutative_quotient
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (A : Subgroup P) [A.Normal] (hnot : ¬ IsMulCommutative (P ⧸ A)) :
    2 * Nat.card (frattini A) ≤ Nat.card (frattini P) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : Fact (IsPGroup 2 A) := ⟨hP.to_subgroup A⟩
  have hphi : ¬ frattini P ≤ A := fun h => hnot
    (Normal.quotient_commutative_iff_commutator_le.mpr
      ((commutator_le_frattini_of_isPGroup (p := 2)).trans h))
  let C := A.subgroupOf (frattini P)
  have hC : C ≠ ⊤ := by
    intro h
    apply hphi
    intro x hx
    exact (show (⟨x,hx⟩ : frattini P) ∈ C by rw [h]; trivial)
  have hi : 2 ≤ C.index := by have := C.one_lt_index_of_ne_top hC; omega
  let f : frattini A → C := fun a =>
    ⟨⟨a.val.val,frattini_map_le_of_isPGroup (p := 2) A.subtype
      (mem_map_of_mem A.subtype a.property)⟩,a.val.property⟩
  have hf : Function.Injective f := by
    intro a b he
    exact Subtype.ext (Subtype.ext (congrArg (fun x : C => x.val.val) he))
  have hc := Nat.card_le_card_of_injective f hf
  have hprod := C.card_mul_index
  nlinarith

private theorem noncommutative_of_perm_card_eight
    {W : Type*} [Fintype W] (hW : Nat.card W ≤ 4)
    (R : Subgroup (Equiv.Perm W)) (hR : Nat.card R = 8) : ¬ IsMulCommutative R := by
  classical
  have hd : Nat.card R ∣ (Nat.card W).factorial := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_perm] using R.card_subgroup_dvd_card
  have hW4 : Nat.card W = 4 := by
    by_contra hn
    have hle : Nat.card W ≤ 3 := by omega
    have hh := hd.trans (Nat.factorial_dvd_factorial hle)
    rw [hR] at hh
    norm_num [Nat.factorial] at hh
  let e : W ≃ Fin 4 := (Finite.equivFin W).trans (finCongr hW4)
  let R' := R.map e.permCongrHom.toMonoidHom
  let a : R ≃* R' := e.permCongrHom.subgroupMap R
  have hc : Nat.card R' = 8 := by rw [←Nat.card_congr a.toEquiv,hR]
  let U : Sylow 2 (Equiv.Perm (Fin 4)) := Sylow.ofCard R' (by
    rw [hc]
    norm_num only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,show (4 : ℕ).factorial = 24 from rfl]
    rw [show 24 = 2^3*3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,Nat.prime_three.factorization])
  obtain ⟨b⟩ := Equiv.Perm.sylow_two_equiv_dihedral_four U
  let c : R ≃* DihedralGroup 4 := a.trans b
  intro h
  let := h
  apply DihedralGroup.not_commutative (by decide : 4 ≠ 1) (by decide : 4 ≠ 2)
  refine ⟨⟨fun x y => ?_⟩⟩
  obtain ⟨x,rfl⟩ := c.surjective x
  obtain ⟨y,rfl⟩ := c.surjective y
  rw [←map_mul,←map_mul,mul_comm]

/-- A faithful degree-four representation and two-rank at most three
bound the Sylow generator number by five. -/
public theorem degree_four_frattini_le_thirtytwo_of_twoRank_le_three
    {F P V : Type*} [Field F] [Group P] [Finite P]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (hP : IsPGroup 2 P) (rho : Representation F P V)
    (hrho : Function.Injective rho) (h2 : (2 : F) ≠ 0)
    (hdim : Module.finrank F V ≤ 4) (hrank : primeRank 2 P ≤ 3) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
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
  have hdimE : Module.finrank E (E ⊗[F] V) ≤ 4 := by
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
  have hdiv24 : A.index ∣ 24 :=
    hdiv.trans (Nat.factorial_dvd_factorial (hweights.trans hdimE))
  have hidx24 : A.index ≤ 24 := by
    exact Nat.le_of_dvd (by decide) hdiv24
  obtain ⟨n, hncard⟩ := hP.index A
  have hnlt : n < 5 := by
    by_contra! hh
    have hh' := Nat.pow_le_pow_right (by decide : 0 < 2) hh
    rw [← hncard] at hh'
    norm_num [Nat.factorial] at hh'
    omega
  have hi8 : A.index ≤ 8 := by
    rw [hncard] at hdiv24 ⊢
    interval_cases n <;> norm_num at *
  let O := omega₁ A (p := 2)
  let : IsElementaryAbelian 2 O := IsElementaryAbelian.omega₁_of_isMulCommutative A
  have hO : Nat.card O ≤ 8 := by
    have h := (primeRank_le_iff_elementary_card_le P).mp hrank
      (O.map A.subtype) (IsElementaryAbelian.map _)
    rw [card_map_of_injective A.subtype_injective] at h
    exact h
  by_cases hi4 : A.index ≤ 4
  · exact (hP.card_frattini_quotient_le_index_mul_omega_one A).trans
      ((Nat.mul_le_mul hi4 hO).trans (by decide))
  have hi : A.index = 8 := by
    rw [hncard] at hi4 hi8 ⊢
    interval_cases n <;> norm_num at *
  have hR : Nat.card f.range = 8 := by
    rw [←index_ker,hker,hi]
  have hnot := noncommutative_of_perm_card_eight (hweights.trans hdimE) f.range hR
  let e : (P ⧸ A) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have hnotA : ¬ IsMulCommutative (P ⧸ A) := by
    intro h
    let := h
    apply hnot
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a,rfl⟩ := e.surjective a
    obtain ⟨b,rfl⟩ := e.surjective b
    rw [←map_mul,←map_mul,mul_comm]
  have hphi := frattini_twice_of_noncommutative_quotient hP A hnotA
  have hAc := card_eq_card_quotient_mul_card_subgroup (frattini A)
  rw [(hP.to_subgroup A).card_frattini_quotient_eq_card_omega_one] at hAc
  have hPc := card_eq_card_quotient_mul_card_subgroup (frattini P)
  have hidx := A.card_mul_index
  rw [hi] at hidx
  have hpos := Nat.card_pos (α := frattini A)
  have h1 := Nat.mul_le_mul_left (Nat.card (P ⧸ frattini P)) hphi
  rw [←hPc,←hidx,hAc] at h1
  nlinarith

/-- Determinant one supplies the required two-rank bound for the natural action. -/
public theorem special_degree_four_frattini_le_thirtytwo
    {F P : Type*} [Field F] [Group P] [Finite P]
    (hP : IsPGroup 2 P) (r : P →* GL (Fin 4) F)
    (hr : Function.Injective r) (h2 : (2 : F) ≠ 0)
    (hdet : ∀ g, Matrix.GeneralLinearGroup.det (r g) = 1) :
    Nat.card (P ⧸ frattini P) ≤ 32 := by
  exact degree_four_frattini_le_thirtytwo_of_twoRank_le_three hP
    ((generalLinearNatural 4).comp r) ((generalLinearNatural_injective 4).comp hr) h2
    (by simp) (Theory.SpecificGroups.OddFourRank.twoRank_le_three r hr h2 hdet)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Generation.OddNormalizer.SpecialFourFrattini
