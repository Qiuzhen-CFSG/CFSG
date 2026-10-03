module

public import Theory.Representation.Maschke
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Tactic

/-!
# Nonsplit prime-order representations in dimension four

Over a finite field of even order `q`, the integer `q² + 1` is coprime to
`|GL(d,q)|` for `1 ≤ d ≤ 3`. Consequently a faithful representation of a
prime-order group in dimension four is irreducible if that prime divides
`q² + 1`: Maschke supplies a complement to any proper invariant subspace,
and one of the two restrictions must still be faithful.

This is the linear irreducibility input for the Singer-cycle argument in
Huppert--Blackburn, *Finite Groups III*, XI.3.10(a), printed pp. 190–191
(compare II.7.3). The proofs are extracted from the corresponding argument
in `BenderSuzuki.SE.Section11Lemma114Models`; this module has no dependency
on the SE development or on Suzuki groups.
-/

noncomputable section

namespace Representation

private theorem coprime_sq_add_one_factors
    (q : ℕ) (hq : 2 ≤ q) (hqeven : Even q) :
    Nat.Coprime (q ^ 2 + 1) q ∧
      Nat.Coprime (q ^ 2 + 1) (q - 1) ∧
      Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) ∧
      Nat.Coprime (q ^ 2 + 1) (q ^ 3 - 1) := by
  have hcop_qsq : Nat.Coprime (q ^ 2 + 1) (q ^ 2) := by
    have h := (Nat.coprime_add_self_left (m := 1) (n := q ^ 2)).2
      (Nat.coprime_one_left (q ^ 2))
    simpa [add_comm] using h
  have hcop_q : Nat.Coprime (q ^ 2 + 1) q :=
    hcop_qsq.coprime_dvd_right (dvd_pow_self q (by norm_num))
  have hq_sq_even : Even (q ^ 2) :=
    Nat.even_pow.mpr ⟨hqeven, by norm_num⟩
  have hq_sq_pos : 0 < q ^ 2 := by positivity
  have hq_sq_sub_one_odd : Odd (q ^ 2 - 1) :=
    Nat.Even.sub_odd hq_sq_pos hq_sq_even odd_one
  have hcop_qsq_sub : Nat.Coprime (q ^ 2 + 1) (q ^ 2 - 1) := by
    have h := (Nat.coprime_self_add_right
      (m := q ^ 2 - 1) (n := 2)).2 hq_sq_sub_one_odd.coprime_two_right
    have heq : q ^ 2 - 1 + 2 = q ^ 2 + 1 := by omega
    rw [heq] at h
    exact h.symm
  have hcop_q_sub : Nat.Coprime (q ^ 2 + 1) (q - 1) :=
    hcop_qsq_sub.coprime_dvd_right (by
      simpa using Nat.sub_dvd_pow_sub_pow q 1 2)
  have hcop_qsq_add_q :
      Nat.Coprime (q ^ 2 + 1) (q ^ 2 + q + 1) := by
    have h := (Nat.coprime_self_add_right
      (m := q ^ 2 + 1) (n := q)).2 hcop_q
    convert h using 1; ring
  have hfactor : q ^ 3 - 1 = (q - 1) * (q ^ 2 + q + 1) := by
    rw [Nat.sub_mul]
    have hqmul : q * (q ^ 2 + q + 1) = q ^ 3 + q ^ 2 + q := by ring
    rw [hqmul, one_mul]
    omega
  have hcop_qcube_sub : Nat.Coprime (q ^ 2 + 1) (q ^ 3 - 1) := by
    rw [hfactor]
    exact hcop_q_sub.mul_right hcop_qsq_add_q
  exact ⟨hcop_q, hcop_q_sub, hcop_qsq_sub, hcop_qcube_sub⟩

/-- The nonsplit factor in dimension four is coprime to the orders of all
general linear groups in positive dimension less than four. -/
public theorem coprime_sq_add_one_card_GL
    {K : Type*} [Field K] [Fintype K]
    (hq : 2 ≤ Fintype.card K) (hqeven : Even (Fintype.card K))
    (d : ℕ) (hdpos : 1 ≤ d) (hdle : d ≤ 3) :
    Nat.Coprime (Fintype.card K ^ 2 + 1)
      (Nat.card (GL (Fin d) K)) := by
  let q := Fintype.card K
  obtain ⟨hcopq, hcop1, hcop2, hcop3⟩ :=
    coprime_sq_add_one_factors q hq hqeven
  interval_cases d
  · rw [Matrix.card_GL_field]
    simpa [q] using hcop1
  · rw [Matrix.card_GL_field]
    have hq2q : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    simpa [Fin.prod_univ_two, q, hq2q] using
      hcop2.mul_right (hcopq.mul_right hcop1)
  · rw [Matrix.card_GL_field]
    have hq3q : q ^ 3 - q = q * (q ^ 2 - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    have hq3q2 : q ^ 3 - q ^ 2 = q ^ 2 * (q - 1) := by
      rw [Nat.mul_sub_left_distrib]
      ring_nf
    simpa [Fin.prod_univ_three, q, hq3q, hq3q2] using
      hcop3.mul_right
        (hcopq.mul_right hcop2) |>.mul_right
          (by simpa [pow_two] using
            (hcopq.mul_right hcopq).mul_right hcop1)

private theorem exists_isCompl_invariant_of_odd
    {A K V : Type*} [Group A] [Fintype A]
    [Field K] [CharP K 2]
    [AddCommGroup V] [Module K V]
    (hAodd : Odd (Fintype.card A))
    (rho : Representation K A V)
    (U : Submodule K V)
    (hU : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    ∃ W, IsCompl U W ∧ ∀ a : A, ∀ v ∈ W, rho a v ∈ W := by
  classical
  have hUinv : U ∈ rho.invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    intro a
    rw [Module.End.mem_invtSubmodule_iff_forall_mem_of_mem]
    exact hU a
  let Upack : rho.invtSubmodule := ⟨U, hUinv⟩
  let instAdd : AddCommGroup rho.asModule :=
    Representation.instAddCommGroupAsModule rho
  let : AddCommGroup rho.asModule := instAdd
  let instMod : Module (MonoidAlgebra K A) rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  let : Module (MonoidAlgebra K A) rho.asModule := instMod
  have : NeZero (Fintype.card A : K) := by
    constructor
    intro hzero
    have hdiv : 2 ∣ Fintype.card A :=
      (CharP.cast_eq_zero_iff K 2 (Fintype.card A)).1 hzero
    exact hAodd.not_two_dvd_nat hdiv
  let Umod : @Submodule (MonoidAlgebra K A) rho.asModule _
      instAdd.toAddCommMonoid instMod :=
    rho.mapSubmodule Upack
  obtain ⟨Wmod, hUWmod⟩ := @MonoidAlgebra.Submodule.exists_isCompl'
    K inferInstance A inferInstance inferInstance rho.asModule
      instAdd instMod inferInstance Umod
  let Wpack : rho.invtSubmodule := rho.mapSubmodule.symm Wmod
  let W : Submodule K V := Wpack
  refine ⟨W, ?_, ?_⟩
  · have hcompl_pack : IsCompl Upack Wpack := by
      exact (rho.mapSubmodule.isCompl_iff).2
        (by simpa [Umod, Wpack] using hUWmod)
    rw [isCompl_iff, disjoint_iff, codisjoint_iff] at hcompl_pack ⊢
    constructor
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.1
    · simpa [Upack, W] using congrArg Subtype.val hcompl_pack.2
  · intro a v hv
    have hmem := (Representation.mem_invtSubmodule (ρ := rho)).1 Wpack.2 a
    exact
      (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (rho a)).1 hmem v
        (by simpa [W] using hv)

/-- A faithful finite-dimensional representation gives the expected
divisibility by the order of the general linear group. -/
public theorem card_dvd_card_GL_of_injective
    {A K V : Type*} [Group A] [Finite A]
    [Field K] [Fintype K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K A V) (hrho : Function.Injective rho) :
    Nat.card A ∣ Nat.card (GL (Fin (Module.finrank K V)) K) := by
  let basis : Module.Basis (Fin (Module.finrank K V)) K V :=
    Module.finBasis K V
  let glEquiv : GL (Fin (Module.finrank K V)) K ≃*
      LinearMap.GeneralLinearGroup K V :=
    Matrix.GeneralLinearGroup.toLin' basis
  have hcard : Nat.card (LinearMap.GeneralLinearGroup K V) =
      Nat.card (GL (Fin (Module.finrank K V)) K) :=
    Nat.card_congr glEquiv.symm.toEquiv
  rw [← hcard]
  have hrhoUnits : Function.Injective rho.toHomUnits := by
    intro a b hab
    apply hrho
    exact congrArg Units.val hab
  exact Subgroup.card_dvd_of_injective rho.toHomUnits hrhoUnits

/-- A faithful prime-order representation in characteristic two and dimension
four is irreducible when the prime divides q squared plus one. -/
public theorem invariant_eq_bot_or_top_of_prime_card_dvd_sq_add_one
    {A K V : Type*} [Group A] [Fintype A]
    [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (r : ℕ) (hr : r.Prime) (hrne2 : r ≠ 2)
    (hAcard : Nat.card A = r)
    (rho : Representation K A V) (hrho : Function.Injective rho)
    (hfinrank : Module.finrank K V = 4)
    (hrdiv : r ∣ Fintype.card K ^ 2 + 1)
    (hq : 2 ≤ Fintype.card K) (hqeven : Even (Fintype.card K))
    (U : Submodule K V)
    (hUinv : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  by_cases hUbot : U = ⊥
  · exact Or.inl hUbot
  by_cases hUtop : U = ⊤
  · exact Or.inr hUtop
  exfalso
  have hAodd : Odd (Fintype.card A) := by
    rw [← Nat.card_eq_fintype_card, hAcard]
    exact hr.odd_of_ne_two hrne2
  obtain ⟨W, hUW, hWinv⟩ :=
    exists_isCompl_invariant_of_odd hAodd rho U hUinv
  have hWbot : W ≠ ⊥ := by
    intro hbot
    apply hUtop
    have hsup : U ⊔ W = ⊤ := codisjoint_iff.mp hUW.2
    simpa [hbot] using hsup
  have hUpos : 1 ≤ Module.finrank K U :=
    Submodule.one_le_finrank_iff.mpr hUbot
  have hWpos : 1 ≤ Module.finrank K W :=
    Submodule.one_le_finrank_iff.mpr hWbot
  have hsum : Module.finrank K U + Module.finrank K W = 4 := by
    simpa [hfinrank] using Submodule.finrank_add_eq_of_isCompl hUW
  have hUle : Module.finrank K U ≤ 3 := by omega
  have hWle : Module.finrank K W ≤ 3 := by omega
  let rhoU : Representation K A U :=
    rho.subrepresentation U (by
      intro a v hv
      exact hUinv a v hv)
  let rhoW : Representation K A W :=
    rho.subrepresentation W (by
      intro a v hv
      exact hWinv a v hv)
  let : Fact (Nat.Prime (Nat.card A)) := ⟨by rw [hAcard]; exact hr⟩
  rcases rhoU.ker.eq_bot_or_eq_top_of_prime_card with hkerU | hkerU
  · have hinjU : Function.Injective rhoU :=
      (MonoidHom.ker_eq_bot_iff rhoU).mp hkerU
    have hdvd :=
      card_dvd_card_GL_of_injective rhoU hinjU
    rw [hAcard] at hdvd
    have hcop := coprime_sq_add_one_card_GL hq hqeven
      (Module.finrank K U) hUpos hUle
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrdiv hdvd)
  · have hUfix (a : A) (u : U) : rho a (u : V) = (u : V) := by
      have ha : a ∈ rhoU.ker := by
        rw [hkerU]
        trivial
      have ha' : rhoU a = (1 : Module.End K U) := ha
      have hau := congrArg (fun f : Module.End K U => f u) ha'
      exact congrArg Subtype.val (by simpa [rhoU] using hau)
    have hinjW : Function.Injective rhoW := by
      intro a b hab
      apply hrho
      apply LinearMap.ext
      intro v
      have hv : v ∈ U ⊔ W := by
        rw [codisjoint_iff.mp hUW.2]
        trivial
      rcases Submodule.mem_sup.mp hv with ⟨u, hu, w, hw, huw⟩
      rw [← huw]
      have hu_a := hUfix a ⟨u, hu⟩
      have hu_b := hUfix b ⟨u, hu⟩
      have hw_ab : rho a w = rho b w := by
        have habw := congrArg
          (fun f : Module.End K W => f ⟨w, hw⟩) hab
        exact congrArg Subtype.val (by simpa [rhoW] using habw)
      calc
        rho a (u + w) = rho a u + rho a w := map_add _ _ _
        _ = u + rho a w := by rw [hu_a]
        _ = u + rho b w := by rw [hw_ab]
        _ = rho b u + rho b w := by rw [hu_b]
        _ = rho b (u + w) := (map_add _ _ _).symm
    have hdvd :=
      card_dvd_card_GL_of_injective rhoW hinjW
    rw [hAcard] at hdvd
    have hcop := coprime_sq_add_one_card_GL hq hqeven
      (Module.finrank K W) hWpos hWle
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrdiv hdvd)

/-- Every nontrivial group of order dividing `q² + 1` acts irreducibly in
any faithful four-dimensional representation over a field of even order `q`.
It suffices to restrict to a subgroup of prime order. -/
public theorem invariant_eq_bot_or_top_of_card_dvd_sq_add_one
    {A K V : Type*} [Group A] [Finite A] [Nontrivial A]
    [Field K] [Fintype K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (rho : Representation K A V) (hrho : Function.Injective rho)
    (hfinrank : Module.finrank K V = 4)
    (hcard : Nat.card A ∣ Fintype.card K ^ 2 + 1)
    (hq : 2 ≤ Fintype.card K) (hqeven : Even (Fintype.card K))
    (U : Submodule K V)
    (hUinv : ∀ a : A, ∀ v ∈ U, rho a v ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  classical
  obtain ⟨r, hr, hrA⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (Finite.one_lt_card (α := A)))
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := A) r hrA
  let Z := Subgroup.zpowers z
  let : Fintype Z := Fintype.ofFinite Z
  have hZ : Nat.card Z = r := by
    rw [Nat.card_zpowers, hz]
  have hrdiv := dvd_trans hrA hcard
  have hrne : r ≠ 2 := by
    intro heq
    rw [heq] at hrdiv
    have hodd : Odd (Fintype.card K ^ 2 + 1) :=
      (hqeven.pow_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)).add_odd odd_one
    exact hodd.not_two_dvd_nat hrdiv
  apply invariant_eq_bot_or_top_of_prime_card_dvd_sq_add_one
    r hr hrne hZ (rho.comp Z.subtype) (hrho.comp Z.subtype_injective)
    hfinrank hrdiv hq hqeven U
  intro a v hv
  exact hUinv a v hv

end Representation
