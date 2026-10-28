module

public import BenderSuzuki.External.Huppert.II.theorem_10_13
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Models
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.Models
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ResidualCentralizers.ComponentExtension.EmbeddingReduction.ModelSeparation
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.SignedReduction.ModelIntersection.LieParameters.Orders
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup
public import Theory.SpecificGroups.SU3.FixedFieldTwo

/-!
# The signed exceptions in the rank-two proof of 13.6.20

All reduced carriers have order dividing 2¹⁰ · 3³ · 5 · 7 · 31. The cube
of the signed field parameter divides the projective order. The source
congruence therefore leaves only q = 2, 4, or 8. Perfectness excludes PSU₃(2),
and the order of PSU₃(8) excludes q = 8. The remaining PSL₃(4) has order
20160: all reduced models except PSL₄(2) are excluded by order, and the
proved A₈–PSL₃(4) Sylow-center distinction excludes PSL₄(2).

The symplectic and G₂ models retain their derived-group carriers; the
hexacode model retains its central triple cover. We use inherited
quasisimplicity, without independently certifying the whole model list.
The special-to-projective comparisons use the actual central quotient
and, for SU₃, the scalar kernel of the natural projective map.

The final application uses the literal image of K in H/O₃′(H) for
H = K ⊔ Lᵥ, and the actual K+. Its common-simple-factor equivalence and
quasisimplicity of the image remain inputs of the independent local
A.3.18 application. Only A.3.18(2) and (3b) are excluded: (3a), which gives
the theta identity, is preserved.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, A.3.18,
printed pp.51–53, and the rank-two line of 13.6.20, printed p.931.
Order and exceptional-isomorphism calculations reuse the attributed
ATLAS ports and checked matrix-group results in the imported modules.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
open ComponentSelection Chapter1.Section02.LocalModels
open Chapter15.Section03.Candidates.SignedReduction.ModelIntersection
open BenderSuzuki.MatrixGroups

private theorem parameter_cases {S : Type*} [Group S] {unitary : Bool} {q : ℕ}
    (h : IsPSLSign S unitary 3 q)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hc : Nat.card S ∣ 29998080) : q = 2 ∨ q = 4 ∨ q = 8 := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp (signed_parameter_primePower h)
  have hpq : p ∣ q := hpn ▸ dvd_pow_self p (by omega : n ≠ 0)
  have hp3 : p ≠ 3 := by
    intro he
    have := Nat.dvd_iff_mod_eq_zero.mp (he ▸ hpq)
    cases unitary <;> simp_all
  have hcube : p ^ 3 ∣ 29998080 :=
    (pow_dvd_pow_of_dvd hpq 3).trans ((signed_parameter_cube_dvd h).trans hc)
  have hd : p ∣ 2 ^ 10 * 3 ^ 3 * 5 * 7 * 31 :=
    (dvd_pow_self p (by decide : 3 ≠ 0)).trans hcube
  simp only [hp.dvd_mul, hp.prime.dvd_pow_iff_dvd (by decide : 10 ≠ 0),
    hp.prime.dvd_pow_iff_dvd (by decide : 3 ≠ 0),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 2),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 5),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 7),
    Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 31)] at hd
  have hp2 : p = 2 := by
    rcases hd with (((he | he) | he) | he) | he
    · exact he
    · exact (hp3 he).elim
    all_goals subst p; norm_num at hcube
  subst p
  have hn4 : n < 4 := by
    by_contra! hn4
    have h16 : 16 ∣ q := by
      rw [← hpn]
      exact pow_dvd_pow 2 hn4
    have : (16 : ℕ) ^ 3 ∣ 29998080 :=
      (pow_dvd_pow_of_dvd h16 3).trans ((signed_parameter_cube_dvd h).trans hc)
    norm_num at this
  interval_cases n <;> norm_num at hn hpn ⊢ <;> omega

private theorem unitary_card {S : Type*} [Group S] {q : ℕ}
    (h : IsPSLSign S true 3 q) :
    Nat.card S = (q ^ 3 + 1) * q ^ 3 * (q ^ 2 - 1) / Nat.gcd 3 (q + 1) := by
  have hpp := signed_parameter_primePower h
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpp
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    rw [← hpn] at hc hconj ⊢
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hc hconj
  rw [Nat.card_congr e.toEquiv]
  exact Representation.SU3.BinaryDegree.card_projective J hc hfixed

private theorem only_linear_four {S : Type*} [Group S] [Group.IsPerfect S] [Nontrivial S]
    {unitary : Bool} {q : ℕ} (h : IsPSLSign S unitary 3 q)
    (hmod : q % 3 = (if unitary then 2 else 1))
    (hc : Nat.card S ∣ 29998080) : unitary = false ∧ q = 4 := by
  rcases parameter_cases h hmod hc with rfl | rfl | rfl
  · cases unitary with
    | false => norm_num at hmod
    | true =>
      obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
      let := BenderSuzuki.MatrixGroups.HermitianForm.FixedFieldTwo.projective_isSolvable
        J hcard hconj
      have hs : Group.IsSolvable S :=
        Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
      exact (Group.IsPerfect.not_isSolvable S hs).elim
  · cases unitary <;> simp_all
  · cases unitary with
    | false => norm_num at hmod
    | true =>
      rw [unitary_card h] at hc
      norm_num at hc

private theorem reduced_card_dvd {Q : Type*} [Group Q]
    (h : ReducedModel Q) : Nat.card Q ∣ 29998080 := by
  cases h with
  | linear n hn he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    let : NeZero n := ⟨by omega⟩
    have hc := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) n
    obtain ⟨hlo, hhi⟩ := hn
    interval_cases n
    all_goals
      norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
        Fin.prod_univ_zero, Nat.gcd_one_right] at hc
      simp only [mul_one] at hc
      rw [hc]
      norm_num
  | symplectic he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv]
    apply (card_subgroup_dvd_card _).trans
    rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two]
    norm_num
  | g2 he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H]
    norm_num
  | ahat6 he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Atlas.Codes.hexEven_card]
    norm_num
  | a7 he =>
    obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
    norm_num

private noncomputable def binary_quotient_equiv {Q : Type*} [Group Q] {n : ℕ}
    (hn : 0 < n) (e : Q ≃* PSL(n, ZMod 2)) :
    (Q ⧸ center Q) ≃* PSL(n, ZMod 2) := by
  have hz : center Q = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr (e.trans
      (BinaryLinear.OuterCyclic.projectiveEquivSL hn))).toEquiv,
      BinaryLinear.OuterCyclic.binary_center_eq_bot hn, Subgroup.card_bot]
  exact ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans e

private theorem reduced_not_psl_four {Q : Type*} [Group Q] [Finite Q]
    (h : ReducedModel Q) {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (e : (Q ⧸ center Q) ≃* PSL(3,F)) : False := by
  have hc : Nat.card (Q ⧸ center Q) = 20160 := by
    rw [Nat.card_congr e.toEquiv]
    have ho := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    norm_num [hF, Fin.prod_univ_succ] at ho
    omega
  have hle := Nat.le_of_dvd Nat.card_pos (center Q).card_quotient_dvd_card
  rw [hc] at hle
  cases h with
  | linear n hn he =>
    obtain ⟨f⟩ := he
    let g := binary_quotient_equiv (by omega : 0 < n) f
    obtain ⟨hlo, hhi⟩ := hn
    interval_cases n
    · have ho := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 3
      norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
        Fin.prod_univ_zero, Nat.gcd_one_right] at ho
      simp only [mul_one] at ho
      rw [Nat.card_congr g.toEquiv, ho] at hc
      omega
    · exact CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.ComponentExtension.EmbeddingReduction.ModelSeparation.alt8_not_equiv_psl3Card4 hF
        ⟨(Atlas.Comparisons.Exceptional.alt8EquivPSL4Two.trans g.symm).trans e⟩
    · have ho := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) 5
      norm_num only [Nat.card_zmod, Fin.prod_univ_succ, Fin.val_zero, Fin.val_succ,
        Fin.prod_univ_zero, Nat.gcd_one_right] at ho
      simp only [mul_one] at ho
      rw [Nat.card_congr g.toEquiv, ho] at hc
      omega
  | symplectic he =>
    obtain ⟨f⟩ := he
    rw [Nat.card_congr f.toEquiv] at hle
    have hh := Nat.le_of_dvd Nat.card_pos
      (card_subgroup_dvd_card (commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))))
    rw [Theory.SpecificGroups.SymplecticFour.Binary.card_sp_two] at hh
    omega
  | g2 he =>
    obtain ⟨f⟩ := he
    rw [Nat.card_congr f.toEquiv, Atlas.G2.BinaryParabolicPair.commutator_eq_longRootClosure,
      Atlas.G2.BinaryException.card_H] at hle
    omega
  | ahat6 he =>
    obtain ⟨f⟩ := he
    rw [Nat.card_congr f.toEquiv, Atlas.Codes.hexEven_card] at hle
    omega
  | a7 he =>
    obtain ⟨f⟩ := he
    rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup] at hle
    norm_num at hle

private noncomputable def centerQuotientCongr {R S : Type*} [Group R] [Group S]
    (e : R ≃* S) : (R ⧸ center R) ≃* (S ⧸ center S) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro y hy
      exact ⟨e.symm y, (centerCongr e.symm ⟨y, hy⟩).property, e.apply_symm_apply y⟩)

private theorem unitary_center_of_perfect {F : Type} [Field F] [Finite F]
    (J : HermitianForm 3 F) [Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J)]
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    center (ProjectiveSpecialUnitaryMatrixGroup J) = ⊥ := by
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hpp : IsPrimePow q := by
    let := Fintype.ofFinite F
    apply (isPrimePow_pow_iff (by decide : 2 ≠ 0)).mp
    simpa only [← Nat.card_eq_fintype_card, hcard] using FiniteField.isPrimePow_card F
  have hq : 2 < q := by
    have := hpp.one_lt
    by_contra! hq
    have htwo : q = 2 := by omega
    subst q
    have hc := HermitianForm.FixedFieldTwo.card_projective J hcard hconj
    let : Nontrivial (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact Group.IsPerfect.not_isSolvable _
      (HermitianForm.FixedFieldTwo.projective_isSolvable J hcard hconj)
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hpp
  let : Fact p.Prime := ⟨hp⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    rw [← hpn] at hcard hconj ⊢
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hcard hconj
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    BenderSuzuki.External.huppert_II_10_13 J q hq hcard hfixed
  rcases (inferInstance : (center (ProjectiveSpecialUnitaryMatrixGroup J)).Normal).eq_bot_or_eq_top
      with h | h
  · exact h
  · exact (Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h)).elim

/-- The actual SL/SU central quotient has the same projective sign and parameter.
Perfectness, inherited from the component, excludes the solvable unitary endpoint. -/
theorem quotient_isPSLSign_of_special {R : Type*} [Group R] [Group.IsPerfect R]
    {unitary : Bool} {q : ℕ} (h : IsSLSign R unitary 3 q) :
    IsPSLSign (R ⧸ center R) unitary 3 q := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    exact ⟨F, inferInstance, inferInstance, hc, ⟨centerQuotientCongr e⟩⟩
  | true =>
    obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h
    let : Group.IsPerfect J.specialSubgroup := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective J.specialToProjective_surjective
    have hk := J.specialToProjective_ker_eq_center (unitary_center_of_perfect J hc hconj)
    let f : (J.specialSubgroup ⧸ center J.specialSubgroup) ≃*
        ProjectiveSpecialUnitaryMatrixGroup J :=
      (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
          J.specialToProjective_surjective)
    exact ⟨F, inferInstance, inferInstance, J, hc, hconj, ⟨(centerQuotientCongr e).trans f⟩⟩

private theorem signed_projective_center_eq_bot {R : Type*} [Group R] [Group.IsPerfect R]
    {unitary : Bool} {q : ℕ} (h : IsPSLSign R unitary 3 q) : center R = ⊥ := by
  cases unitary with
  | false =>
    obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
    let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      Group.IsPerfect.center_quotient_center_eq_bot, Subgroup.card_bot]
  | true =>
    obtain ⟨F, _, _, J, hc, hconj, ⟨e⟩⟩ := h
    let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    apply Subgroup.card_eq_one.mp
    rw [Nat.card_congr (centerCongr e).toEquiv,
      unitary_center_of_perfect J hc hconj, Subgroup.card_bot]

/-- A perfect signed projective model is centerless, so its actual central
quotient retains the given sign and field parameter. -/
theorem quotient_isPSLSign_of_projective {R : Type*} [Group R] [Group.IsPerfect R]
    {unitary : Bool} {q : ℕ} (h : IsPSLSign R unitary 3 q) :
    IsPSLSign (R ⧸ center R) unitary 3 q := by
  exact CFSG.Quasithin.Chapter15.Section03.Candidates.SignedReduction.ModelIntersection.signed_transport h
    ((QuotientGroup.quotientMulEquivOfEq (signed_projective_center_eq_bot h)).trans
      QuotientGroup.quotientBot)

/-- No central quotient of a quasisimple reduced model is a signed degree-three
model with the congruence occurring in A.3.18(2) and (3b). -/
theorem reduced_quotient_not_signed {Q : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    (hmodel : ReducedModel Q) (unitary : Bool) (q : ℕ)
    (hmod : q % 3 = (if unitary then 2 else 1)) :
    ¬ IsPSLSign (Q ⧸ center Q) unitary 3 q := by
  intro h
  let : IsSimpleGroup (Q ⧸ center Q) := IsQuasisimple.simple
  obtain ⟨rfl, rfl⟩ := only_linear_four h hmod
    ((center Q).card_quotient_dvd_card.trans (reduced_card_dvd hmodel))
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  exact reduced_not_psl_four hmodel hF e

/-- Both signed exceptions are impossible when the component image and a
reduced model have the supplied common simple factor. -/
theorem common_factor_not_signed {Q R : Type*} [Group Q] [Finite Q] [IsQuasisimple Q]
    [Group R] [Group.IsPerfect R] (hmodel : ReducedModel Q)
    (e : (R ⧸ center R) ≃* (Q ⧸ center Q))
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1)) :
    ¬ (IsPSLSign R unitary 3 q ∨ IsSLSign R unitary 3 q) := by
  intro h
  apply reduced_quotient_not_signed hmodel unitary q hmod
  apply signed_transport (e := e.symm)
  rcases h with h | h
  · exact quotient_isPSLSign_of_projective h
  · exact quotient_isPSLSign_of_special h

variable {G : Type*} [Group G] [Finite G]

/-- The signed exclusions for the literal component image in H/O₃′(H),
where H = K ⊔ Lᵥ, and the literal K+ carrier. Quasisimplicity of R and the
common-simple-factor equivalence are supplied by the independent local
A.3.18 application. The source A.3.18(3a) theta alternative is retained. -/
theorem source_signed_exclusions (K L T : Subgroup G) (z v : G)
    (hL : Tv T v ≤ normalizer (Lv L v : Set G))
    (hz : Tv T v ≤ centralizer ({z} : Set G))
    (hK : K ∈ Yz L T z v)
    (hcore : pCore 2 (Gplus K L T z v hL hz) = ⊥)
    (hmodel : ReducedModel (plusImage K L T z v hL hz K))
    (unitary : Bool) (q : ℕ) (hmod : q % 3 = (if unitary then 2 else 1)) :
    let H := K ⊔ Lv L v
    let R := (K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 3 H))
    IsQuasisimple R →
    ((R ⧸ center R) ≃* ((plusImage K L T z v hL hz K) ⧸
      center (plusImage K L T z v hL hz K))) →
    ¬ (IsPSLSign R unitary 3 q ∨ IsSLSign R unitary 3 q) := by
  dsimp only
  intro hR e
  let := hR
  let := plusImage_K_quasisimple K L T z v hL hz hK hcore
  exact common_factor_not_signed hmodel e unitary q hmod

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo
