module

public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.FixedQuotient
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ComponentReduction.NaturalClosure.ChiefExclusion.Flags
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order

/-!
# The sharp 3m lower dimension bound for a natural component

Binary Zsigmondy supplies a prime of multiplicative order 3m. Oddness of m
excludes the exceptional exponent six. This prime divides the SL₃(2^m)
order and does not divide its scalar kernel. The actual natural marking
therefore gives a prime divisor of the component order of binary degree 3m.
Every nontrivial representation of this centerless quasisimple component is
faithful, so the checked binary general-linear order bound gives dimension
at least 3m, without an irreducibility assumption.

The consumers are the literal noncentral sections of `InvariantChiefFlag`
and the original quotient V/C_V(C_A(L)). The latter uses the proved
nontrivial quotient action, once the first strict rank comparison is supplied.
No minimum-dimension or quotient-dimension premise is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.5.9,
printed p.108, the dimension estimates before (!) and (!!). The alternative
primitive-prime proof uses the proved binary specialization of GLS2,
Chapter A, Theorem 1.1 and the actual SL₃/PSL₃ order comparison.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
open QuasisimpleSource
set_option backward.isDefEq.respectTransparency false
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

omit [Finite G] in
theorem seed_prime_degree {A L : Subgroup G} (s : NaturalSeed ρ A L) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card L ∧
      orderOf (2 : ZMod p) = 3 * s.field.degree := by
  have hpos := s.field.degree_pos
  have hodd := s.odd_degree
  obtain ⟨p, hp, ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two
    (m := 3 * s.field.degree) (by omega) (by obtain ⟨k, hk⟩ := hodd; omega)
  have hp2 : p ≠ 2 := by
    intro he; subst p
    change orderOf (0 : ZMod 2) = _ at ho
    rw [orderOf_zero] at ho
    omega
  have hp3 : p ≠ 3 := by
    intro he; subst p
    rw [Representation.BinaryPrimeDegree.orderOf_two_mod_three] at ho
    omega
  have hdiv : p ∣ (2 ^ s.field.degree) ^ 3 - 1 := by
    have he : (2 : ZMod p) ^ (3 * s.field.degree) = 1 := by
      rw [← ho]
      exact pow_orderOf_eq_one _
    apply (ZMod.natCast_eq_zero_iff _ p).mp
    rw [Nat.cast_sub (Nat.one_le_pow _ _ (by positivity)), Nat.cast_pow, Nat.cast_pow,
      Nat.cast_ofNat, Nat.cast_one, ← pow_mul, Nat.mul_comm s.field.degree 3, he, sub_self]
  let F := s.field.Carrier
  have hz : center (Matrix.SpecialLinearGroup (Fin 3) F) = ⊥ := by
    apply Subgroup.card_eq_one.mp
    rw [← Nat.card_congr (Subgroup.centerCongr s.natural.groupEquiv).toEquiv,
      seed_center_eq_bot ρ s]
    simp
  let e := s.natural.groupEquiv.trans (Matrix.SL3.equivProjectiveOfCenterEqBot F hz)
  refine ⟨p, hp, hp2, ?_, ho⟩
  rw [Nat.card_congr e.toEquiv]
  have hcard := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
  rw [s.field.card_eq] at hcard
  have hd : p ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) *
      Nat.gcd 3 (2 ^ s.field.degree - 1) := by
    rw [hcard]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hdiv _) _
  rcases hp.dvd_mul.mp hd with h | h
  · exact h
  · have h3 : p ∣ 3 := h.trans (Nat.gcd_dvd_left _ _)
    exact (hp3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h3 |>.resolve_left hp.ne_one)).elim

theorem natural_component_min_degree {A L : Subgroup G} (s : NaturalSeed ρ A L)
    (hL : IsComponent G L) {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] (τ : Representation (ZMod 2) L W) (hne : τ ≠ 1) :
    3 * s.field.degree ≤ Module.finrank (ZMod 2) W := by
  let : IsQuasisimple L := hL.2
  have hk : τ.asGroupHom.ker = ⊥ := by
    rcases IsQuasisimple.normal_le_center_or_eq_top τ.asGroupHom.ker with hc | ht
    · exact bot_unique (hc.trans (seed_center_eq_bot ρ s).le)
    · exfalso
      apply hne
      ext l w
      have hl : l ∈ τ.asGroupHom.ker := by rw [ht]; exact mem_top _
      exact congrArg (fun f : (W →ₗ[ZMod 2] W)ˣ => (f : W →ₗ[ZMod 2] W) w) hl
  have hf : Function.Injective τ := by
    intro x y h
    exact (MonoidHom.ker_eq_bot_iff τ.asGroupHom).mp hk (Units.ext h)
  obtain ⟨p, hp, hp2, hd, ho⟩ := seed_prime_degree ρ s
  rw [← ho]
  exact Representation.BinaryPrimeDegree.orderOf_le_finrank τ hf hp hp2 hd

theorem InvariantChiefFlag.factorDimension_lower [Module.Finite (ZMod 2) V]
    {A L : Subgroup G} (s : NaturalSeed ρ A L) (hL : IsComponent G L)
    {S : Submodule (ZMod 2) V} (f : InvariantChiefFlag ρ A L S)
    {i : ℕ} (hi : i ∈ f.noncentral) : 3 * s.field.degree ≤ f.factorDimension i := by
  apply natural_component_min_degree ρ s hL
    (sectionRepresentation (ρ.comp L.subtype) (f.term i) (f.term (i + 1)))
  intro he
  apply (f.noncentral_mem.mp hi).2
  intro l v
  exact DFunLike.congr_fun (DFunLike.congr_fun he l) v

theorem SecondComponent.centralizer_fixedCodim_lower [Module.Finite (ZMod 2) V]
    {K : GroupClass} {A L : Subgroup G} (setup : Setup ρ K A)
    (s : NaturalSeed ρ A L) (hL : IsComponent G L) (d : SecondComponent ρ A L)
    (hgt : 2 * s.field.degree < rank A) :
    3 * s.field.degree ≤ fixedCodim ρ (A ⊓ centralizer (L : Set G)) :=
  natural_component_min_degree ρ s hL (offenderCentralizerFixed ρ A L).quotientRepresentation
    (d.centralizerQuotient_nontrivial_of_rank_gt ρ setup s hL hgt)

end CFSG.Quasithin.ChapterB.SourceInduction.ComponentReduction.NaturalClosure
