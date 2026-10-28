module
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.CyclotomicSylow
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.ShortBlock
public import Theory.GroupAction.ComponentRankAction.ResidualSource
public import Theory.GroupTheory.PrimeRankCyclicSylow
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Quotient
public import BenderSuzuki.External.Huppert.II.theorem_6_14

/-!
# Noncubic field actors in binary G₂ components

For p > 3, a rank-two prime divides q²−1: the remaining cyclotomic Sylow
subgroups are cyclic, using either the actual cubic torus or the faithful
six-dimensional natural action. The commuting short and long SL₂ factors
supply elementary order p². The field fixed-point congruence retains the
quadratic prime divisor, so the same construction lies in a prime-order
field actor's fixed group. Such an outer actor forces rank three.

Thus every ambient p-element belongs to the original component when its
p-rank and the ambient p-rank are two and its center is prime to p. The
argument includes G₂(4) and keeps the central quotient marking. Its literal
source application is in NonblockEndgameSieveModelsNoncubicLie.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and 4.3.12(2), p.617.
The imported octonion model, root maps and order calculation retain their
ATLAS attribution; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup
open scoped MatrixGroups
noncomputable section
namespace Atlas.G2.NoncubicFieldActors
open LieAutomorphismExtensions Theory.GroupAction.ComponentRankAction
open MultiplierOrdinary.Nondefining.CyclotomicSylow
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {p : ℕ} [Fact p.Prime]

/-- Outside the quadratic torus factors the noncubic Sylow subgroups are cyclic. -/
theorem quadratic_dvd_of_rank_two (hF : 2 < Nat.card F) (hp3 : 3 < p)
    (hr : 2 ≤ primeRank p (Model F)) : p ∣ Nat.card F^2 - 1 := by
  by_contra hquad
  have hd : p ∣ Nat.card (Model F) := by
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    omega
  let P : Sylow p (Model F) := default
  have hc : IsCyclic P := by
    rcases cyclotomic_alternatives hp3 hquad hd with hcub | htwist
    · exact sylow_isCyclic_of_dvd_cubic hp3 hquad hcub P
    · let := Fintype.ofFinite F
      have hpF : (p : F) ≠ 0 :=
        CharP.cast_ne_zero_of_ne_of_prime F (Fact.out : p.Prime) (by omega : 2 ≠ p)
      apply Representation.CyclotomicPrimeCyclicity.isCyclic_of_minimal_degree
        P.isPGroup' hpF
        (by simpa only [Nat.card_eq_fintype_card] using not_dvd_card_field (F := F) hp3)
        ((Natural.action F).comp (P : Subgroup (Model F)).subtype)
        ((natural_action_injective hF).comp (P : Subgroup (Model F)).subtype_injective)
      rw [Natural.finrank_space, ← Nat.card_eq_fintype_card,
        orderOf_card_of_dvd_twisted hp3 hquad htwist]
  have hb := P.primeRank_le_one_of_isCyclic hc
  omega

/-- Two commuting SL₂ planes supply independent prime-order subgroups. -/
theorem exists_elementary_quadratic (hd : p ∣ Nat.card F^2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' (G := SL(2,F)) p (by
    rw [BenderSuzuki.External.huppert614_card_specialLinearGroup]
    exact dvd_mul_of_dvd_right hd _)
  let P := zpowers a
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let f : P × P →* Model F :=
    MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom.comp
      (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom_injective he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,inferInstance,?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod,Nat.card_zpowers,ha,pow_two]

omit [CharP F 2] in
private theorem fixed_quadratic_dvd (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F^2 - 1) :
    p ∣ Nat.card (EvenFieldFixedResidual.fixedField σ)^2 - 1 := by
  let P := zpowers σ
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hσ,pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield P F) [MOD p] at hc
  change Nat.card F ≡ Nat.card (EvenFieldFixedResidual.fixedField σ) [MOD p] at hc
  have hh := Nat.ModEq.sub_right (a := 1)
    (Nat.one_le_pow _ _ Nat.card_pos) (Nat.one_le_pow _ _ Nat.card_pos) (hc.pow 2)
  exact Nat.modEq_zero_iff_dvd.mp (hh.symm.trans hd.modEq_zero_nat)

/-- Prime-order field actors fix an actual elementary subgroup of order p². -/
theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F^2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAction σ).fixedSubgroup := by
  obtain ⟨B,hB,hcard⟩ := exists_elementary_quadratic (fixed_quadratic_dvd σ hσ hd)
  let := hB
  let f : Model (EvenFieldFixedResidual.fixedField σ) →* Model F :=
    (fieldAction σ).fixedSubgroup.subtype.comp (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAction σ).fixedSubgroup.subtype_injective.comp (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((EvenFieldFixedResidual.coefficientFixedEquiv σ).symm b).property

/-- Adjoining an outer field actor to its fixed elementary p² forces rank three. -/
theorem field_actor_rank_three (hF : 2 < Nat.card F) (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAction σ ∈ A)
    (hd : p ∣ Nat.card F^2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hd
  let := hE
  let f : Model F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hF))
      (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAction σ,hσA⟩
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAction fieldAction_injective σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAction σ ∈ MulAut.innerSubgroup (Model F) :=
      ⟨g,congrArg Subtype.val he⟩
    obtain ⟨u,hu⟩ := hi
    have hs := fieldAction_eq_conj_implies_one σ u hu.symm
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAction σ y * g⁻¹ = fieldAction σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- Every odd-prime-power actor is inner when that prime has model rank two. -/
theorem primePower_actor_inner (hF : 2 < Nat.card F) (hp3 : 3 < p)
    (hr : 2 ≤ primeRank p (Model F)) (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut (Model F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup (Model F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  have hd := quadratic_dvd_of_rank_two hF hp3 hr
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he⟩ := exists_inner_field hF a
  have hσ : σ ^ (p^m) = 1 := by
    have hh := congrArg (fieldComponent hF) ham
    rw [map_pow,he,fieldComponent_inner_field,map_one] at hh
    exact hh
  have hσA : fieldAction σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hp : IsPGroup p (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : p ∣ Nat.card (zpowers σ) := hp.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hn (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' p hdP
    have hτA : fieldAction (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAction (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three hF A hinner τ hτp hτA hd
    omega
  rw [he,hσone]
  have hh : fieldAction (1 : F ≃+* F) = 1 := fieldAction.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩

/-- The original component absorbs every ambient p-element, retaining its full center. -/
theorem component_eq_primeClosure_and_residual
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (hF : 2 < Nat.card F) (hp3 : 3 < p) (hz : Nat.Coprime p (Nat.card (center L)))
    (hr : 2 ≤ primeRank p L) (hG : primeRank p G ≤ 2)
    (e : L ⧸ center L ≃* Model F) :
    L = closure {x : G | orderOf x = p} ∧ L = primeToResidual p G := by
  let := hL.2
  have hrmodel : 2 ≤ primeRank p (Model F) := by
    rw [← primeRank_congr p e, ← primeRank_eq_of_surjective_of_coprime p
      (QuotientGroup.mk' (center L)) (QuotientGroup.mk'_surjective (center L))
      (by rwa [QuotientGroup.ker_mk'])]
    exact hr
  apply Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    hL hz hr hG e
  intro a ha m hm
  exact primePower_actor_inner hF hp3 hrmodel _ (inner_le_range L e)
    (range_rank_le_two L e hz hr hG) a ha ⟨m,hm⟩
end Atlas.G2.NoncubicFieldActors
