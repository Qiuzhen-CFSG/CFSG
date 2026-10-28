module
public import Theory.AtlasPort.LinearGroups.G2.EvenThreeRank
public import Theory.AtlasPort.LinearGroups.G2.EvenFieldFixedResidual.Descent
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.AutomorphismDescription
public import Theory.GroupTheory.PrimeRankFixedJoin
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Injective
public import Theory.GroupTheory.PrimeRankInvolutionLift
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Cubic field actors of characteristic-two G₂

The native rank theorem supplies an elementary subgroup of order nine over
any finite characteristic-two field. Descent through the literal coefficient
fixed field puts an elementary nine in every field-automorphism fixed group,
including when the fixed field is F₂.

For the ambient field of order greater than two, the inner action is faithful.
A cubic field actor therefore joins the fixed inner elementary nine to form
an elementary group of order 27. An automorphism subgroup containing all
inner automorphisms and having three-rank at most two excludes that actor.
The full inner–field decomposition and its field-component homomorphism
then show that every three-power actor in the subgroup is inner.

The final theorem retains an original action homomorphism. Its component
and containing-overgroup hypotheses are discharged in the source application.
Source: Aschbacher–Smith A.3.18, printed pp.51–53, and the G₂ case of
14.2.15, printed pp.985–986.
-/

public section
noncomputable section
open Subgroup
namespace Atlas.G2.CubicFieldActors
open LieAutomorphismExtensions
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The native cubic-rank theorem supplies elementary order nine. -/
theorem exists_elementary_cubic :
    ∃ E : Subgroup (Model F), IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 := by
  obtain ⟨E,hE,hcard⟩ := exists_elementaryAbelian_card_primeRank
    (G := Model F) (p := 3)
  let := hE
  have hd : 3^2 ∣ Nat.card E := by
    rw [hcard]
    exact Nat.pow_dvd_pow 3 EvenThreeRank.two_le_primeRank
  obtain ⟨B,hB⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) 3 hd
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.of_injective B.subtype B.subtype_injective
  refine ⟨B.map E.subtype,IsElementaryAbelian.map E.subtype,?_⟩
  rw [card_map_of_injective E.subtype_injective,hB]

/-- Cubic rank two holds over every finite characteristic-two coefficient field. -/
theorem cubic_rank : 2 ≤ primeRank 3 (Model F) := EvenThreeRank.two_le_primeRank

/-- The coefficient-fixed group contains elementary order nine, including
when the literal fixed field is F₂. -/
theorem exists_fixed_elementary_cubic (σ : F ≃+* F) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 ∧
      E ≤ (fieldAction σ).fixedSubgroup := by
  obtain ⟨B,hB,hcard⟩ := exists_elementary_cubic (F := EvenFieldFixedResidual.fixedField σ)
  let := hB
  let f : Model (EvenFieldFixedResidual.fixedField σ) →* Model F :=
    (fieldAction σ).fixedSubgroup.subtype.comp
      (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAction σ).fixedSubgroup.subtype_injective.comp
      (EvenFieldFixedResidual.coefficientFixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((EvenFieldFixedResidual.coefficientFixedEquiv σ).symm b).property

/-- A cubic coefficient actor enlarges the fixed inner elementary nine to
three-rank at least three. -/
theorem cubic_field_actor_rank_three (hF : 2 < Nat.card F) (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (hσA : fieldAction σ ∈ A)
    : 3 ≤ primeRank 3 A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary_cubic σ
  let := hE
  let f : Model F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hF)) (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAction σ,hσA⟩
  have hx : orderOf x = 3 := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAction fieldAction_injective σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAction σ ∈ MulAut.innerSubgroup (Model F) :=
      ⟨g,congrArg Subtype.val he⟩
    obtain ⟨u,hu⟩ := hi
    have hs := fieldAction_eq_conj_implies_one σ u hu.symm
    rw [hs,orderOf_one] at hσ
    exact Nat.prime_three.ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAction σ y * g⁻¹ = fieldAction σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = 3^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- With three-rank at most two, every three-power actor is inner. -/
theorem cubic_primePower_actor_inner (hF : 2 < Nat.card F)
    (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A) (hrank : primeRank 3 A ≤ 2)
    (a : MulAut (Model F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (3^m) = 1) :
    a ∈ MulAut.innerSubgroup (Model F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he⟩ := exists_inner_field hF a
  have hσ : σ ^ (3^m) = 1 := by
    have hh := congrArg (fieldComponent hF) ham
    rw [map_pow,he,fieldComponent_inner_field,map_one] at hh
    exact hh
  have hσA : fieldAction σ ∈ A := by
    have hh := A.mul_mem (A.inv_mem (hinner ⟨g,rfl⟩)) haA
    rwa [he,inv_mul_cancel_left] at hh
  have hσone : σ = 1 := by
    by_contra hn
    have hp : IsPGroup 3 (zpowers σ) := IsPGroup.of_card_dvd_pow (n := m)
      (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hσ)
    have hdP : 3 ∣ Nat.card (zpowers σ) := hp.card_eq_or_dvd.resolve_left (by
      intro hc
      have hb := (card_eq_one.mp hc : zpowers σ = ⊥)
      exact hn (mem_bot.mp (hb ▸ mem_zpowers σ)))
    obtain ⟨τ,hτ⟩ := exists_prime_orderOf_dvd_card' 3 hdP
    have hτA : fieldAction (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAction (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = 3 :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := cubic_field_actor_rank_three hF A hinner τ hτp hτA
    omega
  rw [he,hσone]
  have hh : fieldAction (1 : F ≃+* F) = 1 := fieldAction.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩

/-- The cubic prime-power elements of an original action have inner image.
This keeps the literal action map used by the source A.3.18 application. -/
theorem cubic_primePower_action_inner (hF : 2 < Nat.card F)
    {D : Type*} [Group D] (ρ : D →* MulAut (Model F))
    (hinner : MulAut.innerSubgroup (Model F) ≤ ρ.range)
    (hrank : primeRank 3 ρ.range ≤ 2) (d : D) (hd : ∃ m : ℕ, d ^ (3^m) = 1) :
    ρ d ∈ MulAut.innerSubgroup (Model F) := by
  apply cubic_primePower_actor_inner hF ρ.range hinner hrank (ρ d) ⟨d,rfl⟩
  obtain ⟨m,hm⟩ := hd
  exact ⟨m,by rw [←map_pow,hm,map_one]⟩

end Atlas.G2.CubicFieldActors
