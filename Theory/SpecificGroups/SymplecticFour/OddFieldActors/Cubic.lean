module
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Exclusion
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori
public import Theory.SpecificGroups.PSL2.PairedOuterThree.Cubic

/-!
# Cubic symplectic field actors without a split-torus hypothesis

The constant matrix `[[0,1],[1,1]]` has order three in characteristic two.
The two orthogonal SL₂ embeddings therefore give an elementary subgroup
of order nine, even over F₂. Applying the same construction over the
literal fixed coefficient field gives an elementary nine fixed by every
field automorphism, independently of divisibility of the field order minus one.

Its faithful inner image and an outer cubic field actor generate an
elementary subgroup of order 27. Thus a subgroup of automorphisms with
three-rank at most two and containing all inner automorphisms has no
nontrivial cubic field actor. The existing odd prime-power inner–field
reduction then makes every three-power actor inner. The final theorem
retains an original action homomorphism for the source application.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, applied in 14.2.15,
printed pp.985–986. The source's containing-overgroup placement is separate.
-/

public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.OddFieldActors
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- The two orthogonal prime-field cubic subgroups give elementary order nine,
including over F₂. -/
theorem exists_elementary_cubic :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 := by
  let c := Theory.PSL2.PairedOuterThree.primeCubic F
  have hc : orderOf c = 3 := Theory.PSL2.PairedOuterThree.primeCubic_order F
  let P := zpowers c
  let : IsElementaryAbelian 3 P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (hc ▸ pow_orderOf_eq_one c)
  let : IsElementaryAbelian 3 (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 3 P) x.2) }
  let f : P × P →* Sp F :=
    CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom.comp
      (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom_injective he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian 3 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,inferInstance,?_⟩
  rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    Nat.card_prod,Nat.card_zpowers,hc,pow_two]

/-- Sp₄ over every finite characteristic-two field has cubic rank at least two. -/
theorem cubic_rank : 2 ≤ primeRank 3 (Sp F) := by
  obtain ⟨E,hE,hcard⟩ := exists_elementary_cubic (F := F)
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

omit [Finite F] in
/-- Every coefficient automorphism fixes an elementary subgroup of order nine.
Descent uses the prime-field cubics over its literal fixed coefficient field. -/
theorem exists_fixed_elementary_cubic (σ : F ≃+* F) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian 3 E ∧ Nat.card E = 3^2 ∧
      E ≤ (fieldAutomorphism σ).fixedSubgroup := by
  obtain ⟨B,hB,hcard⟩ := exists_elementary_cubic (F := FieldFixedResidual.fixedField σ)
  let := hB
  let f : Sp (FieldFixedResidual.fixedField σ) →* Sp F :=
    (fieldAutomorphism σ).fixedSubgroup.subtype.comp (FieldFixedResidual.fixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAutomorphism σ).fixedSubgroup.subtype_injective.comp (FieldFixedResidual.fixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((FieldFixedResidual.fixedEquiv σ).symm b).property

/-- A cubic coefficient actor enlarges the fixed inner elementary nine to
three-rank at least three. -/
theorem cubic_field_actor_rank_three (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = 3) (hσA : fieldAutomorphism σ ∈ A)
    : 3 ≤ primeRank 3 A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary_cubic σ
  let := hE
  let f : Sp F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact InvolutionNormalForms.inner_injective (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian 3 B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAutomorphism σ,hσA⟩
  have hfield : Function.Injective (fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hx : orderOf x = 3 := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAutomorphismHom hfield σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) :=
      ⟨g,congrArg Subtype.val he⟩
    have hs := InvolutionNormalForms.field_eq_one_of_inner σ hi
    rw [hs,orderOf_one] at hσ
    exact Nat.prime_three.ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAutomorphism σ y * g⁻¹ = fieldAutomorphism σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = 3^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

/-- With three-rank at most two, every three-power actor is inner, including
when three divides the field order plus one. -/
theorem cubic_primePower_actor_inner (hF : 2 < Nat.card F)
    (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A) (hrank : primeRank 3 A ≤ 2)
    (a : MulAut (Sp F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (3^m) = 1) :
    a ∈ MulAut.innerSubgroup (Sp F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := inner_field_of_primePower hF (by decide : Odd 3) a ham
  have hσA : fieldAutomorphism σ ∈ A := by
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
    have hτA : fieldAutomorphism (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAutomorphismHom (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = 3 :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := cubic_field_actor_rank_three A hinner τ hτp hτA
    omega
  rw [he,hσone]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := fieldAutomorphismHom.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩

/-- The cubic prime-power elements of an original action have inner image.
This keeps the literal action map used by the source A.3.18 application. -/
theorem cubic_primePower_action_inner (hF : 2 < Nat.card F)
    {D : Type*} [Group D] (ρ : D →* MulAut (Sp F))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ ρ.range)
    (hrank : primeRank 3 ρ.range ≤ 2) (d : D) (hd : ∃ m : ℕ, d ^ (3^m) = 1) :
    ρ d ∈ MulAut.innerSubgroup (Sp F) := by
  apply cubic_primePower_actor_inner hF ρ.range hinner hrank (ρ d) ⟨d,rfl⟩
  obtain ⟨m,hm⟩ := hd
  exact ⟨m,by rw [←map_pow,hm,map_one]⟩

end Theory.SpecificGroups.SymplecticFour.OddFieldActors
