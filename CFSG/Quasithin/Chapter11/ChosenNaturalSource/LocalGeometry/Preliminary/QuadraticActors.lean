module
public import Theory.SpecificGroups.SymplecticFour.OddFieldActors.Cubic
public import Theory.SpecificGroups.G2.CubicFieldActors
public import Theory.SpecificGroups.G2.MultiplierOrdinary.Nondefining.QuadraticTorus.ShortBlock
public import Theory.FieldTheory.PrimeOrderFixedUnits
public import GorensteinWalter.PSL2Cardinality

/-!
# Odd field actors for every prime dividing q² − 1

The commuting SL₂ factors in Sp₄ and G₂ embed an elementary group of order
p² whenever p divides q² − 1. Fixed-point counting for a field automorphism
of order p retains this divisibility over its literal fixed coefficient
field. Coefficient descent therefore supplies a fixed elementary p².
A nontrivial field actor would enlarge it to rank three in the inner action.
The rank-two bound excludes it, and the actual automorphism decompositions
then make every p-power actor inner.

This extends the split-prime and cubic arguments in the imported
OddFieldActors and CubicFieldActors modules. The G₂ pair embedding and
coefficient automorphisms use the attributed ATLAS model; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.

Source: Aschbacher--Smith A.3.18, printed pp.51--53. The actual chosen
normalizer consumer is Preliminary.Residual, for 11.0.4, printed p.760.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.QuadraticActors
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem fixed_square_dvd (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    p ∣ Nat.card (FixedPoints.subfield (zpowers σ) F) ^ 2 - 1 := by
  have hP : IsPGroup p (zpowers σ) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hσ, pow_one])
  have hc := hP.card_modEq_card_fixedPoints F
  change Nat.card F ≡ Nat.card (FixedPoints.subfield (zpowers σ) F) [MOD p] at hc
  have hh := Nat.ModEq.sub_right (a := 1)
    (pow_pos (Nat.card_pos (α := F)) 2)
    (pow_pos (Nat.card_pos (α := FixedPoints.subfield (zpowers σ) F)) 2)
    (hc.pow 2)
  exact Nat.modEq_zero_iff_dvd.mp (hh.symm.trans hd.modEq_zero_nat)

omit [Finite F] in
theorem fixedBy_eq (σ : F ≃+* F) :
    FixedPoints.subfield (zpowers σ) F = FixedBy.subfield F σ := by
  ext x
  change (∀ g : zpowers σ, g • x = x) ↔ σ x = x
  constructor
  · intro hx
    exact hx ⟨σ, mem_zpowers σ⟩
  · intro hx g
    exact smul_eq_self_of_mem_zpowers g.property hx

theorem exists_elementary_pair {A : Type*} [Group A]
    (f : SL(2,F) × SL(2,F) →* A) (hf : Function.Injective f)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup A, IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (by
    rw [GorensteinWalter.sl2_card_formula]
    exact dvd_mul_of_dvd_right hd _ : p ∣ Nat.card (SL(2,F)))
  let P := zpowers a
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let g : P × P →* A := f.comp (P.subtype.prodMap P.subtype)
  have hg : Function.Injective g := by
    intro x y he
    have hh := hf he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p g.range :=
    IsElementaryAbelian.of_surjective g.rangeRestrict g.rangeRestrict_surjective
  refine ⟨g.range, inferInstance, ?_⟩
  rw [←Nat.card_congr (MonoidHom.ofInjective hg).toEquiv,
    Nat.card_prod, Nat.card_zpowers, ha, pow_two]

variable [CharP F 2]
namespace Sp4
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms OddFieldActors

omit [CharP F 2] in
theorem exists_elementary (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 :=
  exists_elementary_pair
    CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom
    CentralCovers.OddPrime.LargeSections.OddNondefining.ProductTori.pairHom_injective hd

omit [CharP F 2] in
theorem rank_two (hd : p ∣ Nat.card F ^ 2 - 1) : 2 ≤ primeRank p (Sp F) := by
  obtain ⟨E,hE,hcard⟩ := exists_elementary hd
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

omit [CharP F 2] in
theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAutomorphism σ).fixedSubgroup := by
  have hK := fixed_square_dvd σ hσ hd
  rw [fixedBy_eq σ] at hK
  have heq : FieldFixedResidual.fixedField σ = FixedBy.subfield F σ := by
    ext x
    exact FieldFixedResidual.mem_fixedField σ x
  rw [← heq] at hK
  obtain ⟨B,hB,hcard⟩ := exists_elementary hK
  let := hB
  let f : Sp (FieldFixedResidual.fixedField σ) →* Sp F :=
    (fieldAutomorphism σ).fixedSubgroup.subtype.comp (FieldFixedResidual.fixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAutomorphism σ).fixedSubgroup.subtype_injective.comp (FieldFixedResidual.fixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((FieldFixedResidual.fixedEquiv σ).symm b).property

theorem field_actor_rank_three (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAutomorphism σ ∈ A)
    (hd : p ∣ Nat.card F ^ 2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hd
  let := hE
  let f : Sp F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact InvolutionNormalForms.inner_injective (congrArg Subtype.val hh)
  let B := E.map f
  let : IsElementaryAbelian p B := IsElementaryAbelian.map f
  let x : A := ⟨fieldAutomorphism σ,hσA⟩
  have hfield : Function.Injective (fieldAutomorphismHom (F := F)) := by
    intro a b hh
    apply InvolutionNormalForms.outerFieldHom_injective
    exact congrArg (QuotientGroup.mk' (MulAut.innerSubgroup (Sp F))) hh
  have hx : orderOf x = p := by
    rw [← orderOf_injective A.subtype A.subtype_injective]
    exact (orderOf_injective fieldAutomorphismHom hfield σ).trans hσ
  have hxB : x ∉ B := by
    rintro ⟨g,_,he⟩
    have hi : fieldAutomorphism σ ∈ MulAut.innerSubgroup (Sp F) :=
      ⟨g,congrArg Subtype.val he⟩
    have hs := InvolutionNormalForms.field_eq_one_of_inner σ hi
    rw [hs,orderOf_one] at hσ
    exact (Fact.out : p.Prime).ne_one hσ.symm
  have hBfix : B ≤ centralizer ({x} : Set A) := by
    rintro _ ⟨g,hg,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    apply MulEquiv.ext
    intro y
    have hgfix := (MulAut.mem_fixedSubgroup _ _).mp (hfix hg)
    change g * fieldAutomorphism σ y * g⁻¹ = fieldAutomorphism σ (g * y * g⁻¹)
    rw [map_mul,map_mul,map_inv,hgfix]
  have hcB : Nat.card B = p^2 := by rw [card_map_of_injective hf,hcard]
  exact IsElementaryAbelian.primeRank_ge_of_fixed_join B x hx hxB hBfix hcB

theorem primePower_actor_inner (hF : 2 < Nat.card F) (ho : Odd p)
    (hd : p ∣ Nat.card F ^ 2 - 1) (A : Subgroup (MulAut (Sp F)))
    (hinner : MulAut.innerSubgroup (Sp F) ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut (Sp F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup (Sp F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
  obtain ⟨m,ham⟩ := ha
  obtain ⟨g,σ,he,hσ⟩ := inner_field_of_primePower hF ho a ham
  have hσA : fieldAutomorphism σ ∈ A := by
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
    have hτA : fieldAutomorphism (τ : F ≃+* F) ∈ A := by
      obtain ⟨k,hk⟩ := τ.property
      rw [← hk]
      change fieldAutomorphismHom (σ ^ k) ∈ A
      rw [map_zpow]
      exact A.zpow_mem hσA k
    have hτp : orderOf (τ : F ≃+* F) = p :=
      (orderOf_injective (zpowers σ).subtype (zpowers σ).subtype_injective τ).trans hτ
    have hh := field_actor_rank_three A hinner τ hτp hτA hd
    omega
  rw [he,hσone]
  have hh : fieldAutomorphism (1 : F ≃+* F) = 1 := fieldAutomorphismHom.map_one
  rw [hh,mul_one]
  exact ⟨g,rfl⟩


end Sp4

namespace G2
open Atlas.G2 Atlas.G2.LieAutomorphismExtensions

theorem exists_elementary (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p^2 :=
  exists_elementary_pair MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom
    MultiplierOrdinary.Nondefining.QuadraticTorus.pairHom_injective hd

theorem rank_two (hd : p ∣ Nat.card F ^ 2 - 1) : 2 ≤ primeRank p (Model F) := by
  obtain ⟨E,hE,hcard⟩ := exists_elementary hd
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F ^ 2 - 1) :
    ∃ E : Subgroup (Model F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAction σ).fixedSubgroup := by
  have hK := fixed_square_dvd σ hσ hd
  obtain ⟨B,hB,hcard⟩ := exists_elementary (F := EvenFieldFixedResidual.fixedField σ) hK
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

theorem field_actor_rank_three (hF : 2 < Nat.card F) (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A)
    (σ : F ≃+* F) (hσ : orderOf σ = p) (hσA : fieldAction σ ∈ A)
    (hd : p ∣ Nat.card F ^ 2 - 1) : 3 ≤ primeRank p A := by
  obtain ⟨E,hE,hcard,hfix⟩ := exists_fixed_elementary σ hσ hd
  let := hE
  let f : Model F →* A := MulAut.conj.codRestrict A (fun g => hinner ⟨g,rfl⟩)
  have hf : Function.Injective f := by
    intro x y hh
    exact (Theory.GroupTheory.conj_injective_of_center_eq_bot (model_center_eq_bot hF)) (congrArg Subtype.val hh)
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

/-- The rank bound excludes every nontrivial prime-power field actor. -/
theorem primePower_actor_inner (hF : 2 < Nat.card F)
    (hd : p ∣ Nat.card F ^ 2 - 1)
    (A : Subgroup (MulAut (Model F)))
    (hinner : MulAut.innerSubgroup (Model F) ≤ A) (hrank : primeRank p A ≤ 2)
    (a : MulAut (Model F)) (haA : a ∈ A) (ha : ∃ m : ℕ, a ^ (p^m) = 1) :
    a ∈ MulAut.innerSubgroup (Model F) := by
  let : Finite (F ≃+* F) := Finite.of_injective (fun σ : F ≃+* F => (σ : F → F))
    DFunLike.coe_injective
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


end G2
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.QuadraticActors
