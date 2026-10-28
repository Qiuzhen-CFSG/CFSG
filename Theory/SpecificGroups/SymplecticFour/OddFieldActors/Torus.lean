module
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.FieldFixedResidual.Descent
public import Theory.FieldTheory.PrimeOrderFixedUnits
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The actual rank-two torus fixed by an odd field actor

The diagonal section of the symplectic Borel embeds two independent cyclic
groups of order p. For a field automorphism of order p, fixed-point counting
retains p in the fixed coefficient unit group. Coefficient descent therefore
embeds the same elementary group of order p² in the actual fixed subgroup.

Source: Aschbacher–Smith A.3.18, printed pp.51–53, symplectic field case.
-/

public section
noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.OddFieldActors
open DiagramAutomorphisms
variable {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]

theorem exists_elementary_torus (hd : p ∣ Nat.card F - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 := by
  obtain ⟨a,ha⟩ := exists_prime_orderOf_dvd_card' p (by simpa only [Nat.card_units] using hd : p ∣ Nat.card Fˣ)
  let P := zpowers a
  let : IsElementaryAbelian p P := IsElementaryAbelian.zpowers_of_pow_eq_one
    (ha ▸ pow_orderOf_eq_one a)
  let : IsElementaryAbelian p (P × P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      apply Prod.ext
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.1
      · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p P) x.2) }
  let c : Fˣ × Fˣ →* Sp F := borel.subtype.comp EvenBorelTorus.torusSection
  have hc : Function.Injective c := by
    intro x y he
    have hh : EvenBorelTorus.torusSection x = EvenBorelTorus.torusSection y := Subtype.ext he
    simpa only [EvenBorelTorus.characters_torusSection] using congrArg borelCharacters hh
  let f : P × P →* Sp F := c.comp (P.subtype.prodMap P.subtype)
  have hf : Function.Injective f := by
    intro x y he
    have hh := hc he
    exact Prod.ext (Subtype.ext (congrArg Prod.fst hh)) (Subtype.ext (congrArg Prod.snd hh))
  let : IsElementaryAbelian p f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  refine ⟨f.range,inferInstance,?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,Nat.card_prod,Nat.card_zpowers,ha,pow_two]

theorem split_prime_rank (hd : p ∣ Nat.card F - 1) : 2 ≤ primeRank p (Sp F) := by
  obtain ⟨E,hE,hcard⟩ := exists_elementary_torus hd
  let := hE
  exact IsElementaryAbelian.primeRank_ge_of_card E hcard

theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hd : p ∣ Nat.card F - 1) :
    ∃ E : Subgroup (Sp F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAutomorphism σ).fixedSubgroup := by
  have hK := FiniteField.prime_dvd_fixed_units σ hσ hd
  rw [Nat.card_units] at hK
  have hfixed : FieldFixedResidual.fixedField σ = FixedBy.subfield F σ := by
    ext x
    exact FieldFixedResidual.mem_fixedField σ x
  rw [← hfixed] at hK
  obtain ⟨B,hB,hcard⟩ := exists_elementary_torus hK
  let := hB
  let f : Sp (FieldFixedResidual.fixedField σ) →* Sp F :=
    (fieldAutomorphism σ).fixedSubgroup.subtype.comp (FieldFixedResidual.fixedEquiv σ).symm.toMonoidHom
  have hf : Function.Injective f :=
    (fieldAutomorphism σ).fixedSubgroup.subtype_injective.comp (FieldFixedResidual.fixedEquiv σ).symm.injective
  refine ⟨B.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hcard]
  · rintro _ ⟨b,_,rfl⟩
    exact ((FieldFixedResidual.fixedEquiv σ).symm b).property

end Theory.SpecificGroups.SymplecticFour.OddFieldActors
