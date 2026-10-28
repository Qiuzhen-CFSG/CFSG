module

public import Theory.GroupTheory.PGroup.ExtraspecialPrimeCube
public import Theory.SpecificGroups.Janko4.Model.OddLocalRanks
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
public import Theory.SpecificGroups.Held.OddCubeCandidates.Cardinality
public import Theory.Representation.BinaryCoprimeDegree

/-!
# Concrete extraspecial subgroups for G.7

The checked ATLAS word subgroups in J₄, HS and He are nonabelian of orders
11³, 5³ and 7³. The prime-cube criterion proves their extraspeciality.
Their literal subgroup inclusions and the supplied component isomorphisms
then restrict the original faithful binary representation. The coprime
degree theorem gives lower bounds 110, 20 and 21, respectively; the last
implies the source's weaker bound 20.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), G.7.2(4),(6),
printed pp.347--348 (PDF pp.358--359). The concrete words, their ATLAS
attribution, and their kernel certificates remain in the imported modules.
This module supplies the J₄, HS and He rows; it makes no assertion about Ru.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section07.SporadicLocal
open Sporadic.LeechRelated

/-- The certified J₄ word subgroup is extraspecial of order 11³. -/
theorem j4_contains_extraspecial_eleven :
    ∃ P : Subgroup Janko4.Model, IsExtraspecial 11 P ∧ Nat.card P = 11 ^ 3 := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P := Janko4.Simplicity.Elevens.localSubgroup
    Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  have hc : Nat.card P = 11 ^ 3 := by
    simpa only [P, Nat.reducePow] using Janko4.Simplicity.Elevens.local_card
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four
  exact ⟨P, IsExtraspecial.of_noncommutative_card_prime_cube hc
    (Janko4.Simplicity.Elevens.local_not_isMulCommutative
      Janko4.matrixA_mul_self Janko4.matrixB_pow_four), hc⟩

/-- The certified HS word subgroup is extraspecial of order 5³. -/
theorem hs_contains_extraspecial_five :
    ∃ P : Subgroup HS.Carrier, IsExtraspecial 5 P ∧ Nat.card P = 5 ^ 3 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  exact ⟨HS.FiveSubgroup.subgroup,
    IsExtraspecial.of_noncommutative_card_prime_cube HS.FiveSubgroup.card_subgroup
      HS.FiveSubgroup.subgroup_not_commutative,
    HS.FiveSubgroup.card_subgroup⟩

/-- The certified Held word subgroup is extraspecial of order 7³. -/
theorem he_contains_extraspecial_seven :
    ∃ P : Subgroup Held.He, IsExtraspecial 7 P ∧ Nat.card P = 7 ^ 3 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hc : Nat.card Held.OddCubeCandidates.seven = 7 ^ 3 :=
    Held.OddCubeCandidates.card_seven
  exact ⟨Held.OddCubeCandidates.seven,
    IsExtraspecial.of_noncommutative_card_prime_cube hc
      Held.OddCubeCandidates.seven_not_commutative, hc⟩

variable {G V : Type*} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem finrank_ge_of_extraspecial_model
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {S : Type*} [Group S] [Finite S]
    (hS : ∃ P : Subgroup S, IsExtraspecial p P ∧ Nat.card P = p ^ 3)
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ≃* S) :
    p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨P, hP, hc⟩ := hS
  let := hP
  exact Representation.BinaryCoprimeDegree.extraspecial_finrank_le hp2
    ((ρ.comp L.subtype).comp (e.symm.toMonoidHom.comp P.subtype))
    (hρ.comp (Subtype.val_injective.comp (e.symm.injective.comp Subtype.val_injective))) hc

/-- G.7.2(4), applied to the actual component inclusion and model isomorphism. -/
theorem j4_finrank_ge_one_hundred_ten
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ≃* Janko4.Model) :
    110 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_eleven, Nat.reduceMul] using
    finrank_ge_of_extraspecial_model (by decide : 11 ≠ 2)
      j4_contains_extraspecial_eleven ρ hρ L e

/-- The HS row of G.7.2(6), retaining the original faithful ambient module. -/
theorem hs_finrank_ge_twenty
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ≃* HS.Carrier) :
    20 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, Nat.reduceMul] using
    finrank_ge_of_extraspecial_model (by decide : 5 ≠ 2)
      hs_contains_extraspecial_five ρ hρ L e

/-- The Held row of G.7.2(6); the local calculation gives the stronger bound 21. -/
theorem he_finrank_ge_twenty
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (L : Subgroup G) (e : L ≃* Held.He) :
    20 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h : 21 ≤ Module.finrank (ZMod 2) V := by
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_seven, Nat.reduceMul] using
      finrank_ge_of_extraspecial_model (by decide : 7 ≠ 2)
        he_contains_extraspecial_seven ρ hρ L e
  exact (by decide : 20 ≤ 21).trans h

end CFSG.Quasithin.ChapterG.Section07.SporadicLocal
