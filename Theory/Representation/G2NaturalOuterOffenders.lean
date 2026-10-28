module

public import Theory.SpecificGroups.G2Even.TwoRank.OuterBound
public import Theory.Representation.G2NaturalSemilinear
public import Theory.Representation.FiniteFieldSemilinearDisplacement
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# Field automorphisms cannot be natural G₂ offenders

An outer elementary subgroup has rank strictly below 3n, whereas a field
involution in it moves exactly 3n dimensions by finite-field semilinear
descent. The contradiction proves containment in the literal inner factor
for every offender of the actual natural semidirect-product representation.

Source: Aschbacher–Smith B.4.6(9), (13), printed pp.89–90.
-/

public section
open Representation Representation.BinaryOffender
namespace Atlas.G2.Natural.BinarySemilinear
variable (F : Type*) [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]
/-- A nontrivial field involution moves exactly half the natural binary module. -/
theorem outer_fixedCodim {n : ℕ} (hF : Nat.card F = 2 ^ n) (z : Actor F)
    (hz : z ^ 2 = 1) (hs : z.right ≠ 1) :
    fixedCodim (representation F) (Subgroup.zpowers z) = 3 * n := by
  have hz1 : z ≠ 1 := fun he => hs (congrArg SemidirectProduct.right he)
  have hs2 : z.right ^ 2 = 1 := congrArg SemidirectProduct.right hz
  have hsemi (a : F) (v : Coordinates F) :
      coordinateRepresentation F z (a • v) = z.right a • coordinateRepresentation F z v := by
    rw [coordinateRepresentation_apply, coordinateRepresentation_apply]
    have he : (fun i => z.right ((a • v) i)) = z.right a • (fun i => z.right (v i)) := by
      ext i
      exact map_mul z.right a (v i)
    rw [he, map_smul]
  have hh := FiniteFieldSemilinearDisplacement.fixedCodim_formula (coordinateRepresentation F)
    (by decide : 0 < 2) z (orderOf_eq_prime hz hz1)
    z.right (orderOf_eq_prime hs2 hs) hsemi
  have hd : Module.finrank (ZMod 2) F = n := by
    apply Nat.pow_right_injective (by decide : 1 < 2)
    exact (FiniteField.pow_finrank_eq_natCard 2 F).trans hF
  rw [hd, Module.finrank_pi, Fintype.card_fin] at hh
  have hc := fixedCodim_map_equivariant (representation F) (coordinateRepresentation F)
    (MonoidHom.id _) (coordinatesEquiv F) (coordinates_representation F) (Subgroup.zpowers z)
  simp only [Subgroup.map_id] at hc
  rw [← hc] at hh
  omega
/-- Every offender of the actual semilinear natural representation has
trivial field projection. -/
theorem offender_le_inner {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {E : Subgroup (Actor F)} (hE : IsOffender (representation F) E) :
    E ≤ (SemidirectProduct.rightHom : Actor F →* (F ≃+* F)).ker := by
  let := hE.1.2
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun e : F ≃+* F => (e : F → F)) (fun _ _ h => RingEquiv.ext (congrFun h))
  let : Finite (Actor F) := Finite.of_equiv
    (Model F × (F ≃+* F)) SemidirectProduct.equivProd.symm
  intro z hz
  change z.right = 1
  by_contra hs
  have hcard := EvenTwoRank.outer_elementary_card_lt F hn hF E hE.1.2 ⟨z,hz⟩ hs
  rw [hE.1.card_eq_two_pow_rank] at hcard
  have hr : rank E < 3*n := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hcard
  have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz
  have hc := outer_fixedCodim F hF z hz2 hs
  have hle : fixedSpace (representation F) E ≤ fixedSpace (representation F) (Subgroup.zpowers z) := by
    intro v hv a
    exact hv ⟨a, Subgroup.zpowers_le.mpr hz a.property⟩
  have hd := Submodule.finrank_mono hle
  have h1 := fixedCodim_add_finrank (representation F) E
  have h2 := fixedCodim_add_finrank (representation F) (Subgroup.zpowers z)
  have ho := hE.2
  omega
end Atlas.G2.Natural.BinarySemilinear
