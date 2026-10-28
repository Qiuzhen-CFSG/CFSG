module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.Transport
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.Faithfulness.PositiveSquare.Frame
/-!
# The long cubic has no nonzero fixed vector on the binary Leech module

The natural and dual triples give scalar eigenvalues t and t⁻¹, so a
nonidentity long cubic fixes no nonzero vector on C(U). The scalar
negative-square lift has precisely C(U) as its binary fixed space. If a
vector is fixed by the cubic, its displacement under this scalar lift is
fixed by both actors and hence zero. The vector itself then lies in C(U)
and is zero.

This supplies the class invariant needed for ambient cubic fusion. The
range is also identified with the cyclic subgroup of any nonidentity
long-cubic element. Neither ambient fusion nor a centralizer order is
asserted here; `CubicGeometry` consumes these facts in its local reduction.

Source: Aschbacher, *Sporadic Groups* (1994), proof of 49.5, p.283,
where X has no nonzero fixed vector on the Leech module modulo two.
-/

@[expose] public noncomputable section

open Matrix Atlas.Conway Atlas.Codes Atlas.Lattices
open scoped MatrixGroups
namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
open OctonionLocals PRegularClasses.RationalFusion.CentralizerLang.NoFixedWeight

private theorem scalar_fixed_zero {a : F} (ha : a ≠ 1) {v : F}
    (h : a * v = v) : v = 0 := by
  by_contra hv
  apply ha
  exact mul_right_cancel₀ hv (h.trans (one_mul v).symm)

/-- The cubic has no nonzero fixed vector in the literal U-fixed space. -/
theorem longCubic_fixedSpace_fixed_eq_zero (L : LongFrame) {t : Fˣ} (ht : t ≠ 1) (v : LeechModTwo)
    (hv : v ∈ fixedSpace) (hfix : quotientModTwoRepresentation (longCubic L t) v = v) :
    v = 0 := by
  obtain ⟨w, rfl⟩ := (L.coordinates_range v).mp hv
  rw [longCubic_action] at hfix
  have hw := L.coordinates_injective hfix
  have ht' : (t : F) ≠ 1 := fun h => ht (Units.ext h)
  have hi : ((t⁻¹ : Fˣ) : F) ≠ 1 := by
    intro h
    exact ht (inv_eq_one.mp (Units.ext h))
  have hinv : (torus t)⁻¹ = torus t⁻¹ := by
    apply Subtype.ext
    change (!![(t : F),0;0,((t⁻¹ : Fˣ) : F)] : Matrix (Fin 2) (Fin 2) F).adjugate = _
    simp [torus, Matrix.adjugate_fin_two]
  rw [hinv] at hw
  have hw0 : w = 0 := by
    funext i
    fin_cases i
    · exact scalar_fixed_zero ht' (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 0)
    · exact scalar_fixed_zero hi (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 1)
    · exact scalar_fixed_zero hi (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 2)
    · exact scalar_fixed_zero ht' (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 3)
    · exact scalar_fixed_zero ht' (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 4)
    · exact scalar_fixed_zero hi (by simpa [pairRepresentation, pairLinear, pairAction, torus] using congrFun hw 5)
  rw [hw0, map_zero]

/-- The same conclusion holds on the whole binary Leech module. -/
theorem longCubic_fixed_eq_zero (L : LongFrame) {t : Fˣ} (ht : t ≠ 1)
    (v : LeechModTwo) (hfix : quotientModTwoRepresentation (longCubic L t) v = v) : v = 0 := by
  obtain ⟨a, ha, haU, hspace⟩ := PositiveSquare.scalarFixedSpaceWitness_of_longFrame L
  let ρ := leechModTwoRepresentation
  have ha2 (w : LeechModTwo) : ρ a (ρ a w) = w := by
    have he : ρ a * ρ a = 1 := by
      rw [← map_mul, ← pow_two, ha, negation_modTwo_trivial]
    exact congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) he
  have hc (w : LeechModTwo) :
      quotientModTwoRepresentation (longCubic L t) (ρ a w) =
        ρ a (quotientModTwoRepresentation (longCubic L t) w) := by
    have he := congrArg quotientModTwoRepresentation
      (L.long_mem (longCubicMatrix t) _ (U_le_I haU))
    simp only [map_mul, quotientModTwoRepresentation_compatible] at he
    exact (congrArg (fun f : LeechModTwo ≃ₗ[Bit] LeechModTwo => f w) he).symm
  have hz : ρ a v + v = 0 := by
    apply longCubic_fixedSpace_fixed_eq_zero L ht
    · apply hspace
      rw [map_add, ha2, add_comm]
    · rw [map_add, hc, hfix]
  have hv : ρ a v = v := by
    have hneg : -v = v := by
      have hh : v + v = 0 := by
        have htwo : (2 : Bit) = 0 := by decide
        simpa only [two_smul, zero_smul] using congrArg (fun c : Bit => c • v) htwo
      exact (eq_neg_of_add_eq_zero_left hh).symm
    exact (eq_neg_of_add_eq_zero_left hz).trans hneg
  exact longCubic_fixedSpace_fixed_eq_zero L ht v (hspace v hv) hfix

/-- Any nonidentity scalar generates the entire long cubic. -/
theorem longCubic_range_eq_zpowers (L : LongFrame) {t : Fˣ} (ht : t ≠ 1) :
    (longCubic L).range = Subgroup.zpowers (longCubic L t) := by
  apply Eq.symm
  have hle : Subgroup.zpowers (longCubic L t) ≤ (longCubic L).range :=
    Subgroup.zpowers_le.mpr ⟨t, rfl⟩
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [longCubic_card, Nat.card_zpowers, longCubic_order L ht]

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction
