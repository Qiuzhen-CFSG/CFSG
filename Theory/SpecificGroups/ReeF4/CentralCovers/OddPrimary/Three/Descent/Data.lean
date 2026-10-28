module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Model

/-!
# Concrete inputs for exceptional monomial descent

The geometric construction is separated into a marked nonsplit torus and
its monomial and graph normalizer, both inside the actual root-generated
split F₄ group. The torus marking corresponds to the three diagonal entries
`a, (a*b)⁻¹, b` in the A₂ factor. It includes the scalar three-center.

These structures specify unproved construction obligations. They do not
assert existence, identify a full centralizer, or assume faithfulness of
the full monomial map. `Descent` proves that torus faithfulness and the
generator fixed-point equations suffice for the final assembly.

Sources: GLS3 Example 2.6.3 and Table 4.7.3A; the table uses the half-integer
Ree parameter whose square is our coefficient-field size.
-/

@[expose] public section

namespace ReeF4.CentralCovers.OddPrimary.Three.Descent
noncomputable section

abbrev Parameters (m : ℕ) :=
  BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m) ×
    BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m)

/-- The marked nonsplit torus, in the root-generated split F₄ carrier.
The marking must be constructed from the exceptional A₂×A₂ subsystem;
this structure has no existence instance. -/
structure TorusMap (m : ℕ) where
  map : Parameters m →* SplitGroup m
  injective : Function.Injective map
  fixed : ∀ a, reeTwist m (map a) = map a

/-- Extension of a particular constructed torus to its monomial and graph normalizer.
Only the two permutation generators need individual fixed-point calculations.
Full fixed-point membership and full faithfulness are proved in `Descent`. -/
structure MonomialExtension {m : ℕ} (T : TorusMap m) where
  map : MonomialGroup m →* SplitGroup m
  diagonal : ∀ a, map (Unitary.normDiagonal (form m) (form_matrix m) a) = T.map a
  cycle_fixed : reeTwist m (map (Unitary.cycle (form m) (form_matrix m))) =
    map (Unitary.cycle (form m) (form_matrix m))
  swap_fixed : reeTwist m (map (Unitary.swap (form m) (form_matrix m))) =
    map (Unitary.swap (form m) (form_matrix m))
  inverter : SplitGroup m
  inverter_fixed : reeTwist m inverter = inverter
  inverts : ∀ a, inverter * T.map a * inverter⁻¹ = T.map a⁻¹
  fixes_cycle : Commute inverter (map (Unitary.cycle (form m) (form_matrix m)))

end
end ReeF4.CentralCovers.OddPrimary.Three.Descent
