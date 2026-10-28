module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.Data
public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.Three.Descent.MonomialFaithfulness

/-!
# Descent of a marked unitary monomial map to the actual Ree group

Fixed-point membership is checked on the complete norm-one torus and the two
coordinate permutations, then extended by generation. Faithfulness on that
torus implies faithfulness on the monomial group by its matrix centralizer.
The resulting map and ambient inverter satisfy the exact public contract
`MonomialRealization`, including both action equations.

The geometric inputs remain explicit: this module does not yet prove their
existence. They require the exceptional A₂×A₂ descent of GLS3 Example 2.6.3
and the graph normalizer in Table 4.7.3A. The assembly uses neither a Ree
order formula nor a projective unitary quotient.
-/

@[expose] public noncomputable section

namespace ReeF4.CentralCovers.OddPrimary.Three.Descent

/-- The full norm-one parameter group is nontrivial, even at the excluded small endpoint. -/
theorem exists_normOne_ne_one (m : ℕ) :
    ∃ u : BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m), u ≠ 1 := by
  have hc := BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne_card
    (form m) (quadraticField_card m) (form_conj m)
  have : Nontrivial (BenderSuzuki.MatrixGroups.HermitianForm.EvenInner.normOne (form m)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [hc]
      have hp : 0 < 2 ^ (2 * m + 1) := by positivity
      omega)
  exact exists_ne 1

/-- The three types of literal generators suffice to prove fixed-point membership. -/
theorem MonomialExtension.fixed {m : ℕ} {T : TorusMap m} (E : MonomialExtension T)
    (x : MonomialGroup m) : reeTwist m (E.map x) = E.map x := by
  have he : (reeTwist m).comp E.map = E.map := by
    apply hom_ext (form m) (form_matrix m)
    · intro a
      change reeTwist m (E.map _) = E.map _
      rw [E.diagonal, T.fixed]
    · exact E.cycle_fixed
    · exact E.swap_fixed
  exact DFunLike.congr_fun he x

/-- Faithfulness on the complete norm-one torus detects the entire monomial kernel. -/
theorem MonomialExtension.injective {m : ℕ} {T : TorusMap m} (E : MonomialExtension T) :
    Function.Injective E.map := by
  obtain ⟨u, hu⟩ := exists_normOne_ne_one m
  apply injective_of_normDiagonal (form m) (form_matrix m) u hu E.map
  intro a b hab
  apply T.injective
  simpa only [MonoidHom.comp_apply, E.diagonal] using hab

/-- Assemble the literal Ree embedding and ambient inverter from the two geometric constructions. -/
def MonomialExtension.realization {m : ℕ} {T : TorusMap m} (E : MonomialExtension T) :
    MonomialRealization m where
  embedding := E.map.codRestrict (fixedSubgroup m) (fun x => (mem_fixedSubgroup m _).mpr (E.fixed x))
  injective := by
    intro a b hab
    exact E.injective (congrArg Subtype.val hab)
  inverter := ⟨E.inverter, (mem_fixedSubgroup m _).mpr E.inverter_fixed⟩
  inverts := by
    intro a
    apply Subtype.ext
    change E.inverter * E.map (Unitary.normDiagonal (form m) (form_matrix m) a) *
      E.inverter⁻¹ = E.map (Unitary.normDiagonal (form m) (form_matrix m) a⁻¹)
    simpa only [E.diagonal] using E.inverts a
  fixes_cycle := Subtype.ext E.fixes_cycle.eq

/-- Exact consumer of the marked torus and normalizer construction obligations. -/
theorem nonempty_monomialRealization_of_extension {m : ℕ} (T : TorusMap m)
    (h : Nonempty (MonomialExtension T)) : Nonempty (MonomialRealization m) := by
  obtain ⟨E⟩ := h
  exact ⟨E.realization⟩

end ReeF4.CentralCovers.OddPrimary.Three.Descent
