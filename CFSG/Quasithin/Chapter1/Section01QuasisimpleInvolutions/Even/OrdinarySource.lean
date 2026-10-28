module

public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Even.AvailableCovers
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.PrimeCover
public import CFSG.Quasithin.Chapter1.Section01QuasisimpleInvolutions.Odd.DegreeThreeCenters
public import Theory.SpecificGroups.PSL3.BinaryComparison
public import Theory.SpecificGroups.SU3.BinaryG2Comparison

/-!
# Ordinary degree-three and small derived source branches

For ordinary binary PSL3 the universal SL3 projection forces the original
center order to divide three. The marked inner involution makes that center
a two-group, so it is trivial. PSL3(4) retains the allowed two-cover case;
PSL3(2) uses its genuine PSL2(7) comparison and the prime-cover exclusion.
The actual G2(2) derived group is compared with PSU3(3), whose complete
universal-kernel bound removes its center. No extra cover premise remains.

Source: Aschbacher--Smith 1.1.5(3), printed pp.501--503, and I.1.3(2).
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
namespace CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
open Chapter15.Section03.Candidates.ComponentStructure ClassificationModels
variable {L : Type*} [Group L] [Finite L] [IsQuasisimple L]
  {α : MulAut L} {P : Sylow 2 L}

/-- Ordinary even PSL3 has no compatible nontrivial marked central cover. -/
theorem MarkedInvolution.linearThree_source (d : MarkedInvolution α P) {f : ℕ}
    (hf : 1 ≤ f) (h : ClassicalGroup.IsPSL (L ⧸ center L) 3 (2 ^ f)) :
    ModelAction115 L α := by
  by_cases hsmall : f = 1
  · subst f
    have hi := d.linearThree_inner hf h
    apply d.lie_of_center_eq_bot (.inr (.inl (.linear 1 hf h))) hi
    obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
    let : Fact (Nat.Prime 7) := ⟨by decide⟩
    apply d.linear_two_prime_center_eq_bot (p := 7) (by decide) (by decide)
    exact ⟨ZMod 7, inferInstance, inferInstance, Nat.card_zmod 7,
      ⟨e.trans (Matrix.PSL3.binaryEquivPsl2Seven F (by simpa using hF))⟩⟩
  by_cases hfour : f = 2
  · subst f
    exact d.linearThreeFour_modelAction h
  have hi := d.linearThree_inner hf h
  apply d.lie_of_center_eq_bot (.inr (.inl (.linear f hf h))) hi
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  have h8 : 8 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : 3 ≤ f)
  let c := centralQuotientCover e
  obtain ⟨a, ha, _⟩ := Matrix.PSL3.UniversalProjection.existsUnique_projection_lift
    c.toMonoidHom c.surjective c.ker_le_center (by omega) (by omega)
  have hs : Function.Surjective a :=
    Matrix.PSL3.projection_lift_surjective F c.toMonoidHom c.ker_le_center a ha
  have hd : Nat.card (center L) ∣ Nat.card (Matrix.PSL3.projection F).ker := by
    simpa only [c, centralQuotientCover_ker] using
      kernel_card_dvd_of_surjective_factor (Matrix.PSL3.projection F)
        c.toMonoidHom a hs ha
  rw [Matrix.PSL3.card_projectionKernel] at hd
  have hd3 : Nat.card (center L) ∣ 3 := hd.trans (Nat.gcd_dvd_left _ _)
  have hz := MulAut.center_eq_twoCore_of_inner_inverts_oddCore α hi d.inverts_odd_core
  have hp : IsPGroup 2 (center L) := hz ▸ pCore_isPGroup
  rcases hp.card_eq_or_dvd with hc | hc
  · exact Subgroup.card_eq_one.mp hc
  · exact False.elim ((by decide : ¬ 2 ∣ 3) (hc.trans hd3))

/-- The literal derived binary G2 endpoint has the prescribed marked Lie action. -/
theorem MarkedInvolution.g2Derived_source (d : MarkedInvolution α P)
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) : ModelAction115 L α := by
  have hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 3 := by
    refine ⟨GaloisField 3 (2 * 1), inferInstance, inferInstance,
      ABG.unitaryForm 3 3 1 (by decide), ?_, ?_, ?_⟩
    · simpa using GaloisField.card 3 (2 * 1) (by decide)
    · intro x
      simp only [ABG.unitaryForm, iterateFrobeniusEquiv_def, pow_one]
    · exact ⟨e.trans Atlas.G2.nonempty_commutator_binary_equiv_psu3.some⟩
  exact d.lie_of_center_eq_bot (.inr (.inl (.g2_derived ⟨e⟩)))
    (d.g2Derived_inner e) (unitary_three_three_center_eq_bot hmodel)

end CFSG.Quasithin.Chapter1.QuasisimpleInvolutions
