module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.Coordinates
public import Theory.Frattini.PGroup

/-!
# Specialness from the explicit arms commutator and square formulas

The radical of the trace pairing identifies the center, and the two singleton
root groups attain every central commutator. The finite p-group Frattini formula
then identifies the Frattini subgroup using the squares. All results below
retain the actual Geck commutator and square formulas as explicit premises.
They are reductions for the source theorem, not completed source assertions;
the assembly owner must prove those formulas and supply them.

Source: GLS3 2.4.5 and §2.6 (`refs/KGroup/GLS3/chapter2.tex`);
Aschbacher–Smith F.1.11–12 (`refs/quasithin.pdf`, printed pp.262–264).
-/

@[expose] public section

noncomputable section
open scoped commutatorElement
namespace Triality.Standard.RadicalCoordinates.Centers

variable (P : Parameters) (hp : P.prime = 2)

theorem centralParameters_mem_center (z : fixedField P) :
    armsEquiv P hp (centralParameters P z) ∈ Subgroup.center (armsSubgroup P) := by
  have hz : (armsEquiv P hp (centralParameters P z)).val ∈ highestRoot P := by
    rw [armsEquiv_centralParameters, ← highestHom_range P hp]
    exact ⟨Multiplicative.ofAdd z, rfl⟩
  obtain ⟨x, hx, he⟩ := highestRoot_le_center_arms P hp hz
  exact (Subtype.ext he : x = armsEquiv P hp (centralParameters P z)) ▸ hx

variable (hcomm : ∀ v w : ArmsParameters P,
  ⁅armsEquiv P hp v, armsEquiv P hp w⁆ =
    armsEquiv P hp (centralParameters P (armsCommutator P v w)))

include hp hcomm

/-- Reduction from the explicit Geck commutator formula. The formula is an
undischarged premise here, not an assertion about the source group. -/
theorem mem_center_arms_iff_of_commutator (x : armsSubgroup P) :
    x ∈ Subgroup.center (armsSubgroup P) ↔
      ∃ z : fixedField P, armsEquiv P hp (centralParameters P z) = x := by
  constructor
  · intro hx
    let v := (armsEquiv P hp).symm x
    have hv : armsEquiv P hp v = x := (armsEquiv P hp).apply_symm_apply x
    have hc : ∀ w, armsCommutator P v w = 0 := by
      intro w
      apply (armsEquiv_central_eq_one_iff P hp _).mp
      rw [← hcomm, hv]
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      exact (Subgroup.mem_center_iff.mp hx _).symm
    have he := armsCommutator_radical P hp v hc
    exact ⟨v.2 2, (congrArg (armsEquiv P hp) he).symm.trans hv⟩
  · rintro ⟨z, rfl⟩
    exact centralParameters_mem_center P hp z

theorem embedded_center_arms_of_commutator :
    (Subgroup.center (armsSubgroup P)).map (armsSubgroup P).subtype = highestRoot P := by
  apply le_antisymm
  · rintro g ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := (mem_center_arms_iff_of_commutator P hp hcomm x).mp hx
    rw [Subgroup.subtype_apply, armsEquiv_centralParameters, ← highestHom_range P hp]
    exact ⟨Multiplicative.ofAdd z, rfl⟩
  · exact highestRoot_le_center_arms P hp

theorem card_center_arms_of_commutator :
    Nat.card (Subgroup.center (armsSubgroup P)) = P.q := by
  rw [← Subgroup.card_map_of_injective (armsSubgroup P).subtype_injective,
    embedded_center_arms_of_commutator P hp hcomm]
  exact card_highestRoot P hp

theorem center_arms_eq_commutator_of_formula :
    Subgroup.center (armsSubgroup P) = _root_.commutator (armsSubgroup P) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨z, rfl⟩ := (mem_center_arms_iff_of_commutator P hp hcomm x).mp hx
    rw [← armsCommutator_singletons P z, ← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  · rw [_root_.commutator_def]
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    obtain ⟨v, rfl⟩ := (armsEquiv P hp).surjective x
    obtain ⟨w, rfl⟩ := (armsEquiv P hp).surjective y
    rw [hcomm]
    exact centralParameters_mem_center P hp _

/-- The general finite p-group Frattini formula completes specialness once
the actual commutator and square formulas have been supplied. -/
theorem center_arms_eq_frattini_of_formulas
    (hsquare : ∀ v : ArmsParameters P, (armsEquiv P hp v) ^ 2 =
      armsEquiv P hp (centralParameters P (armsCocycle P v v))) :
    Subgroup.center (armsSubgroup P) = frattini (armsSubgroup P) := by
  let : Fact (IsPGroup 2 (armsSubgroup P)) :=
    ⟨isPGroup_descendedRootSubgroup P hp .arms⟩
  apply le_antisymm
  · rw [center_arms_eq_commutator_of_formula P hp hcomm]
    exact commutator_le_frattini_of_isPGroup (p := 2)
  · rw [frattini_eq_closure_commutator_union_powers (p := 2)]
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with hx | ⟨y, rfl⟩
    · rwa [← center_arms_eq_commutator_of_formula P hp hcomm] at hx
    · obtain ⟨v, rfl⟩ := (armsEquiv P hp).surjective y
      change (armsEquiv P hp v) ^ 2 ∈ Subgroup.center (armsSubgroup P)
      rw [hsquare]
      exact centralParameters_mem_center P hp _

end Triality.Standard.RadicalCoordinates.Centers
