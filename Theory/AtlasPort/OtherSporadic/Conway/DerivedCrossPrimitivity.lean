/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/DerivedCrossPrimitivity.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.DerivedCrossTransitivity

/-!
Primitivity of the cross actions of the Leech isometry group and its central quotient.
The proof identifies the cross stabilizers and uses maximality of the monomial subgroup.

Source: Gerald Höhn, `Atlas/Conway/DerivedCrossPrimitivity.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to Lean 4.33.0 with public imports and exposed concrete definitions
for the source cross-module reductions; the mathematical namespaces are preserved.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

theorem quotient_cross_stabilizer :
    MulAction.stabilizer LeechCentralQuotient standardCross = quotientMonomialSubgroup := by
  ext g
  obtain ⟨h,rfl⟩ := leechCentralProjection_surjective g
  constructor
  · intro hg
    have hh : h ∈ monomialSubgroup := by
      rw [← full_cross_stabilizer]
      exact hg
    obtain ⟨m,hm⟩ := hh
    exact ⟨m,congrArg leechCentralProjection hm⟩
  · rintro ⟨m,hm⟩
    rw [← hm]
    exact monomial_fixes_standardCross m

theorem full_cross_primitive : MulAction.IsPreprimitive LeechIsometryGroup LeechCross := by
  let := full_cross_transitive
  let : Nontrivial LeechCross := (Fintype.one_lt_card_iff_nontrivial).mp (by
    rw [← Nat.card_eq_fintype_card,leechCross_card]; norm_num)
  apply (MulAction.isCoatom_stabilizer_iff_preprimitive _ standardCross).mp
  rw [full_cross_stabilizer]
  exact monomial_maximal

theorem quotient_cross_primitive : MulAction.IsPreprimitive LeechCentralQuotient LeechCross := by
  let := full_cross_primitive
  let f : LeechCross →ₑ[leechCentralProjection] LeechCross :=
    ⟨id,fun _ _ => rfl⟩
  exact MulAction.IsPreprimitive.of_surjective (f := f) Function.surjective_id

theorem monomial_not_normal : ¬ monomialSubgroup.Normal := by
  intro hN
  let := hN
  let := full_cross_transitive
  have hle : monomialSubgroup ≤ leechCentralSigns := by
    intro n hn
    rw [← crossRepresentation_kernel]
    change crossRepresentation n = 1
    apply Equiv.ext
    intro x
    obtain ⟨g,hg⟩ := MulAction.exists_smul_eq LeechIsometryGroup standardCross x
    have hc : g⁻¹*n*g ∈ monomialSubgroup := by
      simpa only [inv_inv] using hN.conj_mem n hn g⁻¹
    rw [← full_cross_stabilizer] at hc
    have he := congrArg (fun y : LeechCross => g • y) hc
    change g • ((g⁻¹*n*g) • standardCross) = g • standardCross at he
    change n • x = x
    simpa only [mul_smul,smul_inv_smul,hg] using he
  have hc := Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  rw [monomial_order,leechCentralSigns_card] at hc
  omega

end Atlas.Conway
