module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder

/-!
# Order of the full natural-line residual in six-letter groups

For a permutation group containing A₆, the natural-line stabilizer has
an embedded two-residual of order twelve. Conjugating the line to the duad
line identifies this residual with the embedded A₄. This retains the Klein
four lost when passing to the residual's intrinsic two-core quotient.

The finite enumeration and line transport adapt the corresponding proofs
in `NaturalCubicOrder`, whose public quotient calculation has order three.
Source: Aschbacher–Smith, Notation 13.2.1, p.877; applied to the literal
local centralizer/index assertions of 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard
open NaturalGeometry NaturalPairing BinaryPermutation Representation.BinaryOffender

private def words : List S := (permsOfList [0, 1, 2, 3]).filter (fun g => decide (g ∈ K))
private theorem mem_words (g : S) : g ∈ words ↔ g ∈ K := by
  rw [words, List.mem_filter, decide_eq_true_eq]
  refine ⟨And.right, fun hg => ⟨?_, hg⟩⟩
  apply mem_permsOfList_of_mem
  intro x hx
  fin_cases x <;> simp_all [mem_K]

private instance : Fintype K := Fintype.ofFinset words.toFinset (by
  intro g
  simp only [List.mem_toFinset]
  exact mem_words g)

private theorem card_K : Nat.card K = 12 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

private def duadMover (d : NaturalGeometry.Duad) : Equiv.Perm Ω :=
  Equiv.swap ((Equiv.swap 4 d.val.1) 5) d.val.2 * Equiv.swap 4 d.val.1

set_option maxRecDepth 4096 in
private theorem duadMover_apply : ∀ d : NaturalGeometry.Duad,
    duadMover d 4 = d.val.1 ∧ duadMover d 5 = d.val.2 := by decide

private theorem line_is_image (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    ∃ g : S, canonicalLine.map (naturalRepresentation Ω g) = P := by
  have hP0 : P ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hP
    contradiction
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff P).mp hP0
  obtain ⟨d, rfl⟩ := (vector_cases v).resolve_left hv0
  refine ⟨duadMover d, ?_⟩
  rw [canonicalLine, Submodule.map_span, Set.image_singleton, pairVector_map,
    (duadMover_apply d).1, (duadMover_apply d).2]
  exact (eq_span_singleton_of_mem_of_finrank_eq_one hP hv hv0).symm

private theorem conjugate_stabilizes (P : Submodule (ZMod 2) V) (g h : S)
    (hh : h ∈ subspaceStabilizer (naturalRepresentation Ω) P) :
    g * h * g⁻¹ ∈ subspaceStabilizer (naturalRepresentation Ω)
      (P.map (naturalRepresentation Ω g)) := by
  apply (mem_stabilizer_iff_map _ _).mpr
  have hh' := (mem_stabilizer_iff_map _ _).mp hh
  simp only [map_mul, Module.End.mul_eq_comp, Submodule.map_comp]
  rw [← Submodule.map_comp (naturalRepresentation Ω g) (naturalRepresentation Ω g⁻¹),
    ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_eq_id, Submodule.map_id, hh']

/-- The full natural-line residual has order twelve in the six-letter image. -/
theorem point_residual_card (I : Subgroup S)
    (hI : alternatingGroup Ω ≤ I) (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    let M := I ⊓ subspaceStabilizer (naturalRepresentation Ω) P
    Nat.card ((pResidual 2 M).map M.subtype) = 12 := by
  obtain ⟨g, rfl⟩ := line_is_image P hP
  dsimp only
  let M := I ⊓ subspaceStabilizer (naturalRepresentation Ω)
    (canonicalLine.map (naturalRepresentation Ω g))
  let c := (MulAut.conj g⁻¹).toMonoidHom
  have hback : (canonicalLine.map (naturalRepresentation Ω g)).map
      (naturalRepresentation Ω g⁻¹) = canonicalLine := by
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul,
      inv_mul_cancel, map_one, Module.End.one_eq_id, Submodule.map_id]
  have hlo : K ≤ M.map c := by
    intro k hk
    refine ⟨g * k * g⁻¹, ⟨hI ?_, ?_⟩, ?_⟩
    · change Equiv.Perm.sign (g * k * g⁻¹) = 1
      simp only [map_mul, map_inv, (mem_K.mp hk).2, mul_one, mul_inv_cancel]
    · exact conjugate_stabilizes _ g k
        ((mem_stabilizer_iff_map _ _).mpr (canonicalLine_map_of_mem (K_le_H1 hk)))
    · change g⁻¹ * (g * k * g⁻¹) * (g⁻¹)⁻¹ = k
      simp [mul_assoc]
  have hhi : M.map c ≤ H1 := by
    rintro _ ⟨h, hh, rfl⟩
    have hs := conjugate_stabilizes _ g⁻¹ h hh.2
    rw [hback] at hs
    exact (canonicalLine_stabilizer _).mp ((mem_stabilizer_iff_map _ _).mp hs)
  let R := (pResidual 2 M).map M.subtype
  have he : R.map c = K :=
    (map_embedded_pResidual 2 M c).trans (residual_eq_K_of_between _ hlo hhi)
  let e : R ≃* K := ((MulAut.conj g⁻¹).subgroupMap R).trans (MulEquiv.subgroupCongr he)
  exact (Nat.card_congr e.toEquiv).trans card_K

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard
