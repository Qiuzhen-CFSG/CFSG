module
public import Theory.GroupTheory.ComponentLocalDirectPowerSection
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalPairing
import Mathlib.Tactic

/-!
# Cubic quotients of natural-line residuals in six-letter groups

For every subgroup of S₆ containing A₆, the two-residual of a natural-line
stabilizer has order three modulo its intrinsic two-core. Conjugating the
line to the span of the duad vector v₄₅ puts its stabilizer between the
embedded A₄ and the full duad stabilizer. The checked residual calculation
then identifies its residual with that A₄. The square-one subgroup in A₄
is a normal Klein four; its order and the two-core's prime-power order
identify the full two-core.

The duad-mover argument adapts the private line transport in
`BinaryFlags.NaturalResidualAction`; all finite certificates here are
checked by the kernel. No identification with the larger S₄ intersection
is used for the residual.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, §13.2 and
Notation 13.2.1, printed pp.876–877; the ordinary case of 13.8.25,
printed p.959 (PDF p.976).
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder
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

private def klein : Subgroup K where
  carrier := {g | g ^ 2 = 1}
  one_mem' := by simp
  mul_mem' := by decide +kernel
  inv_mem' := by
    intro g hg
    change (g⁻¹) ^ 2 = 1
    rw [inv_pow, show g ^ 2 = 1 from hg, inv_one]

private instance : klein.Normal where
  conj_mem := by
    intro n hn g
    change (g * n * g⁻¹) ^ 2 = 1
    rw [conj_pow, show n ^ 2 = 1 from hn, mul_one, mul_inv_cancel]

private instance (g : K) : Decidable (g ∈ klein) :=
  inferInstanceAs (Decidable (g ^ 2 = 1))

private theorem card_klein : Nat.card klein = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- The embedded A₄ residual has cubic two-core quotient. -/
theorem quotient_K_card : Nat.card (K ⧸ pCore 2 K) = 3 := by
  have hle : klein ≤ pCore 2 K :=
    le_sSup ⟨inferInstance, IsPGroup.of_card (n := 2) card_klein⟩
  have hlo : 4 ≤ Nat.card (pCore 2 K) := by
    rw [← card_klein]
    exact Nat.card_le_card_of_injective _ (inclusion_injective hle)
  have hd : Nat.card (pCore 2 K) ∣ 4 * 3 := by
    simpa only [card_K] using (pCore 2 K).card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card (pCore 2 K)) 3 := by
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := K)).exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 2 3).pow_left n
  have hhi := Nat.le_of_dvd (by decide : 0 < 4) (hcop.dvd_mul_right.mp hd)
  have he : Nat.card (pCore 2 K) = 4 := le_antisymm hhi hlo
  have hc := (pCore 2 K).card_mul_index
  change Nat.card (pCore 2 K) * Nat.card (K ⧸ pCore 2 K) = Nat.card K at hc
  rw [he, card_K] at hc
  omega


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

/-- For any permutation group containing A₆, the residual of a natural-line
stabilizer has quotient of order three by its own two-core. -/
theorem point_residual_quotient_card (I : Subgroup S)
    (hI : alternatingGroup Ω ≤ I) (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    let M := I ⊓ subspaceStabilizer (naturalRepresentation Ω) P
    let R := (pResidual 2 M).map M.subtype
    Nat.card (R ⧸ pCore 2 R) = 3 := by
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
  exact (Nat.card_congr
    (Theory.GroupTheory.ComponentLocalCoreSection.quotientCoreEquiv 2 e.toMonoidHom
      e.surjective (IsPGroup.ker_isPGroup_of_injective e.injective)).toEquiv).trans
        quotient_K_card

end Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalCubicOrder
