module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.AlternatingSixQuotient
public import Theory.GroupTheory.PResidual.CentralModuleFixed
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowFixedLine
/-!
# The natural-line residual of an alternating-six block

The image of a Sylow-fixed subgroup of U(L) in U(L)/C_U(L) is a line.
Its pointwise fixer lifts to the subgroup centralizing that subgroup
modulo Z(L). The central-module residual theorem removes these central
errors before taking the literal six-letter image. The resulting residual
is conjugate to the A₄ on four letters.

This argument retains the full central kernel, so it applies to both
orders of U(L) without selecting or assuming a split module cover.
Source: Aschbacher–Smith B.3 and 3.3.31, printed pp.81–85 and 602.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.AlternatingSixBlockAction
open BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Representation.BinaryOffender
variable {L : Type*} [Group L] [Finite L]
  {ρ : Actor →* MulAut (Multiplicative Vector)} (m : BlockModuleModel L ρ)
  (hρ : ∀ g v, (ρ g v).toAdd = naturalRepresentation (Fin 6) g v.toAdd)

/-- The original component quotient, embedded in its six letters. -/
@[expose] def componentPermutation : L →* S :=
  (alternatingGroup (Fin 6)).subtype.comp
    (m.quotientIso.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

/-- The point in the marked natural module represented by an actual block element. -/
@[expose] def modulePoint (u : blockU L) : Vector :=
  (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)).toAdd

omit [Finite L] in
private theorem component_range : (componentPermutation m).range = alternatingGroup (Fin 6) := by
  rw [componentPermutation, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr (m.quotientIso.surjective.comp (QuotientGroup.mk'_surjective _)),
    ← MonoidHom.range_eq_map, range_subtype]

omit [Finite L] in
include hρ in
/-- Fixation in the natural quotient is literal central displacement in the block. -/
theorem central_error_iff (l : L) (u : blockU L) :
    ⁅l, (u : L)⁆ ∈ center L ↔
      naturalRepresentation (Fin 6) (componentPermutation m l) (modulePoint m u) = modulePoint m u := by
  change blockConjugate L l u * u⁻¹ ∈ blockFixed L ↔ _
  rw [← QuotientGroup.eq_one_iff, ← m.moduleIso.map_eq_one_iff]
  change m.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l u * u⁻¹)) = 1 ↔ _
  rw [map_mul, map_inv, map_mul, map_inv, mul_inv_eq_one, m.intertwining]
  exact (Multiplicative.toAdd.injective.eq_iff).symm.trans
    (by rw [hρ]; rfl)

omit [Finite L] in
private theorem span_stabilizer_iff (v : Vector) (hv : v ≠ 0) (g : S) :
    g ∈ subspaceStabilizer (naturalRepresentation (Fin 6)) (Submodule.span (ZMod 2) {v}) ↔
      naturalRepresentation (Fin 6) g v = v := by
  rw [NaturalPairing.mem_stabilizer_iff_map]
  constructor
  · intro hg
    have hmem : naturalRepresentation (Fin 6) g v ∈ Submodule.span (ZMod 2) {v} := by
      rw [← hg]
      exact Submodule.mem_map_of_mem (Submodule.subset_span (by simp))
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hmem
    have hn : naturalRepresentation (Fin 6) g v ≠ 0 :=
      fun he => hv (((naturalRepresentation (Fin 6)).apply_bijective g).injective
        (he.trans (map_zero _).symm))
    have hc1 : c = 1 := by
      fin_cases c
      · change (0 : ZMod 2) • v = _ at hc
        rw [zero_smul] at hc
        exact (hn hc.symm).elim
      · rfl
    simpa only [hc1, one_smul] using hc.symm
  · intro hg
    simp only [Submodule.map_span, Set.image_singleton, hg]

include hρ in
/-- Residual image determined by the nonzero fixed quotient line; the full
central kernel is retained and removed by two-perfectness. -/
theorem centralizer_residual_image (_hb : IsShort L) (E : Subgroup L)
    (hEU : E ≤ blockU L) (v : Vector) (hv : v ≠ 0)
    (hvE : ∃ u : blockU L, (u : L) ∈ E ∧ modulePoint m u = v)
    (hE : ∀ u : blockU L, (u : L) ∈ E →
      modulePoint m u ∈ Submodule.span (ZMod 2) {v}) :
    ((pResidual 2 (centralizer (E : Set L))).map (centralizer (E : Set L)).subtype).map
      (componentPermutation m) =
      let P := alternatingGroup (Fin 6) ⊓
        subspaceStabilizer (naturalRepresentation (Fin 6)) (Submodule.span (ZMod 2) {v})
      (pResidual 2 P).map P.subtype := by
  let D := commutatorPreimage (⊤ : Subgroup L) E (center L)
  let P := subspaceStabilizer (naturalRepresentation (Fin 6)) (Submodule.span (ZMod 2) {v})
  have hD : D = P.comap (componentPermutation m) := by
    apply le_antisymm
    · intro l hl
      apply (span_stabilizer_iff v hv _).mpr
      obtain ⟨u,hu, rfl⟩ := hvE
      exact (central_error_iff m hρ l u).mp
        (commutator_le.mp (commutator_commutatorPreimage_le ⊤ E (center L)
          le_normalizer_of_normal) l hl u hu)
    · apply le_commutatorPreimage le_top
      apply commutator_le.mpr
      intro l hl u hu
      let uU : blockU L := ⟨u,hEU hu⟩
      apply (central_error_iff m hρ l uU).mpr
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hE uU hu)
      rw [← hc, map_smul, (span_stabilizer_iff v hv _).mp hl]
  have hres := embedded_residual_centralizer_eq_central_preimage
    (blockU L) E (center L) (pCore_isPGroup.to_le blockU_le_core) hEU le_rfl
  change commutatorPreimage (⊤ : Subgroup L) E (center L) = _ at hD
  rw [hres, map_embedded_pResidual, hD, map_comap_eq, component_range]

include hρ in
/-- The same coordinates simultaneously mark the full residual as A₄. -/
theorem centralizer_residual_image_conjugate (hb : IsShort L) (E : Subgroup L)
    (hEU : E ≤ blockU L) (v : Vector) (hv : v ≠ 0)
    (hvE : ∃ u : blockU L, (u : L) ∈ E ∧ modulePoint m u = v)
    (hE : ∀ u : blockU L, (u : L) ∈ E →
      modulePoint m u ∈ Submodule.span (ZMod 2) {v}) :
    ∃ g : S,
      (((pResidual 2 (centralizer (E : Set L))).map (centralizer (E : Set L)).subtype).map
        (componentPermutation m)).map (MulAut.conj g).toMonoidHom = K := by
  rw [centralizer_residual_image m hρ hb E hEU v hv hvE hE]
  exact OrdinaryNormalizer.point_residual_conjugate _ le_rfl _ (finrank_span_singleton hv)
end CFSG.Quasithin.ChapterC.AlternatingSixBlockAction
