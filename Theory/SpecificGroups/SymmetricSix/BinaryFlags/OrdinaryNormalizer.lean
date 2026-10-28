module

public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalResidualCard
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PairNormalizer
public import Theory.GroupTheory.PResidual.PerfectCover
/-!
# Two-perfect subgroups of the natural point-residual normalizer

The common fixed letters of the two generating three-cycles in the
standard A₄ are exactly its last two letters. Consequently its normalizer
in S₆ lies in the duad stabilizer, whose two-residual is that same A₄.
Conjugating a natural line to the standard duad line transports this fact
to every line and every permutation group containing A₆.

The duad transport follows NaturalResidualCard; the new calculation is
normalizer containment. This is the ordinary six-letter calculation,
independent of automorphisms of the triple cover.
Source: Aschbacher–Smith §B.3, pp.83–85, Notation 13.2.1, p.877,
and the local action calculation for 13.8.20, p.954/PDF p.971.
-/

@[expose] public section
open Subgroup
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
open NaturalGeometry NaturalPairing BinaryPermutation Representation.BinaryOffender
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

/-- A line residual is conjugate to the literal four-letter A₄. -/
theorem point_residual_conjugate (I : Subgroup S)
    (hI : alternatingGroup (Fin 6) ≤ I) (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) :
    let M := I ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) P
    ∃ g : S, ((pResidual 2 M).map M.subtype).map (MulAut.conj g).toMonoidHom = K := by
  obtain ⟨g, rfl⟩ := line_is_image P hP
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
  exact ⟨g⁻¹, he⟩

/-- Every two-perfect six-letter subgroup normalizing a natural-line residual
lies in that residual. -/
theorem le_point_residual_of_isPPerfect (I : Subgroup S)
    (hI : alternatingGroup (Fin 6) ≤ I) (P : Submodule (ZMod 2) V)
    (hP : Module.finrank (ZMod 2) P = 1) (A : Subgroup S)
    (hA : IsPPerfect 2 A) :
    let M := I ⊓ subspaceStabilizer (naturalRepresentation (Fin 6)) P
    let R := (pResidual 2 M).map M.subtype
    A ≤ normalizer (R : Set S) → A ≤ R := by
  dsimp only
  intro hn
  obtain ⟨g, hg⟩ := point_residual_conjugate I hI P hP
  let e := MulAut.conj g
  have hAn : A.map e.toMonoidHom ≤ normalizer (K : Set S) := by
    rw [← hg]
    exact (map_mono hn).trans (le_normalizer_map e.toMonoidHom)
  have hperf : IsPPerfect 2 (A.map e.toMonoidHom) :=
    hA.of_surjective (e.toMonoidHom.subgroupMap A) (e.toMonoidHom.subgroupMap_surjective A)
  have hAK : A.map e.toMonoidHom ≤ K := by
    have hres := embedded_pResidual_mono 2 (hAn.trans normalizer_K_le_H1)
    rw [residual_H1, (pResidual_eq_top_iff 2 _).mpr hperf,
      ← MonoidHom.range_eq_map, range_subtype] at hres
    exact hres
  rw [← hg] at hAK
  exact (map_le_map_iff_of_injective e.injective).mp hAK
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.OrdinaryNormalizer
