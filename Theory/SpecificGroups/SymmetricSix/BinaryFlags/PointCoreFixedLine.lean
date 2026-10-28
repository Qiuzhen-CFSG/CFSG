module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.SylowGeometry
/-!
# The fixed vector of a six-letter point core

The full point core fixes the marked nonzero vector in the binary natural
module. An element fixing that vector stabilizes its line and consequently
normalizes the two-core of its line stabilizer. Both statements use literal
conjugation in S6 and transport the canonical pair vector.

Source: the point stabilizers in Aschbacher--Smith B.3.4 and Notation 13.2.1;
used for the edge-kernel identification in Meierfrankenfeld--Stellmacher
(1993), (5.9), printed pp.920--921.
-/

public noncomputable section
open Subgroup BinaryPermutation
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreFixedLine
open NaturalGeometry
private theorem canonical_fixed (g:S) (hg:g∈H1) :
    naturalRepresentation Ω g (pairVector 4 5)=pairVector 4 5 := by
  rw [pairVector_map]
  apply (pairVector_eq_iff (g.injective.ne (by decide)) (by decide)).mpr
  change (pair 4 5).image g=pair 4 5 at hg
  simpa only [pair,Finset.image_insert,Finset.image_singleton] using hg

/-- The marked full point core fixes its distinguished natural vector. -/
theorem conjugate_core_fixes (u g:S)
    (hg:g∈pointCore.map (MulAut.conj u).toMonoidHom) :
    naturalRepresentation Ω g (naturalRepresentation Ω u (pairVector 4 5))=
      naturalRepresentation Ω u (pairVector 4 5) := by
  obtain ⟨k,hk,rfl⟩ := hg
  change naturalRepresentation Ω (u*k*u⁻¹) (naturalRepresentation Ω u (pairVector 4 5))=_
  rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel_right,map_mul,Module.End.mul_apply,
    canonical_fixed k (pointCore_le_flag hk).1]

/-- A fixer of the marked vector normalizes the corresponding full point core. -/
theorem normalizes_core_of_fixes (u g:S)
    (hg:naturalRepresentation Ω g (naturalRepresentation Ω u (pairVector 4 5))=
      naturalRepresentation Ω u (pairVector 4 5)) :
    g∈normalizer (pointCore.map (MulAut.conj u).toMonoidHom:Set S) := by
  have hs : g∈flagStabilizer (move u canonicalLine) := by
    apply (NaturalPairing.mem_stabilizer_iff_map _ _).mpr
    change (canonicalLine.map (naturalRepresentation Ω u)).map (naturalRepresentation Ω g)=
      canonicalLine.map (naturalRepresentation Ω u)
    rw [canonicalLine,Submodule.map_span,Set.image_singleton,
      Submodule.map_span,Set.image_singleton,hg]
  have hn := (flagStabilizer (move u canonicalLine)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image (flagStabilizer (move u canonicalLine))
      (pCore 2 (flagStabilizer (move u canonicalLine))))
  change flagStabilizer (move u canonicalLine)≤
    normalizer ((flagStabilizer (move u canonicalLine)).pCoreIn 2:Set S) at hn
  rw [line_core_of_marking] at hn
  exact hn hs
end Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreFixedLine
