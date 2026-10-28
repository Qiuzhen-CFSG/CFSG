/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/AntipodalLines.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.LeechCentralQuotient
public import Theory.AtlasPort.OtherSporadic.Lattices.LeechClassCapacity
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/AntipodalLines.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices
attribute [local instance] Classical.propDecidable

/-- An actual antipodal pair in the retained Leech lattice. -/
def LeechAntipodalLine := {s : Finset leech // ∃ v : leech, s = antipodalPair v}

def antipodalLine (v : leech) : LeechAntipodalLine := ⟨antipodalPair v, v, rfl⟩

theorem antipodalLine_neg (v : leech) : antipodalLine (-v) = antipodalLine v :=
  Subtype.ext (antipodalPair_neg v)

theorem antipodalLine_eq_iff (v w : leech) :
    antipodalLine v = antipodalLine w ↔ v = w ∨ v = -w := by
  constructor
  · intro h
    have hv : v ∈ antipodalPair w := by
      have he : antipodalPair v = antipodalPair w := congrArg Subtype.val h
      rw [← he]
      simp [antipodalPair]
    simpa [antipodalPair] using hv
  · rintro (rfl | rfl)
    · rfl
    · exact antipodalLine_neg w

def antipodalLineMap (g : LeechIsometryGroup) (s : LeechAntipodalLine) : LeechAntipodalLine :=
  ⟨s.val.image g.val, by
    obtain ⟨v,hv⟩ := s.prop
    refine ⟨g.val v,?_⟩
    simp [hv,antipodalPair,map_neg]⟩

theorem antipodalLineMap_line (g : LeechIsometryGroup) (v : leech) :
    antipodalLineMap g (antipodalLine v) = antipodalLine (g.val v) := by
  apply Subtype.ext
  simp [antipodalLineMap,antipodalLine,antipodalPair,map_neg]

def antipodalLinePermutation (g : LeechIsometryGroup) : Equiv.Perm LeechAntipodalLine where
  toFun := antipodalLineMap g
  invFun := antipodalLineMap g⁻¹
  left_inv s := by
    obtain ⟨v,hv⟩ := s.prop
    have hs : s = antipodalLine v := Subtype.ext hv
    rw [hs,antipodalLineMap_line,antipodalLineMap_line]
    exact congrArg antipodalLine (g.val.symm_apply_apply v)
  right_inv s := by
    obtain ⟨v,hv⟩ := s.prop
    have hs : s = antipodalLine v := Subtype.ext hv
    rw [hs,antipodalLineMap_line,antipodalLineMap_line]
    exact congrArg antipodalLine (g.val.apply_symm_apply v)

def antipodalLineRepresentation : LeechIsometryGroup →* Equiv.Perm LeechAntipodalLine where
  toFun := antipodalLinePermutation
  map_one' := by
    ext s
    obtain ⟨v,hv⟩ := s.prop
    have hs : s = antipodalLine v := Subtype.ext hv
    change antipodalLineMap 1 s = s
    rw [hs,antipodalLineMap_line]
    rfl
  map_mul' g h := by
    ext s
    obtain ⟨v,hv⟩ := s.prop
    have hs : s = antipodalLine v := Subtype.ext hv
    change antipodalLineMap (g*h) s = antipodalLineMap g (antipodalLineMap h s)
    rw [hs,antipodalLineMap_line,antipodalLineMap_line,antipodalLineMap_line]
    rfl

def quotientAntipodalLineRepresentation : LeechCentralQuotient →* Equiv.Perm LeechAntipodalLine :=
  QuotientGroup.lift leechCentralSigns antipodalLineRepresentation (by
    intro g hg
    rcases (leechCentralSigns_mem g).mp hg with rfl | rfl
    · exact antipodalLineRepresentation.map_one
    · apply Equiv.ext
      intro s
      obtain ⟨v,hv⟩ := s.prop
      have hs : s = antipodalLine v := Subtype.ext hv
      change antipodalLineMap negationIsometry s = s
      rw [hs,antipodalLineMap_line,negationIsometry_apply,antipodalLine_neg])

instance : MulAction LeechCentralQuotient LeechAntipodalLine :=
  MulAction.compHom _ quotientAntipodalLineRepresentation

theorem projection_antipodalLine (g : LeechIsometryGroup) (v : leech) :
    leechCentralProjection g • antipodalLine v = antipodalLine (g.val v) :=
  antipodalLineMap_line g v

end Atlas.Conway
