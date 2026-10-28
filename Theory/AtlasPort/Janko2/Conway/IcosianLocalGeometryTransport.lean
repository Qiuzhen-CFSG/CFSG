/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/IcosianLocalGeometryTransport.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.Janko2.Conway.IcosianAxisCompletion
public import Theory.AtlasPort.Janko2.Conway.IcosianFrameCountInterface

/-!
# IcosianLocalGeometryTransport

A group element taking the first axis to a root point transports neighbors and unique
orthogonal completions. Point normalizers therefore discharge the frame-count
interface.

Source: Gerald Höhn, ATLAS, `Atlas/Conway/IcosianLocalGeometryTransport.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with mapped imports, public module boundaries,
and local proof syntax; concrete carriers and public statements are retained.
-/

@[expose] public section


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Atlas.Conway

abbrev IcosianRootNeighbors (p : IcosianRootPoint) :=
  {q : IcosianRootPoint // IcosianRootPointOrthogonal p q}

/-- Transport of the independently counted axis geometry along a specified
actual Hermitian lattice isometry. No transitivity theorem is assumed. -/
def icosianRootNeighborsEquiv (p : IcosianRootPoint) (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=p) : IcosianAxisNeighbor ≃ IcosianRootNeighbors p where
  toFun q := ⟨g • q.val,by
    rw [← hg]
    exact (icosianRootPointOrthogonal_smul_iff g _ _).mpr q.property⟩
  invFun q := ⟨g⁻¹ • q.val,by
    apply (icosianRootPointOrthogonal_smul_iff g _ _).mp
    simpa only [smul_inv_smul,hg] using q.property⟩
  left_inv q := Subtype.ext (inv_smul_smul g q.val)
  right_inv q := Subtype.ext (smul_inv_smul g q.val)

theorem icosianRootNeighbors_card_of_normalizer (p : IcosianRootPoint) (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=p) : Nat.card (IcosianRootNeighbors p)=10 := by
  rw [← Nat.card_congr (icosianRootNeighborsEquiv p g hg),icosianAxisNeighbors_card]

/-- The explicitly constructed axis completions transport to the root line
normalized by the specified actual isometry. -/
theorem icosianRoot_completion_of_normalizer (p : IcosianRootPoint) (g : icosianHermitianGroup)
    (hg : g • icosianRootAxisPoint 0=p) (q : IcosianRootPoint)
    (hpq : IcosianRootPointOrthogonal p q) :
    ∃! r : IcosianRootPoint,IcosianRootPointOrthogonal p r ∧ IcosianRootPointOrthogonal q r := by
  have hq0 : IcosianRootPointOrthogonal (icosianRootAxisPoint 0) (g⁻¹ • q) := by
    apply (icosianRootPointOrthogonal_smul_iff g _ _).mp
    simpa only [smul_inv_smul,hg] using hpq
  obtain ⟨r,hr,hur⟩ := icosianRootAxis_completion ⟨g⁻¹ • q,hq0⟩
  refine ⟨g • r,⟨?_,?_⟩,?_⟩
  · rw [← hg]
    exact (icosianRootPointOrthogonal_smul_iff g _ _).mpr hr.1
  · simpa only [smul_inv_smul] using
      (icosianRootPointOrthogonal_smul_iff g (g⁻¹ • q) r).mpr hr.2
  · intro t ht
    have hback0 : IcosianRootPointOrthogonal (icosianRootAxisPoint 0) (g⁻¹ • t) := by
      apply (icosianRootPointOrthogonal_smul_iff g _ _).mp
      simpa only [smul_inv_smul,hg] using ht.1
    have hbackq := (icosianRootPointOrthogonal_smul_iff g⁻¹ q t).mpr ht.2
    have he := hur (g⁻¹ • t) ⟨hback0,hbackq⟩
    calc
      t=g • (g⁻¹ • t) := (smul_inv_smul g t).symm
      _=g • r := congrArg (g • ·) he

/-- Structural point normalizations complete the independent local geometry
and hence the unordered frame count. The hypotheses contain no group order,
reflection generation, or frame-transitivity statement. -/
theorem icosianRootFrame_card_of_normalizers
    (hn : ∀ p : IcosianRootPoint,∃ g : icosianHermitianGroup,g • icosianRootAxisPoint 0=p) :
    Nat.card IcosianRootFrame=525 := by
  apply icosianRootFrame_card_of_local_geometry
  · intro p
    obtain ⟨g,hg⟩ := hn p
    exact icosianRootNeighbors_card_of_normalizer p g hg
  · intro p q hpq
    obtain ⟨g,hg⟩ := hn p
    exact icosianRoot_completion_of_normalizer p g hg q hpq

end Atlas.Conway
