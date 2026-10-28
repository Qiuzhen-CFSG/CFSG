/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Conway/AntipodalStabilizer.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Conway.AntipodalLines
public import Theory.AtlasPort.OtherSporadic.Conway.MinimumVectorStabilizer
/-!
Central signs, antipodal geometry, and faithful quotient actions for the Leech isometry group.
The proofs identify the actual kernels and transport the concrete actions through the central quotient.

Source: Gerald Höhn, `Atlas/Conway/AntipodalStabilizer.lean`, ATLAS revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted to CFSG Lean 4.33.0 with public imports and exposed definition bodies,
preserving the source namespaces and cross-module coordinate reductions.
-/

@[expose] public section

noncomputable section
namespace Atlas.Conway
open Atlas.Codes Atlas.Lattices

/-- Restrict the actual central projection to a vector stabilizer. -/
def vectorStabilizerProjection (v : leech) : fullVectorStabilizer v →* LeechCentralQuotient :=
  leechCentralProjection.comp (fullVectorStabilizer v).subtype

theorem leech_ne_neg_of_ne_zero (v : leech) (hv : v ≠ 0) : v ≠ -v := by
  intro he
  apply hv
  apply Subtype.ext
  ext i
  have h := congrArg (fun z : leech => z.val i) he
  change v.val i = -v.val i at h
  change v.val i = 0
  omega

theorem vectorStabilizerProjection_injective (v : leech) (hv : v ≠ 0) :
    Function.Injective (vectorStabilizerProjection v) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro g hg
  have hk : g.val ∈ leechCentralSigns := by
    rw [← leechCentralProjection_kernel]
    exact hg
  rcases (leechCentralSigns_mem g.val).mp hk with he | he
  · exact Subtype.ext he
  · have hf : g.val.val v = v := g.prop
    rw [he,negationIsometry_apply] at hf
    exact False.elim (leech_ne_neg_of_ne_zero v hv hf.symm)

theorem vectorStabilizerProjection_range (v : leech) :
    (vectorStabilizerProjection v).range =
      MulAction.stabilizer LeechCentralQuotient (antipodalLine v) := by
  ext q
  constructor
  · rintro ⟨g,rfl⟩
    change leechCentralProjection g.val • antipodalLine v = antipodalLine v
    rw [projection_antipodalLine]
    exact congrArg antipodalLine g.prop
  · intro hq
    obtain ⟨g,rfl⟩ := leechCentralProjection_surjective q
    change leechCentralProjection g • antipodalLine v = antipodalLine v at hq
    rw [projection_antipodalLine,antipodalLine_eq_iff] at hq
    rcases hq with hg | hg
    · exact ⟨⟨g,hg⟩,rfl⟩
    · have hf : (negationIsometry*g).val v = v := by
        change negationIsometry.val (g.val v) = v
        rw [hg,negationIsometry_apply,neg_neg]
      refine ⟨⟨negationIsometry*g,hf⟩,?_⟩
      change leechCentralProjection (negationIsometry*g) = leechCentralProjection g
      rw [map_mul]
      have hz : leechCentralProjection negationIsometry = 1 := by
        apply (QuotientGroup.eq_one_iff _).mpr
        exact (leechCentralSigns_mem _).mpr (Or.inr rfl)
      rw [hz,one_mul]

def vectorAntipodalStabilizerEquiv (v : leech) (hv : v ≠ 0) :
    fullVectorStabilizer v ≃*
      MulAction.stabilizer LeechCentralQuotient (antipodalLine v) :=
  (MonoidHom.ofInjective (vectorStabilizerProjection_injective v hv)).trans
    (MulEquiv.subgroupCongr (vectorStabilizerProjection_range v))

theorem vectorAntipodalStabilizerEquiv_compatible (v : leech) (hv : v ≠ 0)
    (g : fullVectorStabilizer v) :
    (vectorAntipodalStabilizerEquiv v hv g).val = leechCentralProjection g.val := rfl

theorem minimum_vector_ne_zero (x : LeechShell 4) : x.val ≠ 0 := by
  intro h
  have hn := x.prop
  rw [h] at hn
  norm_num [integerDot] at hn

end Atlas.Conway
