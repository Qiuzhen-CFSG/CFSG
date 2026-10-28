module

public import Theory.Mathieu.M24.LocalGeometry.SextetCore.Candidate
public import Theory.Mathieu.M24.ValueBoundParabolics.Construction.Generation

/-!
# Generation by the incident octad and sextet stabilizers

The existing three native Sylow extensions generate M24. Conjugating by the
checked sextet coordinate permutation puts each of their generators in the
standard octad or sextet stabilizer. The only new finite checks concern the
three extra generators on 24 points. Thus generation uses the literal native
stabilizers and no maximal-subgroup classification.

Source: Aschbacher–Smith, 2.3.9(7), printed p.526; GLS3, Table 5.3e.
The generating triple is constructed for Aschbacher–Smith E.4.3(2).
-/

@[expose] public section

open Subgroup
namespace Sporadic.Mathieu.M24LocalGeometry.Stabilizers
open M24ValueBoundParabolics.Construction

/-- The actual incident standard octad and sextet stabilizers generate M24. -/
theorem standard_pair_generates :
    octadStabilizer standardOctad ⊔ sextetStabilizer standardSextet = ⊤ := by
  let f := (MulAut.conj SextetCore.transport).toMonoidHom
  have hbase (a : Fin 4) : f (SylowNormalizer.generator a) ∈
      SextetCore.standardSylow.toSubgroup := by
    rw [SextetCore.standardSylow_coe]
    exact mem_map_of_mem _ (SylowNormalizer.generator_mem a)
  have hextra (i : Fin 3) : f (extra i) ∈
      octadStabilizer standardOctad ⊔ sextetStabilizer standardSextet := by
    fin_cases i
    · apply mem_sup_left
      change standardOctad.val.image
        (fun x => SextetCore.transportPerm (extraPoint 0 (SextetCore.transportPerm.symm x))) =
          standardOctad.val
      decide +kernel
    · apply mem_sup_left
      change standardOctad.val.image
        (fun x => SextetCore.transportPerm (extraPoint 1 (SextetCore.transportPerm.symm x))) =
          standardOctad.val
      decide +kernel
    · apply mem_sup_right
      change standardSextet.parts.image (fun A => A.image
        (fun x => SextetCore.transportPerm (extraPoint 2 (SextetCore.transportPerm.symm x)))) =
          standardSextet.parts
      decide +kernel
  have hle : (⨆ i, parabolic i).map f ≤
      octadStabilizer standardOctad ⊔ sextetStabilizer standardSextet := by
    rw [Subgroup.map_iSup]
    apply iSup_le
    intro i
    rw [map_le_iff_le_comap, parabolic, closure_le]
    rintro _ ⟨a, rfl⟩
    change f (localGenerator i a) ∈
      octadStabilizer standardOctad ⊔ sextetStabilizer standardSextet
    fin_cases a
    · exact mem_sup_left (SextetCore.standardSylow_le_octadStabilizer (hbase 0))
    · exact mem_sup_left (SextetCore.standardSylow_le_octadStabilizer (hbase 1))
    · exact mem_sup_left (SextetCore.standardSylow_le_octadStabilizer (hbase 2))
    · exact mem_sup_left (SextetCore.standardSylow_le_octadStabilizer (hbase 3))
    · exact hextra i
  rw [parabolic_iSup, map_top_of_surjective _ (MulAut.conj SextetCore.transport).surjective] at hle
  exact top_unique hle

end Sporadic.Mathieu.M24LocalGeometry.Stabilizers

end
