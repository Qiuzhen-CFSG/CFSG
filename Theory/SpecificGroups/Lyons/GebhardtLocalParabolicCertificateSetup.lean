module

public import Theory.SpecificGroups.Lyons.GebhardtLocalTowerSetup
public import Theory.GroupTheory.GeneratorCosetCoverFiniteIndex

/-!
# The local parabolic coset-certificate interface

The first four generators, regarded as elements of their generated subgroup,
generate that subgroup. The first three lie in the parabolic. Consequently a
3906-state cover for these four generators is precisely the remaining
certificate needed for the local relative-index bound. Its transitions must
be subgroup-witness equations in the literal Gebhardt presentation.

No order or finiteness of either subgroup is assumed here.

Source: V. Gebhardt, "Two Short Presentations for Lyons' Sporadic Simple
Group", Experimental Mathematics 9 (2000), 333–338, Section 3B.
-/

namespace Lyons.Gebhardt.LocalParabolicCertificate
public section

/-- The four canonical generators as elements of the local subgroup. -/
@[expose] def generator (i : Fin 4) : localSubgroup :=
  ⟨Gebhardt.generator i.castSucc, LocalTower.generator_mem 4 i.castSucc i.isLt⟩

/-- The parabolic viewed inside the local subgroup. -/
abbrev parabolic : Subgroup localSubgroup :=
  LocalTower.parabolic.subgroupOf localSubgroup

theorem closure_range_generator : Subgroup.closure (Set.range generator) = ⊤ := by
  apply Subgroup.map_injective localSubgroup.subtype_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, localSubgroup.range_subtype]
  change Subgroup.closure (localSubgroup.subtype '' Set.range generator) =
    Subgroup.closure (Gebhardt.generator '' {i | i.val < 4})
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i.castSucc, i.isLt, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    refine ⟨generator ⟨i.val, hi⟩, Set.mem_range_self _, ?_⟩
    rfl

theorem generator_mem_parabolic (i : Fin 4) (hi : i.val < 3) :
    generator i ∈ parabolic :=
  LocalTower.generator_mem 3 i.castSucc hi

/-- A witness-producing cover is the finite enumeration contract. -/
abbrev Cover := Subgroup.GeneratorCosetCover parabolic generator (Fin 3906)

end
end Lyons.Gebhardt.LocalParabolicCertificate
