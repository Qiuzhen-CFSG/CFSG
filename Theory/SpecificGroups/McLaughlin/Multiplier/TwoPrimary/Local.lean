module

public import Theory.Alternating.Theorem523Reduction
public import Theory.GroupTheory.CentralExtensionSections

/-!
# Central extensions of the certified alternating double cover of degree eight

Schur's degree-eight double cover is universal by GLS3, Theorem 5.2.3(b).
Consequently every finite central extension of this very group splits.
Transport through an actual subgroup isomorphism gives a section over the
literal subgroup inclusion in any finite perfect central cover.

The consumer in `McLaughlin.Multiplier.TwoPrimary` applies central transfer
at odd index. Identifying an actual subgroup with this cover remains separate
from this intrinsic local calculation.

Source: GLS3, Theorem 5.2.3; R. L. Griess, Jr., The Schur multiplier of
McLaughlin's simple group, Arch. Math. 48 (1987), p.31,
doi:10.1007/BF01196350.
-/

public section

namespace Theory.SpecificGroups.McLaughlin.Multiplier.TwoPrimary

open Subgroup Theory.GroupTheory PerfectCentralCovering
open GLS3.Chapter5.SchurPresentation

universe u v

/-- The certified perfect double cover of A₈, with its actual presentation. -/
abbrev DoubleCover := SchurAlternatingGroup 3

/-- Every finite central extension of the certified double cover splits. -/
theorem doubleCover_exists_section
    {E : Type u} [Group E] [Finite E]
    (f : E →* DoubleCover) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) :
    ∃ s : DoubleCover →* E, f.comp s = MonoidHom.id DoubleCover :=
  CentralExtension.exists_section_of_universal_cover
    (schurAlternatingCovering 3)
    (theorem_5_2_3_b_universality 3 (by decide) (by decide)) f hf hc

/-- The exact group order used only after an actual embedding has been supplied. -/
theorem doubleCover_card : Nat.card DoubleCover = 40320 := by
  change Nat.card (SchurAlternatingGroup 3) = 40320
  rw [card_schurAlternatingGroup]
  decide

/-- An actual copy of the certified double cover splits the restriction of
an arbitrary finite perfect central covering, with the subgroup inclusion
retained in the commuting triangle. -/
theorem exists_local_section_of_doubleCover_equiv
    {E : Type u} {G : Type v} [Group E] [Finite E] [Group G]
    (f : Cover E G) (P : Subgroup G) (e : P ≃* DoubleCover) :
    ∃ s : P →* E, f.toMonoidHom.comp s = P.subtype := by
  let M := P.comap f.toMonoidHom
  let q : M →* P := f.toMonoidHom.subgroupComap P
  let g : M →* DoubleCover := e.toMonoidHom.comp q
  have hg : Function.Surjective g := e.surjective.comp
    (f.toMonoidHom.subgroupComap_surjective_of_surjective P f.surjective)
  have hc : g.ker ≤ center M := by
    intro x hx
    have hq : q x = 1 := e.injective (hx.trans e.map_one.symm)
    have hxk : (x : E) ∈ f.toMonoidHom.ker := congrArg Subtype.val hq
    exact mem_center_iff.mpr fun y =>
      Subtype.ext (mem_center_iff.mp (f.ker_le_center hxk) y)
  obtain ⟨t, ht⟩ := doubleCover_exists_section g hg hc
  refine ⟨M.subtype.comp (t.comp e.toMonoidHom), ?_⟩
  ext x
  exact congrArg Subtype.val (e.injective (DFunLike.congr_fun ht (e x)))

end Theory.SpecificGroups.McLaughlin.Multiplier.TwoPrimary
