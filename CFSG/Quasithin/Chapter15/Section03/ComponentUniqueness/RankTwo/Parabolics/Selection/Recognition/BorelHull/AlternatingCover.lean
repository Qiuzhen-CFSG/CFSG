module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary

/-!
# Alternating-six and binary derived symplectic coverage

The actual A₆ Sylow two-subgroups are self-normalizing. Transport through the
given model equivalence therefore supplies normalizer coverage. For the derived
symplectic branch we use the checked polar equivalence after taking the central
quotient and then its commutator, preserving the source's order of operations.
Simplicity and perfectness are inherited from the actual component.

Source: Aschbacher--Smith, 1.1.5(3)(c), pp.501--502, Theorem C on p.33,
and the parabolic step of 15.3.35 on p.1139.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

variable {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]

/-- Coverage for the actual alternating-six model. -/
theorem alternating_six_twoSubgroupNormalizerCover
    (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) : TwoSubgroupNormalizerCover K := by
  obtain ⟨e⟩ := hK
  apply twoSubgroupNormalizerCover_of_self_normalizing
  intro P
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Sylow.normalizer_map_surjective P e.toMonoidHom e.surjective]
  exact AlternatingSix.ShadowLocal.sylow_normalizer_eq (P.mapSurjective e.surjective)

/-- Coverage for the literal commutator of the projective binary symplectic group. -/
theorem symplectic_derived_twoSubgroupNormalizerCover
    (hK : Nonempty (K ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨e⟩ := hK
  exact alternating_six_twoSubgroupNormalizerCover
    ⟨e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix⟩

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
