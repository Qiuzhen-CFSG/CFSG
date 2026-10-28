module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.Selection.Recognition.BorelHull.Cover
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary

/-!
# Coverage in the actual binary derived G₂ group

The checked root calculation makes one Sylow subgroup of G₂(2)′
self-normalizing. Sylow conjugacy gives this for every Sylow, and the actual
model equivalence transports it to the component. Simplicity and perfectness
are inherited from that component, so no independent simplicity calculation
or identification with a different small group is needed.

Source: Aschbacher--Smith, Theorem C on p.33 and 15.3.35 on p.1139.
The root calculations use the licensed ATLAS port (LICENSES/ATLAS.txt).
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull

/-- Normalizer coverage for the commutator of the actual binary octonion group. -/
theorem g2_derived_twoSubgroupNormalizerCover
    {K : Type*} [Group K] [Finite K] [IsSimpleGroup K] [Group.IsPerfect K]
    (hK : Nonempty (K ≃* commutator (Atlas.G2.Model (ZMod 2)))) :
    TwoSubgroupNormalizerCover K := by
  obtain ⟨e⟩ := hK
  apply twoSubgroupNormalizerCover_of_self_normalizing
  intro P
  have hs : Function.Surjective e.toMonoidHom := e.surjective
  let Q := P.mapSurjective (f := e.toMonoidHom) hs
  let U : Sylow 2 (commutator (Atlas.G2.Model (ZMod 2))) :=
    Atlas.G2.BinaryParabolicPair.derivedSylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (commutator (Atlas.G2.Model (ZMod 2))) U Q
  have he : (U : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))).map
      (MulAut.conj g).toMonoidHom = (Q : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) :=
    congrArg Sylow.toSubgroup hg
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  change (normalizer ((P : Subgroup K) : Set K)).map e.toMonoidHom = _
  rw [map_equiv_normalizer_eq]
  change normalizer ((Q : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) :
    Set (commutator (Atlas.G2.Model (ZMod 2)))) = (Q : Subgroup _)
  have hU : normalizer ((U : Subgroup (commutator (Atlas.G2.Model (ZMod 2)))) :
      Set (commutator (Atlas.G2.Model (ZMod 2)))) = (U : Subgroup _) :=
    Atlas.G2.DerivedNormalizerSolvable.binary_normalizer_derivedSylow
  rw [← he, ← map_equiv_normalizer_eq, hU]

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.Selection.BorelHull
