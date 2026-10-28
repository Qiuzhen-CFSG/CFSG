module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry.CoreGeneration
public import Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction

/-!
# Transporting the irreducible parabolic core action

Under a supplied isomorphism I* ≃ S₈ carrying N* to the stabilizer of two
four-point blocks, the image of O₂(N) is a normal two-subgroup of that
stabilizer. It therefore lies in the concrete V₄ × V₄ two-core. Every
N*-invariant subgroup of the core image is zero or the entire target core,
and hence is zero or the entire image of O₂(N).

This proves the precise irreducibility interface used by `CoreGeneration`.
It needs no equality between the star kernel and O₂(I). The source assembly
supplies the actual marked parabolic identification for N = XS.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, proof of 15.3.32(6), printed p.1133 (PDF p.1150).
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
open Subgroup
open Theory.SpecificGroups.SymmetricEight
variable {G : Type*} [Group G]

/-- The actual marked four-block parabolic has irreducible star core image. -/
theorem starCoreIrreducible_of_fourStabilizer [Finite G] (d : LocalData G)
    {I N : Subgroup G} (hNI : N ≤ I)
    (e : d.Star I ≃* Equiv.Perm (Fin 8))
    (hN : (d.starImage I N).map e.toMonoidHom = A6ShadowTwoLocals.fourStabilizer) :
    StarCoreIrreducible d I N := by
  let K := d.starImage I (N.pCoreIn 2)
  let f := e.toMonoidHom
  have hQI : N.pCoreIn 2 ≤ I := (pCoreIn_le 2 N).trans hNI
  have hKp : IsPGroup 2 K :=
    ((isPGroup_pCoreIn 2 N).of_equiv (subgroupOfEquivOfLe hQI).symm).map (d.starMap I)
  have hNK : d.starImage I N ≤ normalizer (K : Set (d.Star I)) := by
    have hn : N ≤ normalizer (N.pCoreIn 2 : Set G) :=
      N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
    have hr : N.subgroupOf I ≤ normalizer ((N.pCoreIn 2).subgroupOf I : Set I) :=
      (comap_mono hn).trans (le_normalizer_comap I.subtype)
    exact (map_mono hr).trans (le_normalizer_map (d.starMap I))
  have hKH : K.map f ≤ A6ShadowTwoLocals.fourStabilizer := by
    rw [← hN]
    exact map_mono (map_mono (comap_mono (pCoreIn_le 2 N)))
  have hHK : A6ShadowTwoLocals.fourStabilizer ≤ normalizer (K.map f : Set _) := by
    rw [← hN]
    exact (map_mono hNK).trans (le_normalizer_map f)
  have hcore : K.map f ≤ A6ShadowTwoLocals.fourStabilizer.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hKp.map f) hKH hHK
  intro A hAK hNA
  have hAK' : A.map f ≤ K.map f := map_mono hAK
  have hHA : A6ShadowTwoLocals.fourStabilizer ≤ normalizer (A.map f : Set _) := by
    rw [← hN]
    exact (map_mono hNA).trans (le_normalizer_map f)
  rcases FourBlockCoreAction.fourStabilizer_core_irreducible (A.map f)
      (hAK'.trans hcore) hHA with hzero | hfull
  · exact Or.inl ((A.map_eq_bot_iff_of_injective e.injective).mp hzero)
  · right
    apply Subgroup.map_injective (f := f) e.injective
    apply le_antisymm hAK'
    rw [hfull]
    exact hcore

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.EightGeometry
