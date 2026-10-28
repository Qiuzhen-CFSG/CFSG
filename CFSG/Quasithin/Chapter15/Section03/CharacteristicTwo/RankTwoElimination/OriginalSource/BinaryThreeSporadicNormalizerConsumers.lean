module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource.BinaryThreePointSporadicPlacement

/-!
# Native sporadic normalizer consumers

The native placements are consumed at the exact normal-component interface.
For M₂₃, a component-normalizing overgroup transports into the certified
heptad stabilizer while retaining the full Sylow marking.  For Held, the
self-normalizing max5 placement forces any overgroup normalizing the marked
PSL₃(2) component to equal that component.  No quotient-normalizer lift or
unmarked carrier assumption is introduced.
-/
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry

/-- An M₂₃ overgroup normalizing the actual marked PSL₃(2) component is carried
by the same full-Sylow conjugator into the native heptad stabilizer. -/
theorem binary_three_m23_normal_component_heptad
    (S : Sylow 2 M23) (B A : Subgroup M23)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup M23) ≤ normalizer (B : Set M23))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hA : A ≤ normalizer (B : Set M23)) :
    ∃ g : M23,
      (S : Subgroup M23).map (MulAut.conj g).toMonoidHom =
        FusionCertificate.subgroup ∧
      A.map (MulAut.conj g).toMonoidHom ≤
        MulAction.stabilizer M23 FourNormalizers.fixedSet := by
  obtain ⟨g,hS,hN⟩ := binary_three_mathieuTwentyThree_heptad_placement S B hB hSB eB
  refine ⟨g,hS,?_⟩
  exact (map_mono (f := (MulAut.conj g).toMonoidHom) hA).trans hN

/-- In the Held native carrier, a component-normalizing overgroup containing
B cannot be proper: the actual max5 placement is self-normalizing. -/
theorem binary_three_held_normal_component_eq
    (S : Sylow 2 Held.He) (B A : Subgroup Held.He)
    (hB : B ∈ ChapterA.Section03.localCComponents S)
    (hSB : (S : Subgroup Held.He) ≤ normalizer (B : Set Held.He))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (hBA : B ≤ A) (hA : A ≤ normalizer (B : Set Held.He)) : A = B := by
  obtain ⟨⟨g,hg⟩,hS,hn⟩ := binary_three_held_actual_max5 S B hB hSB eB
  exact le_antisymm (hA.trans_eq hn) hBA

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open Sporadic.Mathieu Sporadic.Mathieu.M23Geometry
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The M₂₃ heptad placement transports to an arbitrary actual containing
C-component, retaining the original Sylow intersection and component
normalizer. -/
theorem binary_three_containing_m23_placement
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents T)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup X) ≤ normalizer (B : Set X))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) (eK : K ≃* M23) :
    ∃ (S : Sylow 2 K) (g : M23),
      ((S.mapSurjective (f := eK.toMonoidHom) eK.surjective : Sylow 2 M23) :
          Subgroup M23).map (MulAut.conj g).toMonoidHom = FusionCertificate.subgroup ∧
      ((normalizer (B.subgroupOf K : Set K)).map eK.toMonoidHom).map
          (MulAut.conj g).toMonoidHom ≤
        MulAction.stabilizer M23 FourNormalizers.fixedSet := by
  obtain ⟨S,hS,hl,hn⟩ :=
    exists_local_sylow_normalizing T hB hK.subnormal hBK hTB
  let A := B.subgroupOf K
  let a := subgroupOfEquivOfLe hBK
  let aq := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let c := eK.subgroupMap A
  let cq := QuotientGroup.congr _ _ c (pCore_map_iso 2 c)
  let : Group.IsSolvable eK.toMonoidHom.ker := by
    rw [eK.toMonoidHom.ker_eq_bot eK.injective]
    infer_instance
  let P := S.mapSurjective (f := eK.toMonoidHom) eK.surjective
  let D := A.map eK.toMonoidHom
  have hlD : D ∈ ChapterA.Section03.localCComponents P :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hl eK.toMonoidHom
  have hnD : (P : Subgroup M23) ≤ normalizer (D : Set M23) :=
    (map_mono (f := eK.toMonoidHom) hn).trans (A.le_normalizer_map eK.toMonoidHom)
  let eD := cq.symm.trans (aq.trans eB)
  obtain ⟨g,hPD,hND⟩ := binary_three_mathieuTwentyThree_heptad_placement
    P D hlD hnD eD
  refine ⟨S,g,hPD,?_⟩
  have hmap : (normalizer (A : Set K)).map eK.toMonoidHom = normalizer (D : Set M23) :=
    map_normalizer_eq_of_bijective A eK.bijective
  change (((normalizer (A : Set K)).map eK.toMonoidHom).map
      (MulAut.conj g).toMonoidHom) ≤ _
  rw [hmap]
  exact hND

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings

/-- The Held placement gives the same equality in an arbitrary containing
component: an overgroup A lying in K and normalizing B is exactly B. -/
theorem binary_three_containing_held_normalizer_eq
    {X : Type*} [Group X] [Finite X] (T : Sylow 2 X) {B K A : Subgroup X}
    (hB : B ∈ ChapterA.Section03.localCComponents T)
    (hK : K.IsCComponent) (hBK : B ≤ K)
    (hTB : (T : Subgroup X) ≤ normalizer (B : Set X))
    (eB : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) (eK : K ≃* Held.He)
    (hBA : B ≤ A) (hAK : A ≤ K) (hA : A ≤ normalizer (B : Set X)) : A = B := by
  obtain ⟨_,_,hNB,_⟩ := binary_three_containing_held_placement
    T hB hK hBK hTB eB eK
  apply le_antisymm
  · exact (le_inf hAK hA).trans (by rw [inf_comm]; exact hNB.le)
  · exact hBA

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
