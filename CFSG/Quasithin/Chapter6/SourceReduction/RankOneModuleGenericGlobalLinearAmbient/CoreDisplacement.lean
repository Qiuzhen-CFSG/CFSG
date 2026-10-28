module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralFusion
public import Theory.GroupTheory.PCoreRestriction

/-!
# Core displacements on the original central-line centralizer

Let z be an involution of Z(S) central in the original Sylow T and put
R = O₂(C_G(z)). Sylow restriction gives R ≤ T. Hence R normalizes
C_G(Z(S)), which in turn normalizes R. Their commutator lies in the
intersection with R; core restriction and the proved §5.3.5 calculation
place that intersection in S. Thus R acts trivially on C_G(Z(S))/S.

The final export chooses such a z and also establishes the actual
self-centralizing core from even characteristic. No restriction on the
field degree or orientation is imposed. This supplies the displacement
input for §5.3.7's torus calculation; it does not assert R ≤ S, construct
the exceptional marked Sylow, or establish ambient recognition.
Source: Aschbacher–Smith §5.3.5–7, printed pp.660–661 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- The core of an involution centralizer acts trivially on the actual
whole central-line centralizer modulo S. The involution is central in T. -/
theorem Preparation.linear_centralizer_core_displacement
    (z : G) (hz : z ∈ centerIn (sourceS L H))
    (hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G)) :
    (centralizer ({z} : Set G)).pCoreIn 2 ≤ (T : Subgroup G) ∧
    ⁅(centralizer ({z} : Set G)).pCoreIn 2,
      centralizer (centerIn (sourceS L H) : Set G)⁆ ≤ sourceS L H := by
  let C := centralizer (centerIn (sourceS L H) : Set G)
  let D := centralizer ({z} : Set G)
  let R := D.pCoreIn 2
  have hRT : R ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow D (T.subtype hzT)
    change R ≤ ((T : Subgroup G).subgroupOf D).map D.subtype at hh
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ D from hzT)] at hh
  have hCD : C ≤ D := centralizer_le (Set.singleton_subset_iff.mpr hz)
  have hTZ : (T : Subgroup G) ≤ normalizer (centerIn (sourceS L H) : Set G) := by
    rw [d.linear_center_normalizer h hH hp F hm hF he hmax]
    exact le_inf h.sylow_normalizes (hH.1.1.2.trans (le_normalizer_residual H))
  have hRC : R ≤ normalizer (C : Set G) :=
    hRT.trans (hTZ.trans (normalizer_le_normalizer_centralizer _))
  have hCR : C ≤ normalizer (R : Set G) := hCD.trans
    (D.le_normalizer.trans (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))
  refine ⟨hRT,?_⟩
  have hh : ⁅R,C⁆ ≤ C ⊓ R := le_inf
    (le_normalizer_iff_commutator_le_right.mp hRC)
    (le_normalizer_iff_commutator_le_left.mp hCR)
  exact hh.trans ((inf_pCoreIn_le_of_le 2 hCD).trans_eq
    (d.linear_center_centralizer_core h hH hp F hm hF he hmax))

/-- The actual central involution has a self-centralizing core in T, with
all displacements on C_G(Z(S)) lying in S. These are the original groups,
including in the even-degree and field-four branches. -/
theorem Preparation.linear_exists_centralizer_core_setup :
    ∃ z : G, z ∈ centerIn (sourceS L H) ∧ orderOf z = 2 ∧
      (T : Subgroup G) ≤ centralizer ({z} : Set G) ∧
      (centralizer ({z} : Set G)).pCoreIn 2 ≤ (T : Subgroup G) ∧
      ⁅(centralizer ({z} : Set G)).pCoreIn 2,
        centralizer (centerIn (sourceS L H) : Set G)⁆ ≤ sourceS L H ∧
      centralizer ({z} : Set G) ⊓
        centralizer ((centralizer ({z} : Set G)).pCoreIn 2 : Set G) ≤
          (centralizer ({z} : Set G)).pCoreIn 2 := by
  obtain ⟨z,hz,hz2,hzT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  obtain ⟨hRT,hd⟩ := d.linear_centralizer_core_displacement h hH hp F hm hF he hmax z hz hzT
  refine ⟨z,hz,hz2,hzT,hRT,hd,?_⟩
  exact Chapter1.twoLocal_mem_He_of_sylow_le T (h.qtke.evenCharacteristic T)
    (isTwoLocal_involution_centralizer hz2) hzT

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
