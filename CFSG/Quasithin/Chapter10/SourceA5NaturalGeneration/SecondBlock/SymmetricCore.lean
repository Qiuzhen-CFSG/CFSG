module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.ResidualCore
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.SeedGeneration
/-!
# The entire H* core from one or two residual blocks

A residual block, or a pair of conjugate blocks covering the residual,
makes core squares residual-fixed. The zero Sylow-center fixed subgroup
kills them. The entire core is consequently reduced, and actual Thompson
movement passes to it from the given reduced module. The seed-centralizer
source theorem then proves generation of the whole core by the residual,
including the genuine single-component case.
Source: Aschbacher--Smith 10.2.3(4), p.747, and E.2.3, pp.216--217.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC ChapterE.ThompsonAction
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Full-core movement works for a single block as well as a conjugate pair. -/
theorem source_block_residual_full_core_moved
    (hG : IsSQTK KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) (hU : IsPReduced 2 U)
    (hns : ¬ Group.IsSolvable G)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (hfit : generalizedFitting G = pCore 2 G)
    (Z : Subgroup G) (hZU : Z ≤ U)
    (hCZ : centralizer (Z : Set G) = (T : Subgroup G))
    (hz : omegaCenterIn (T : Subgroup G) ⊓ center G = ⊥)
    (K : Subgroup G) (hb : IsBlock K)
    (hR : pResidual 2 G = K ∨
      ∃ t : G, pResidual 2 G = K ⊔ K.map (MulAut.conj t).toMonoidHom) :
    IsElementaryAbelian 2 (pCore 2 G) ∧
      pCore 2 G = ⁅pCore 2 G,pResidual 2 G⁆ := by
  have hfixed := core_residual_fixed_eq_bot_of_omega_center T hz
  have hE : IsElementaryAbelian 2 (pCore 2 G) := by
    rcases hR with hR | ⟨t,hR⟩
    · exact hb.ambient_core_elementary_of_residual hR hfixed
    · exact hb.ambient_core_elementary_of_pair_core_centralizer
        (hb.map_equiv (MulAut.conj t)) (hR ▸ hfixed)
  let := hE
  have hc : centralizer (pCore 2 G : Set G) = pCore 2 G :=
    le_antisymm (by rw [←hfit]; exact centralizer_generalizedFitting_le G)
      (le_centralizer_iff_isMulCommutative.mpr inferInstance)
  have hQ : IsPReduced 2 (pCore 2 G) := by
    refine ⟨inferInstance,inferInstance,?_⟩
    let f := QuotientGroup.quotientMulEquivOfEq hc.symm
    rw [←pCore_map_iso 2 f,pCore_quotient_pCore_eq_bot,Subgroup.map_bot]
  refine ⟨hE,source_module_eq_commutator_of_seed_centralizer hG T hP _ hQ hns ?_
    Z (hZU.trans hU.le_pCore) hCZ hfixed⟩
  exact fun h => hJ (h.trans (centralizer_le hU.le_pCore))

end CFSG.Quasithin.Chapter10
