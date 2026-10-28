module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.ControlSource
/-!
# Canonical-module paired linear source

Characteristic two makes the original omega-center span reduced, and
proper characteristic-normalizer control forces Thompson movement.
The actual paired source then supplies an outside moved chi-block with
its block module supported in that same canonical subgroup.

Source: Aschbacher–Smith C.1.26–28, printed pp.132–134.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem paired_linear_outside_of_control
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (hspan : U = normalClosure (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (M : Subgroup G) (hcpu : (T : Subgroup G).characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ M ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  have hU : IsPReduced 2 U := hspan ▸ omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  have hJ := thompson_moves_omega_closure_of_control T hTne U hspan M hcpu hM
  exact paired_linear_outside_moved_chi h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange M hcpu hM
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
