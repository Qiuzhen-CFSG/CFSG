module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.FixedPairNonsolvable.PairedLinear

/-!
# Nonsolvable paired source on the original omega-center module

Characteristic two proves that the original omega-center closure is reduced.
Proper control for the already chosen pair forces the original Thompson
subgroup to move it. The genuine paired linear source then produces an
outside ambient chi-block with exactly that movement and module support.
The marked paired action is the original B.6.9 source action.

Source: Aschbacher--Smith C.1.26--28 and 14.1.11, pp.132--134,978.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource GlaubermanNiles FixedPairSolvable
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

theorem paired_linear_source_of_fixed_pair_escape
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
    (D : CharacteristicPair (baumann (T : Subgroup G))) (hD : D.Universal.{u,u})
    (hM : control T D ≠ ⊤) :
    ∃ L : Subgroup G, ¬ L ≤ control T D ∧ IsChiBlockIn L ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  have hU : IsPReduced 2 U := hspan ▸ omegaCenter_normalClosure_reduced T
    ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit)
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G) := by
    apply thompson_moves_of_escape T D ⊤ U le_top le_top
    · rw [hspan]
      exact inf_le_left.trans le_normalClosure
    · exact fun hh => hM (top_unique hh)
  exact paired_linear_moved_chi_of_fixed_pair_escape h36 hG T hP U hU hJ q hq hk hs hfit d F c
    hexchange D hD hM

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.FixedPairNonsolvable
