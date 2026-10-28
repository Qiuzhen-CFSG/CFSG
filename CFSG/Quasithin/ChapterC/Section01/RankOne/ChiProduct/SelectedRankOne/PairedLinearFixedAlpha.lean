module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.PairedFactorOrbit.AlphaCentralizer
/-!
# The canonical paired component retains a nonzero alpha fixed subgroup

The actual C.1.17 first component maps to the first factor of the original
paired action. The second fixed line therefore gives nontrivial fixed points
in alpha for this same component, retaining its literal quotient and localV.
Source: Aschbacher--Smith C.1.26 and 10.2.3(4), pp.132 and746--747.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
theorem first_component_localClass_with_alpha_fixed
    {C : GroupClass.{u}} (h36 : Chapter1.Section02.A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)
    let B := baumann (T : Subgroup G)
    ∃ L : Subgroup G, L.IsCComponent ∧ L.map q = d.first.map Y.subtype ∧
      (solvableResidual (factorPreimage q Y d.first)).map (factorPreimage q Y d.first).subtype = L ∧
      U ≤ normalizer (L : Set G) ∧ B ≤ normalizer (L : Set G) ∧
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ L ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ L ⊔ B from le_sup_right))).map (L ⊔ B).subtype =
        (⁅U,L⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G)) ∧
      thompsonAlpha (T : Subgroup G) ⊓ centralizer (L : Set G) ≠ ⊥ := by
  obtain ⟨L,hL,hi,hcan,hUL,hBL,hlocal,hv⟩ :=
    first_component_localClass h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  let := hL.perfect
  have hp : IsPPerfect 2 L := by
    intro N hN hp
    let := hN
    let : Group.IsNilpotent (L ⧸ N) := hp.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := L)]
    exact solvableResidual_le_of_solvable_quotient N
  exact ⟨L,hL,hi,hcan,hUL,hBL,hlocal,hv,
    paired_source_alpha_centralizer_nontrivial T hP U hU hJ q hq hk d F c hexchange L hp hi.le⟩
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
