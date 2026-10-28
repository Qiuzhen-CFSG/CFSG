module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.Images
public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
/-!
# Original Thompson movement through the residual Frattini kernel

A nontrivial Thompson image in a center-free quasisimple residual acts
nontrivially and therefore generates the full image by commutators.
The genuine minimal-parabolic Frattini bound removes the action kernel
modulo O₂. Two-perfection removes that remaining two-group supplement.
Thus the original residual equals its commutator with the original J(T).

Source: Aschbacher–Smith C.1.26, p.132, with B.6.8 and B.6.10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]

omit [Finite Q] in
theorem residual_moved_of_quasisimple_image
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (hqs : IsQuasisimple ((pResidual 2 G).map q))
    (hJL : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ (pResidual 2 G).map q)
    (hz : center ((pResidual 2 G).map q) = ⊥) :
    pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
  let X := pResidual 2 G
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let A := X.map q
  let C := ⁅X,J⁆
  let : A.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple A := hqs
  have hne : ⁅A,J.map q⁆ ≠ ⊥ := by
    intro he
    have hcent : J.map q ≤ centralizer (A : Set Q) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp he)
    have hb : J.map q = ⊥ := by
      apply le_bot_iff.mp
      intro j hj
      have hjz : (⟨j,hJL hj⟩ : A) ∈ center A := by
        rw [mem_center_iff]
        intro a
        exact Subtype.ext ((hcent hj) a a.property)
      have he1 : (⟨j,hJL hj⟩ : A) = 1 := mem_bot.mp (hz ▸ hjz)
      exact congrArg Subtype.val he1
    exact hJ ((map_eq_bot_iff J).mp hb |>.trans_eq hk)
  have hi : A = ⁅A,J.map q⁆ := by
    have hcomponent : IsComponent Q A := ⟨(inferInstance : A.Normal).isSubnormal,inferInstance⟩
    rcases hcomponent.commutator_dichotomy (J.map q) with hb | he
    · exact (hne hb).elim
    · exact le_antisymm ((le_iSup_conjugates A (J.map q)).trans he.symm.le)
        (commutator_le_left A (J.map q))
  have himage : X.map q ≤ C.map q := by
    change A ≤ ⁅X,J⁆.map q
    rw [map_commutator]
    exact hi.le
  have hfr : X ⊓ q.ker ≤ BaumannArgument.coreFrattini X := by
    rw [hk]
    exact RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ
  have hcover := pResidual_le_sup_of_frattini_kernel 2 C q (pCore 2 X) himage hfr
  have hCX : C ≤ X := commutator_le_left X J
  let D := C.subgroupOf X
  let : D.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left X J)
  have hcover' : (⊤ : Subgroup X) ≤ D ⊔ pCore 2 X := by
    intro x hx
    obtain ⟨c,hc,z,hz',he⟩ := mem_sup_of_normal_right.mp (hcover x.property)
    obtain ⟨z,hz',rfl⟩ := hz'
    have he' : (⟨c,hCX hc⟩:X)*z=x := Subtype.ext he
    rw [←he']
    exact mul_mem_sup hc hz'
  have htop : D = ⊤ := top_le_iff.mp (le_normal_of_isPPerfect_of_le_sup_pGroup
    ⊤ D (pCore 2 X) ((isPPerfect_pResidual 2).of_surjective (topEquiv (G := X)).symm.toMonoidHom
      (topEquiv (G := X)).symm.surjective) pCore_isPGroup hcover')
  exact le_antisymm (subgroupOf_eq_top.mp htop) hCX
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
