module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedLinearLocalClass

/-!
# The local-class conclusion for the original marked component

The reduced minimal-parabolic action has solvable kernel. Its component
lift is therefore uniquely the solvable residual of the literal marked
factor preimage. Any original C-component with that image is the same
component, so C.1.17 applies to its original Baumann join. The two axis
cases retain the same natural marking and Sylow exchanger, exchanging
coordinates together when needed. No central kernel is removed.

Source: Aschbacher–Smith C.1.26 and 10.2.3(4), pp.132 and746,
using the solvable-kernel correspondence A.3.3.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
open ChapterB.RankOneBaumann.PairedFactorOrbit
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
set_option backward.isDefEq.respectTransparency false in
theorem component_localClass_of_first_linear_axis
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
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (K : Subgroup G) (hK : K.IsCComponent)
    (himage : K.map q = d.first.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype) :
    let B := baumann (T : Subgroup G)
    U ≤ normalizer (K : Set G) ∧ B ≤ normalizer (K : Set G) ∧
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map (K ⊔ B).subtype =
        (⁅U,K⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  obtain ⟨K',hK',hi,hcan,hUK,hBK,hloc,hV⟩ :=
    first_component_localClass h36 hG T hP U hU hJ q hq hk hs hfit d F c hexchange
  have hker : q.ker ≤ minimalParabolicCore T hP :=
    hk ▸ RankOneBaumann.reduced_centralizer_le_core T hP U hU hJ
  let : Group.IsSolvable (minimalParabolicCore T hP) := minimalParabolic_core_solvable T hP
  let : Group.IsSolvable q.ker := Group.isSolvable_of_isSolvable_injective (inclusion_injective hker)
  have he : K' = K := by
    rw [←hcan]
    have hp : factorPreimage q (offenderSubgroup
        (NormalElementaryQuotient.representation U q hq hk)) d.first = K ⊔ q.ker := by
      change ((d.first.map _).comap q) = _
      rw [←himage,comap_map_eq]
    rw [hp]
    exact hK.solvableResidual_sup_eq q.ker le_normalizer_of_normal
  exact he ▸ ⟨hUK,hBK,hloc,hV⟩
set_option backward.isDefEq.respectTransparency false in
theorem component_localClass_of_linear_axis
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
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (K : Subgroup G) (hK : K.IsCComponent)
    (himage : K.map q = d.first.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype ∨
      K.map q = d.second.map
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype) :
    let B := baumann (T : Subgroup G)
    U ≤ normalizer (K : Set G) ∧ B ≤ normalizer (K : Set G) ∧
      GlaubermanNiles.InLocalClass (inclusion (show B ≤ K ⊔ B from le_sup_right)) ∧
      (GlaubermanNiles.localV (inclusion (show B ≤ K ⊔ B from le_sup_right))).map (K ⊔ B).subtype =
        (⁅U,K⁆ : Subgroup G) ⊔ (thompsonAlpha (T : Subgroup G) ⊓ centralizer (K : Set G)) := by
  rcases himage with hi | hi
  · exact component_localClass_of_first_linear_axis h36 hG T hP U hU hJ q hq hk
      hs hfit d F c hexchange K hK hi
  · have hex' : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
        ∃ t : T.mapSurjective hq,
          (sourceSwap d).first.map (MulAut.conjNormal (t:H)).toMonoidHom = (sourceSwap d).second ∧
          (sourceSwap d).second.map (MulAut.conjNormal (t:H)).toMonoidHom = (sourceSwap d).first := by
      obtain ⟨t,ht₁,ht₂⟩ := hexchange
      exact ⟨t,ht₂,ht₁⟩
    exact component_localClass_of_first_linear_axis h36 hG T hP U hU hJ q hq hk
      hs hfit (sourceSwap d) F (markedSwap c) hex' K hK hi

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
