module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.AlphaOrbit
public import Theory.GroupTheory.ReducedNormal.MovedCentralizer
public import Theory.ElementaryAbelian.Injective
public import Theory.ElementaryAbelian.Join
/-!
# The action kernel of the selected Baumann module

The alpha summand centralized by the residual is central in the selected
group. Thus adjoining it to the moved subgroup changes neither the action
kernel nor elementary abelianness. Reducedness identifies the centralizer
of the moved subgroup with the original module centralizer. These facts
are stated on the literal inclusion Baum(T) → O²(G) Baum(T).

Source: Aschbacher–Smith C.1.17 and C.1.26, printed pp.126 and132.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) = centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm (le_inf (centralizer_le (show (A : Set G) ⊆ (A ⊔ B : Subgroup G) from fun _ hx => (show A ≤ A ⊔ B from le_sup_left) hx)) (centralizer_le (show (B : Set G) ⊆ (A ⊔ B : Subgroup G) from fun _ hx => (show B ≤ A ⊔ B from le_sup_right) hx)))
  exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp inf_le_left)
    (le_centralizer_iff.mp inf_le_right))

omit [Finite G] in
theorem fixed_alpha_central_selected (T L : Subgroup G) :
    thompsonAlpha T ⊓ centralizer (L : Set G) ≤ centralizer ((L ⊔ baumann T : Subgroup G) : Set G) := by
  rw [centralizer_join]
  refine le_inf inf_le_right ?_
  intro e he b hb
  exact (hb.2 e he.1).symm

theorem localKernel_selected_baumann (T U : Subgroup G)
    [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hgen : pResidual 2 G ⊔ T = ⊤)
    (hspan : U = normalClosure (omegaOneCenterAmbient T : Set G))
    (ha : thompsonAlpha T ≤ ⁅U,pResidual 2 G⁆ ⊔
      (thompsonAlpha T ⊓ centralizer (pResidual 2 G : Set G))) :
    GlaubermanNiles.localKernel (inclusion
      (show baumann T ≤ pResidual 2 G ⊔ baumann T from le_sup_right)) =
      (centralizer (U : Set G)).subgroupOf (pResidual 2 G ⊔ baumann T) := by
  let N := pResidual 2 G ⊔ baumann T
  let e := inclusion (show baumann T ≤ N from le_sup_right)
  have hv := localV_selected_baumann_eq_moved_sup_fixed T U (pResidual 2 G) hgen hspan ha
  have hw : ⁅U,pResidual 2 G⁆ ≤ (GlaubermanNiles.localV e).map N.subtype := by
    rw [hv]
    exact le_sup_left
  rw [← hU.centralizer_moved_eq U]
  ext x
  constructor
  · intro hx w hw'
    obtain ⟨v,hv',he⟩ := hw hw'
    change (v:G) = w at he
    have hh := hx v hv'
    have hh' := congrArg (fun a : N => (a : G)) hh
    change w * (x:G) = (x:G) * w
    rw [←he]
    exact hh'
  · intro hx v hv'
    apply Subtype.ext
    have hh : (v : G) ∈ ⁅U,pResidual 2 G⁆ ⊔
        (thompsonAlpha T ⊓ centralizer (pResidual 2 G : Set G)) := by
      rw [←hv]
      exact mem_map_of_mem N.subtype hv'
    have hc : (x:G) ∈ centralizer
        ((⁅U,pResidual 2 G⁆ ⊔ (thompsonAlpha T ⊓ centralizer (pResidual 2 G : Set G)) : Subgroup G) : Set G) := by
      rw [centralizer_join]
      refine ⟨hx,?_⟩
      intro d hd
      exact ((fixed_alpha_central_selected T (pResidual 2 G) hd) x x.property).symm
    exact hc v hh

theorem localV_selected_baumann_elementary (T U L : Subgroup G)
    [U.Normal] [L.Normal] [IsElementaryAbelian 2 U]
    (hgen : L ⊔ T = ⊤)
    (hspan : U = normalClosure (omegaOneCenterAmbient T : Set G))
    (ha : thompsonAlpha T ≤ ⁅U,L⁆ ⊔ (thompsonAlpha T ⊓ centralizer (L : Set G))) :
    IsElementaryAbelian 2 (GlaubermanNiles.localV (inclusion
      (show baumann T ≤ L ⊔ baumann T from le_sup_right))) := by
  let N := L ⊔ baumann T
  let e := inclusion (show baumann T ≤ N from le_sup_right)
  let W := ⁅U,L⁆
  let D := thompsonAlpha T ⊓ centralizer (L : Set G)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left U L)
  let : IsElementaryAbelian 2 (thompsonAlpha T) := omegaOneCenterAmbient_elementaryAbelian _
  let : IsElementaryAbelian 2 D := IsElementaryAbelian.of_le (show D ≤ thompsonAlpha T from inf_le_left)
  have hWN : W ≤ N := (commutator_le_right U L).trans le_sup_left
  have hDW : D ≤ centralizer (W : Set G) :=
    (fixed_alpha_central_selected T L).trans (centralizer_le hWN)
  let : IsElementaryAbelian 2 (W ⊔ D : Subgroup G) := IsElementaryAbelian.sup_of_le_centralizer hDW
  have heq : (GlaubermanNiles.localV e).map N.subtype = W ⊔ D :=
    localV_selected_baumann_eq_moved_sup_fixed T U L hgen hspan ha
  let : IsElementaryAbelian 2 ((GlaubermanNiles.localV e).map N.subtype) := heq.symm ▸ inferInstance
  exact IsElementaryAbelian.of_injective
    ((GlaubermanNiles.localV e).equivMapOfInjective N.subtype N.subtype_injective).toMonoidHom
    ((GlaubermanNiles.localV e).equivMapOfInjective N.subtype N.subtype_injective).injective

end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
