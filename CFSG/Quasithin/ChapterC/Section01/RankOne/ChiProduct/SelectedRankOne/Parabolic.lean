module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.AlphaOrbit
public import Theory.SpecificGroups.SL2.FrattiniParabolic
public import CFSG.Quasithin.ChapterB.Section06To07.RankOneBaumann.FrattiniSource
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.SelfCentralizingCoreInheritance
public import CFSG.Quasithin.ChapterA.Section01.Fitting.Characteristic
/-!
# Minimal-parabolic structure of the actual selected subgroup

Restricting the original action map to the two-residual retains its
O₂,Φ-kernel bound. Transport to the literal residual inside O²(G) Baum(T)
and the rank-one Sylow theorem give unique maximality and nonnormality.
The selected group is normal in G, so characteristic two passes to it.

Source: Aschbacher–Smith C.1.26, p.132, with B.6.8–10.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
open ChapterB
variable {G Q F : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
  [Field F] [Finite F] [CharP F 2]

omit [Finite Q] in
theorem selected_baumann_minimal
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Q) (_hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (c : (pResidual 2 G).map q ≃* SL(2,F))
    (hs : Chapter1.IsSylowIn 2 (baumann (T : Subgroup G))
      (pResidual 2 G ⊔ baumann (T : Subgroup G))) :
    ∃ S : Sylow 2 (pResidual 2 G ⊔ baumann (T : Subgroup G) : Subgroup G),
      (inclusion (show baumann (T : Subgroup G) ≤ pResidual 2 G ⊔ baumann (T : Subgroup G)
        from le_sup_right)).range = S ∧ IsMinimalParabolicOver S ⊤ := by
  let X := pResidual 2 G
  let B := baumann (T : Subgroup G)
  let N := X ⊔ B
  let A := X.subgroupOf N
  let i : A ≃* X := subgroupOfEquivOfLe (show X ≤ N from le_sup_left)
  let f : A →* SL(2,F) := c.toMonoidHom.comp ((q.subgroupMap X).comp i.toMonoidHom)
  have hf : Function.Surjective f := c.surjective.comp
    ((q.subgroupMap_surjective X).comp i.surjective)
  have hfr := RankOneBaumann.residual_centralizer_le_coreFrattini T hP U hU hJ
  have hfker : f.ker ≤ (frattini (A ⧸ pCore 2 A)).comap (QuotientGroup.mk' (pCore 2 A)) := by
    have hik : IsPGroup 2 i.toMonoidHom.ker := by
      rw [(MonoidHom.ker_eq_bot_iff i.toMonoidHom).mpr i.injective]
      exact IsPGroup.of_subsingleton 2 _
    rw [← i.toMonoidHom.comap_frattini_pCore_of_pKernel i.surjective hik]
    intro a ha
    have hqa : q (i a : G) = 1 := by
      have hh : c ((q.subgroupMap X) (i a)) = c 1 := by
        change f a = 1 at ha
        exact ha.trans (map_one c.toMonoidHom).symm
      exact congrArg Subtype.val (c.injective hh)
    have hca : (i a : G) ∈ centralizer (U : Set G) := hk ▸ hqa
    obtain ⟨x,hx,he⟩ := hfr ⟨(i a).property,hca⟩
    have he' : x = i a := Subtype.ext he
    change i a ∈ (frattini (X ⧸ pCore 2 X)).comap (QuotientGroup.mk' (pCore 2 X))
    exact he' ▸ hx
  obtain ⟨S,hS⟩ := hs
  have hSN : (S : Subgroup N) = B.subgroupOf N := by
    apply map_injective N.subtype_injective
    rw [map_subgroupOf_eq_of_le (show B ≤ N from le_sup_right)]
    exact hS
  have hAS : A ⊔ (S : Subgroup N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,hS,map_subgroupOf_eq_of_le (show X ≤ N from le_sup_left),
      ←MonoidHom.range_eq_map,range_subtype]
  refine ⟨S,?_,minimal_over_normal_rankOne_frattini F A S hAS f hf hfker⟩
  rw [hSN]
  ext x
  constructor
  · rintro ⟨b,rfl⟩
    exact b.property
  · intro hx
    exact ⟨⟨x,hx⟩,rfl⟩

theorem selected_baumann_fitting (T L : Subgroup G) [L.Normal]
    (hgen : L ⊔ T = ⊤) (hfit : generalizedFitting G = pCore 2 G) :
    generalizedFitting (L ⊔ baumann T : Subgroup G) =
      pCore 2 (L ⊔ baumann T : Subgroup G) := by
  let : (L ⊔ baumann T).Normal := baumann_residual_join_normal T L hgen
  exact (ChapterA.generalizedFitting_eq_pCore_iff 2).mpr
    (normal_core_selfCentralizing ((ChapterA.generalizedFitting_eq_pCore_iff 2).mp hfit) _)
end CFSG.Quasithin.ChapterC.RankOne.ChiProduct.SelectedRankOne
