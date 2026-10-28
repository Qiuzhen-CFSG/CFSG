module
public import Theory.GroupTheory.CComponent.FullSylowJoin
public import Theory.GroupTheory.GeneralizedFitting.SylowOvergroup
public import Theory.GroupTheory.CharacteristicNormalizerRestriction
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.KnownSimple

/-!
# Three-free full-Sylow components lie in the control subgroup

The original two-group R is Sylow in J R by the component-orbit theorem.
Its characteristic-normalizer control restricts to that join. Characteristic
two also restricts, since R contains the ambient two-core. The genuine C.1.29
ordered product has no factors: each chi-zero factor contains a cubic, whereas
the join is three-free. Thus J lies in the original control group M.

This is precisely the three-free branch of C.2.4(1) required to exclude the
moved Suzuki component in original 13.3.12. No block, normality, or ordered
factorization is assumed. Source: Aschbacher--Smith, printed pp.144 and889.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section02Source
variable {G : Type*} [Group G] [Finite G]

/-- The original characteristic control absorbs a three-free C-component
when the original two-subgroup contains a full Sylow intersection. -/
theorem three_free_component_le_control_of_full_sylow
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (R M J : Subgroup G)
    (hR : IsPGroup 2 R) (hcore : pCore 2 G ≤ R)
    (hcpu : R.characteristicNormalizerClosure ≤ M)
    (hc : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (hJ : J.IsCComponent) [IsQuasisimple (J ⧸ pCore 2 J)]
    (hthree : ¬ 3 ∣ Nat.card (J ⧸ pCore 2 J))
    (S : Sylow 2 J) (hS : (S : Subgroup J).map J.subtype ≤ R) : J ≤ M := by
  let D := J ⊔ R
  obtain ⟨T,hT⟩ := hJ.full_sylow_join hR hcore S hS
  have hf : generalizedFitting D = pCore 2 D :=
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (centralizer_pCore_le_of_pCore_le D hc (hcore.trans le_sup_right))
  have hctl : (T : Subgroup D).characteristicNormalizerClosure ≤ M.subgroupOf D := by
    rw [hT]
    exact characteristicNormalizerClosure_subgroupOf_le le_sup_right hcpu
  obtain ⟨n,_,B,hB,_,_,hprod⟩ :=
    RankOne.ChiProduct.SelectedRankOne.ordered_chiZero_product_knownSimple
      (hG.subgroup D) hf T (M.subgroupOf D) hctl
  have h3 : ¬ 3 ∣ Nat.card D := hJ.three_free_join hR hthree
  have hn : n = 0 := by
    by_contra hn
    let i : Fin n := ⟨0,Nat.pos_of_ne_zero hn⟩
    exact h3 ((RankOne.ChiProduct.three_dvd_card_of_chi (hB i).2.chi).trans
      (card_subgroup_dvd_card (B i)))
  subst n
  intro j hj
  obtain ⟨m,b,he⟩ := hprod ⟨j,mem_sup_left hj⟩
  simp only [List.ofFn_zero,List.prod_nil,mul_one] at he
  have hm : (m : D) ∈ M.subgroupOf D := m.property
  rw [← he] at hm
  exact hm
end CFSG.Quasithin.ChapterC.Section02Source
