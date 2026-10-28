module
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PResidual.SubnormalSupplement

/-!
# Generation by a two-element in a quasisimple extension

In a two-core-free group with a normal quasisimple subgroup and two-group
quotient, a normal subgroup containing a nonidentity two-element contains
the quasisimple subgroup. Otherwise the component dichotomy and the
self-centralizing generalized Fitting subgroup put that normal subgroup
in the component center, whose two-core is trivial.

Applying this to the literal quotient by O₂ gives normal-closure generation
in a C-component extension. This is the group-theoretic input to MS93
(2.3)(b), used in (3.8), printed pp.857 and 877. Central covers are retained.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- A normal subgroup containing a nontrivial two-element contains the component. -/
theorem quasisimple_le_normal_of_two_escape
    (K N S : Subgroup G) [K.Normal] [N.Normal] [IsQuasisimple K]
    (hquot : IsPGroup 2 (G ⧸ K)) (hcore : pCore 2 G = ⊥)
    (hS : IsPGroup 2 S) (x : G) (hxS : x ∈ S) (hxN : x ∈ N)
    (hne : x ≠ 1) : K ≤ N := by
  have hK : IsComponent G K :=
    ⟨(inferInstance : K.Normal).isSubnormal, inferInstance⟩
  rcases hK.normal_dichotomy N with h | hc
  · exact h
  have hF := generalizedFitting_eq_of_quasisimple_two_quotient K hquot hcore
  have hNC : N ≤ centralizer (K : Set G) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc)
  have hNK : N ≤ K := hNC.trans (hF ▸ centralizer_generalizedFitting_le G)
  let : IsMulCommutative N := isMulCommutative_iff.mpr fun a b =>
    Subtype.ext (hNC a.property b (hNK b.property)).symm
  have hSP : S.subgroupOf N ≤ pCore 2 N := le_sSup ⟨inferInstance,hS.comap_subtype⟩
  have hPN : (pCore 2 N).map N.subtype ≤ pCore 2 G :=
    le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,pCore_isPGroup.map N.subtype⟩
  have hxP : x ∈ pCore 2 G := hPN (mem_map_of_mem N.subtype
    (hSP (show (⟨x,hxN⟩ : N) ∈ S.subgroupOf N from hxS)))
  exact (hne (mem_bot.mp (hcore ▸ hxP))).elim

/-- A normal subgroup meeting the supplement outside O₂ generates with it. -/
theorem normal_sup_eq_top_of_two_escape
    (K N S : Subgroup G) [K.Normal] [N.Normal]
    (hK : K.IsCComponent) [IsQuasisimple (K ⧸ pCore 2 K)]
    (hS : IsPGroup 2 S) (hgen : K ⊔ S = ⊤) (hQS : pCore 2 G ≤ S)
    (x : G) (hxS : x ∈ S) (hxN : x ∈ N) (hxQ : x ∉ pCore 2 G) :
    N ⊔ S = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  let B := K.map q
  let C := N.map q
  let : B.Normal := Normal.map inferInstance q hq
  let : C.Normal := Normal.map inferInstance q hq
  let : IsQuasisimple B := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hquot : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ B) :=
    isPGroup_quotient_of_sup_eq_top B (S.map q) (hS.map q) (by
      rw [← Subgroup.map_sup,hgen,map_top_of_surjective q hq])
  have hBC : B ≤ C := quasisimple_le_normal_of_two_escape B C (S.map q)
    hquot (pCore_quotient_pCore_eq_bot 2) (hS.map q) (q x)
    (mem_map_of_mem q hxS) (mem_map_of_mem q hxN)
    (fun he => hxQ ((QuotientGroup.eq_one_iff x).mp he))
  have hKNQ : K ≤ N ⊔ pCore 2 G := by
    have hh := map_le_iff_le_comap.mp hBC
    simpa only [C,comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  exact top_unique (by
    rw [← hgen]
    exact sup_le (hKNQ.trans (sup_le_sup_left hQS N)) le_sup_right)

end Theory.GroupTheory
