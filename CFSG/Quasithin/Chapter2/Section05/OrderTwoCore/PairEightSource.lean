module
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.ResidualSource
public import CFSG.Quasithin.Chapter2.Section05.NormalComponentPairs.NormalizerIntersection
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CrossingMarksSource
public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The actual elementary eight in the order-two core branch

Suppose the original source core has order two. A largest local pair supplies
an inner four E with C_K(E)=E. Its commuting product F=E O₂(H) is elementary
of order eight, meets K in E, and contains Z(S). Normality of K identifies
N_H(F) with N_H(E). The largest-pair theorem therefore makes the original
base Sylow in N_G(F). An equality Fˣ=Fˢ would put xs⁻¹ in that normalizer,
contradicting its intersection with the specified ambient Sylow T.

The theorem preserves the original pair and crossing. It proves the first
normalizer and escape paragraph of Aschbacher--Smith 2.5.21, printed p.565;
it does not assert the later centralizer contradictions.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05
open A6Shadow.Frattini ComponentRefinement ComponentSelection ClassificationModels
variable {G : Type*} [Group G] [Finite G] {H K M U L : Subgroup G}
  {S : Sylow 2 H} {z : G}

theorem largest_pair_conjugate_ne_of_crossing
    (c : MathieuSourceSetup H K M S z) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    {F : Subgroup G} (hF : IsPGroup 2 F) (hzF : z ∈ F)
    (hLN : L ≤ normalizer (F : Set G))
    {x : G} (hxT : x ∈ c.T) (hxS : x ∉ (S : Subgroup H).map H.subtype)
    (s : G) (hs : s ∈ (S : Subgroup H).map H.subtype) :
    F.conjBy x⁻¹ ≠ F.conjBy s⁻¹ := by
  intro he
  have hn : x * s⁻¹ ∈ normalizer (F : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hh := F.conjBy_inv_mul_cancel he
    rw [inv_inv] at hh
    exact hh
  have hxT' : x * s⁻¹ ∈ c.T := c.T.mul_mem hxT (c.T.inv_mem (c.sylow_lt.le hs))
  have hxS' : x * s⁻¹ ∉ (S : Subgroup H).map H.subtype := by
    intro h
    have hh := ((S : Subgroup H).map H.subtype).mul_mem h hs
    exact hxS (by simpa only [inv_mul_cancel_right] using hh)
  exact largest_pair_normal_two_not_normalized_by_crossing c hG hp hUS hF hzF hLN hxT' hxS' hn

theorem largest_pair_eight_of_core_card_two
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ IsBenderModel K)
    (hp : (U,L) ∈ largestLocalPairs M H)
    (hUS : U ≤ (S : Subgroup H).map H.subtype)
    (hcard : Nat.card (twoCore H) = 2) :
    ∃ E : Subgroup G, E ≤ (S : Subgroup H).map H.subtype ⊓ K ∧ IsKleinFour E ∧
      let F := E ⊔ twoCore H
      F ≤ (S : Subgroup H).map H.subtype ∧ IsElementaryAbelian 2 F ∧ Nat.card F = 8 ∧
      K ⊓ F = E ∧ centerIn ((S : Subgroup H).map H.subtype) ≤ F ∧
      L = H ⊓ normalizer (F : Set G) ∧
      U = (S : Subgroup H).map H.subtype ⊓ normalizer (F : Set G) ∧
      (c.T : Subgroup G) ⊓ normalizer (F : Set G) = U ∧
      ∀ x : G, x ∈ c.T → x ∉ (S : Subgroup H).map H.subtype →
        ∀ s ∈ (S : Subgroup H).map H.subtype, F.conjBy x⁻¹ ≠ F.conjBy s⁻¹ := by
  let Y := (S : Subgroup H).map H.subtype
  let C := twoCore H
  obtain ⟨E,hEY,hE,hL,hU,_,_,hCE⟩ := largest_pair_four_structure_of_source
    c hG hempty hgen hb hp hUS
  let := hE
  let : IsElementaryAbelian 2 E := {
    toIsMulCommutative := IsKleinFour.isMulCommutative
    exponent_dvd_p := by rw [IsKleinFour.exponent_two] }
  have hEK : E ≤ K := hEY.trans inf_le_right
  have hCS : C ≤ Y := by
    change twoCore H ≤ Y
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_left
  have hCK : C ≤ centralizer (K : Set G) := by
    change twoCore H ≤ centralizer (K : Set G)
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_right
  have hCKdis : Disjoint K C := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro a ha
    obtain ⟨haK,haC⟩ := ha
    apply mem_bot.mpr
    have hh : (⟨a,haK⟩ : K) ∈ center K :=
      mem_center_iff.mpr (fun k => Subtype.ext (hCK haC k k.property))
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen] at hh
    exact congrArg Subtype.val (mem_bot.mp hh)
  obtain ⟨t,k,ht,_,htC,_,_,_,_,_,_,htH,_⟩ :=
    MathieuSourceSetup.source_central_marks c hG hempty hgen hb
  have hCt : C = zpowers t := (eq_of_le_of_card_ge (zpowers_le.mpr htC) (by
    rw [Nat.card_zpowers,ht,hcard])).symm
  let : IsElementaryAbelian 2 C := by
    rw [hCt]
    exact IsElementaryAbelian.zpowers_of_pow_eq_one (ht ▸ pow_orderOf_eq_one t)
  have hHC : H ≤ centralizer (C : Set G) := by
    rw [hCt,zpowers_eq_closure,centralizer_closure]
    exact htH
  let F := E ⊔ C
  have hFC : IsElementaryAbelian 2 F :=
    IsElementaryAbelian.sup_of_le_centralizer (hCK.trans (centralizer_le hEK))
  let := hFC
  have hFS : F ≤ Y := sup_le (hEY.trans inf_le_left) hCS
  have hFcard : Nat.card F = 8 := by
    rw [show F=E⊔C from rfl,card_sup_eq_mul_of_normalizes_of_disjoint _ _
      ((hCK.trans (centralizer_le hEK)).trans (Subgroup.centralizer_le_normalizer _))
      (hCKdis.mono_left hEK),IsKleinFour.card_four,hcard]
  have hKF : K ⊓ F = E := by
    apply le_antisymm
    · intro a ha
      apply hCE ▸ (show a ∈ K ⊓ centralizer (E : Set G) from ?_)
      exact ⟨ha.1, (F.le_centralizer.trans (centralizer_le (show E≤F from le_sup_left))) ha.2⟩
    · exact le_inf hEK le_sup_left
  have hZF : centerIn Y ≤ F := by
    obtain ⟨hz,_,_,_⟩ := MathieuSourceSetup.normal_component_center_split c hG hempty hgen hb
    rw [hz]
    apply sup_le
    · intro a ha
      apply (show E ≤ F from le_sup_left)
      rw [←hCE]
      exact ⟨ha.2,fun e he => ha.1.2 e (hEY he).1⟩
    · exact inf_le_right.trans le_sup_right
  have hHN : H ≤ normalizer (K : Set G) :=
    (normal_subgroupOf_iff_le_normalizer c.component_le).mp inferInstance
  have hN : H ⊓ normalizer (E : Set G) = H ⊓ normalizer (F : Set G) := by
    apply le_antisymm
    · exact le_inf inf_le_left
        ((le_inf inf_le_right (inf_le_left.trans (hHC.trans (Subgroup.centralizer_le_normalizer _)))).trans
          (normalizer_inf_normalizer_le_normalizer_sup E C))
    · intro a ha
      refine ⟨ha.1,?_⟩
      rw [←hKF]
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [Subgroup.map_inf _ _ _ (MulAut.conj a).injective,
        mem_normalizer_iff_map_conj_eq.mp (hHN ha.1),mem_normalizer_iff_map_conj_eq.mp ha.2]
  have hLF : L = H ⊓ normalizer (F : Set G) := hL.trans hN
  have hUF : U = Y ⊓ normalizer (F : Set G) := by
    rw [hU]
    apply le_antisymm
    · intro a ha
      exact ⟨ha.1,(hN ▸ (show a∈H⊓normalizer (E:Set G) from ⟨map_subtype_le _ ha.1,ha.2⟩)).2⟩
    · intro a ha
      exact ⟨ha.1,(hN.symm ▸ (show a∈H⊓normalizer (F:Set G) from ⟨map_subtype_le _ ha.1,ha.2⟩)).2⟩
  have hLN : L ≤ normalizer (F : Set G) := hLF ▸ inf_le_right
  have hzF : z ∈ F := hZF ⟨c.center_le c.mem_center,by
    obtain ⟨a,ha,he⟩ := c.mem_center
    rw [←he]
    intro b hb
    exact congrArg Subtype.val (mem_center_iff.mp ha ⟨b,c.sylow_lt.le hb⟩)⟩
  refine ⟨E,hEY,hE,hFS,hFC,hFcard,hKF,hZF,hLF,hUF,?_,?_⟩
  · exact largest_pair_normal_two_normalizer_intersection c hG hp hUS
      (IsElementaryAbelian.isPGroup 2 F) hzF hLN
  · intro x hxT hxS s hs
    exact largest_pair_conjugate_ne_of_crossing c hG hp hUS
      (IsElementaryAbelian.isPGroup 2 F) hzF hLN hxT hxS s hs
end CFSG.Quasithin.Chapter2.Section05
