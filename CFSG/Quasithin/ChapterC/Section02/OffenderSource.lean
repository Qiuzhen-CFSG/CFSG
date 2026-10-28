module
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.ElementaryThompsonFrattini

/-!
# The offender forced by characteristic-normalizer control

Let V be a normal elementary subgroup with centralizer O₂(G), and let the
nontrivial two-subgroup R contain that core. If C(G,R) lies in a proper
subgroup, then J(R) cannot centralize V: the centralizing branch of B.2.10
would make its nontrivial characteristic Thompson subgroup normal in G.
The maximum-elementary replacement argument consequently supplies an FF
module and a best offender inside the actual quotient image of R.

Source: Aschbacher--Smith, B.2.7--10 and C.2.7(2), printed pp.75--77,145--146.
-/

public section
open Subgroup Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

theorem offender_of_characteristic_control
    (V R M : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (hR : IsPGroup 2 R) (hne : R ≠ ⊥) (hQR : pCore 2 G ≤ R)
    (hVQ : V ≤ pCore 2 G) (hCV : centralizer (V : Set G) = pCore 2 G)
    (hcontrol : R.characteristicNormalizerClosure ≤ M) (hM : M ≠ ⊤)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G)) :
    ¬ elementaryAbelianMaxJ R ≤ elementaryAbelianMaxJ (pCore 2 G) ∧
    IsFFModule (NormalElementaryQuotient.representation V q hq hker) ∧
    ∃ E : Subgroup H, E ≤ R.map q ∧
      IsBestOffender (NormalElementaryQuotient.representation V q hq hker) E := by
  have hJR : elementaryAbelianMaxJ R ≤ R := sSup_le fun _ hA => hA.1
  have hJN : normalizer (elementaryAbelianMaxJ R : Set G) ≤ M :=
    (normalizer_maxJ_le_characteristicNormalizerClosure R R hJR le_rfl
      (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hR hne)).trans hcontrol
  have hnoncentral : ¬ elementaryAbelianMaxJ R ≤ centralizer (V : Set G) := by
    intro hJ
    have hcore : pCore 2 G = R ⊓ centralizer (V : Set G) := by
      rw [hCV, inf_eq_right.mpr hQR]
    have hn := (ChapterB.lemma_B_2_10_centralizing V R (hVQ.trans hQR) hQR
      hcore (by simpa only [ChapterB.thompsonJ_zero] using hJ)).2.2.1
    have hjn : (elementaryAbelianMaxJ R).Normal := by
      simpa only [ChapterB.thompsonJ_zero] using hn
    rw [normalizer_eq_top_iff.mpr hjn] at hJN
    exact hM (top_unique hJN)
  have hjker : ¬ elementaryAbelianMaxJ R ≤ q.ker := hker ▸ hnoncentral
  obtain ⟨hff, hbest⟩ := ChapterB.lemma_B_2_7_local V q hq hker R
    (hVQ.trans hQR) hjker
  have hmax : ∃ A ∈ elementaryAbelianMaxSubgroups R, A.map q ≠ ⊥ := by
    by_contra! hall
    apply hjker
    exact sSup_le fun A hA => (map_eq_bot_iff A).mp (hall A hA)
  obtain ⟨A,hA,hAq⟩ := hmax
  refine ⟨?_,hff,A.map q,map_mono hA.1,hbest _ ⟨A,hA,rfl,hAq⟩⟩
  intro hJ
  apply hnoncentral
  exact (hJ.trans (sSup_le fun _ hB => hB.1)).trans hCV.ge

end CFSG.Quasithin.ChapterC

