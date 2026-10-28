module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.Setup
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# The source normality reduction for the triality branch

The nontrivial elementary subgroup U lies in O₂(C_G(U)), so its centralizer
belongs to the source family H. Apply the universal 1.2.1(3) statement there
to the ordinary component, viewed as a C-component. Its alternative is either
relative normality or one of the four specified two-core quotient models.
A genuine exclusion of those models therefore makes Q normalize L.

The model exclusion is an explicit premise here and remains a separate
triality calculation. The source input retains the full normalizer-index-two
clause (equivalently, two conjugates), not merely a normality conclusion.
The local extension lemma supplies inherited quasisimplicity and the actual
Sylow embedding for the independent parabolic calculations.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 1.2.1(3),
printed p.504 (PDF p.521), applied in E.6.8, printed p.247 (PDF p.258).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
open Chapter1.Section02

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U Q L : Subgroup G}

/-- The exact source component alternative plus a model separation gives
normalization by Q; all normality is relative to C_G(U). -/
theorem normalizes_of_source_1_2_1 (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (source : ∀ H : Subgroup G, H ∈ Chapter1.H G → ∀ B : Subgroup H,
      B.IsCComponent → B.Normal ∨ (normalizer (B : Set H)).index = 2 ∧
        NonnormalCComponentModel (B ⧸ pCore 2 B))
    (hnot : ¬ NonnormalCComponentModel (L ⧸ pCore 2 L)) :
    Q ≤ normalizer (L : Set G) := by
  let _ := h.elementary
  have hUH : U ≤ centralizer (U : Set G) :=
    hU.1.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU.1))
  have hcore : U ≤ (centralizer (U : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1)
      hUH (Subgroup.centralizer_le_normalizer _)
  have hH : centralizer (U : Set G) ∈ Chapter1.H G :=
    fun he => hU.2.1 (le_bot_iff.mp (he ▸ hcore))
  rcases source _ hH _ hL.2.isCComponent with hn | ⟨_, hm⟩
  · have hQH : Q ≤ centralizer (U : Set G) := by
      rw [hQ]
      exact inf_le_right.trans (Subgroup.centralizer_le hU.1)
    exact hQH.trans ((normal_subgroupOf_iff_le_normalizer hL.1).mp hn)
  · let e := subgroupOfEquivOfLe hL.1
    let eqv := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    exact False.elim (hnot (hm.of_mulEquiv eqv.symm))

/-- The component supplies quasisimplicity and Q is Sylow in the actual LQ. -/
theorem local_extension_context (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (hN : Q ≤ normalizer (L : Set G)) :
    IsQuasisimple L ∧ ∃ S : Sylow 2 ↥(L ⊔ Q),
      (S : Subgroup ↥(L ⊔ Q)).map (L ⊔ Q).subtype = Q := by
  refine ⟨IsComponentIn.quasisimple hL, ?_⟩
  rw [← componentExtension_eq hN]
  exact extension_sylow h hU hL hQ hN

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
