module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Stellmacher.SectionTwo.NormalSupplementBaumannSetup
public import CFSG.Quasithin.ChapterB.Section06To07.Structure.CoreOdd
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents

/-!
# Baumann Sylow transfer from a normal supplement

In a solvable minimal parabolic, let R be a Sylow subgroup of O²(G)R,
normalized by the original Sylow T and containing Ω₁Z(T). Stellmacher's
normal-supplement theorem makes Baum(R) Sylow in its full normal closure.
If that closure lies in the minimal-parabolic core, Baum(R) lies in O₂(G),
so its normal closure is a two-group and equals Baum(R). Thompson heredity
would then make J(R) normal. Thus failure of residual normalization forces
the closure to contain O²(G), and restriction gives the required Sylow.

The omega-orbit core equality is retained explicitly. The original 13.2.13
application discharges it from the proved original 13.2.9 kernel equality.
Source: Stellmacher, Journal of Algebra 190 (1997), (2.3), pp.20,26;
Aschbacher--Smith B.6.8 and13.2.13, printed pp.113--115,883.
-/

public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.ChapterB.RankOneBaumann
variable {G : Type*} [Group G] [Finite G]

/-- Transfer to the Baumann subgroup without requiring the smaller supplement
to be minimal parabolic. -/
theorem normal_supplement_baumann_sylow
    (h : Stellmacher.SectionTwo.Hypotheses G) (T : Sylow 2 G)
    (hp : IsMinimalParabolicOver T ⊤) (R : Subgroup G)
    (hRT : R ≤ (T : Subgroup G)) (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hZR : omegaOneCenterAmbient (T : Subgroup G) ≤ R)
    (hn : ¬ pResidual 2 G ≤ normalizer (elementaryAbelianMaxJ R : Set G))
    (hs : Chapter1.IsSylowIn 2 R (pResidual 2 G ⊔ R))
    (hc : pCore 2 G = (T : Subgroup G) ⊓
      centralizer (Stellmacher.SectionTwo.vSubgroup T : Set G)) :
    Chapter1.IsSylowIn 2 (baumann R) (pResidual 2 G ⊔ baumann R) := by
  let K := pResidual 2 G ⊔ R
  have hKn : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←pResidual_sup_sylow_eq_top T]
    apply sup_le (le_sup_left.trans K.le_normalizer)
    exact (le_inf le_normalizer_of_normal hTR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let := hKn
  have hgen : K ⊔ (T : Subgroup G) = ⊤ := by
    rw [show K = pResidual 2 G ⊔ R from rfl,sup_assoc,sup_eq_right.mpr hRT,
      pResidual_sup_sylow_eq_top T]
  obtain ⟨S,hS⟩ := hs
  have hSne : (S : Subgroup K) ≠ ⊥ := by
    intro he
    have hr : R = ⊥ := by rw [←hS,he,Subgroup.map_bot]
    have hj : elementaryAbelianMaxJ R = ⊥ := bot_unique
      ((sSup_le fun _ ha => ha.1).trans_eq hr)
    apply hn
    rw [hj]
    exact le_normalizer_of_normal
  have hb := (Stellmacher.SectionTwo.normal_supplement_baumann_setup h T K S hgen
    (hS ▸ hRT) (hS ▸ hTR) (hS ▸ hZR) hSne hc).2
  change Chapter1.IsSylowIn 2
    ((S : Subgroup K).map K.subtype ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ ((S : Subgroup K).map K.subtype)) : Set G))
    (normalClosure (((S : Subgroup K).map K.subtype ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ ((S : Subgroup K).map K.subtype)) : Set G)) : Set G)) at hb
  rw [hS] at hb
  change Chapter1.IsSylowIn 2 (baumann R) (normalClosure (baumann R : Set G)) at hb
  let B := baumann R
  let N := normalClosure (B : Set G)
  have hBN : B ≤ N := le_normalClosure
  have hNres : pResidual 2 G ≤ N := by
    rcases minimalParabolic_normal_subgroup_residual_dichotomy T hp N with he | he
    · have hBQ : B ≤ pCore 2 G := by
        rw [←minimalParabolic_sylow_inf_core T hp]
        exact le_inf (inf_le_left.trans hRT) (hBN.trans he)
      have hNQ : N ≤ pCore 2 G := normalClosure_le_normal hBQ
      obtain ⟨P,hP⟩ := hb
      have ht : (P : Subgroup N) = ⊤ :=
        (P.is_maximal' (((pCore_isPGroup (p := 2) (G := G)).to_le hNQ).to_subgroup ⊤) le_top).symm
      have hBN' : B = N := by
        rw [ht,←MonoidHom.range_eq_map,range_subtype] at hP
        exact hP.symm
      have hJB : elementaryAbelianMaxJ B = elementaryAbelianMaxJ R := by
        have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq B R inf_le_left
        have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le R B
          (elementaryAbelianMaxJ_le_baumann R)
        have horder := le_antisymm hsmall.1 hlarge.1
        exact le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
      apply (hn ?_).elim
      rw [←hJB,hBN']
      exact (le_normalizer_of_normal (H := N)).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ N)
    · exact he
  exact Chapter1.IsSylowIn.restrict hb le_sup_right (sup_le hNres hBN)

end CFSG.Quasithin.ChapterB.RankOneBaumann
