module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsOriginalOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientFourHyperplaneSource

/-!
# The original Tits two-core cannot meet the Hermitian module in a hyperplane

If O₂(KT) lies in the original O₂(LT), the intersection of that core with
R₂(LT)=Ω₁Z(O₂(LT)) lies in its own omega-center. The actual Tits component
centralizes this intersection. The original global hyperplane centralizer
bound then forces the intersection to have binary corank at least two.

Source: Aschbacher--Smith 6.1.4, printed pp.665--666, with E.6.13.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
attribute [local instance] Representation.SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric ChapterE
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K : Subgroup G} {n : ℕ}

/-- An original Tits two-core contained in O₂(LT) has intersection of
corank at least two with the full original Hermitian module. -/
theorem original_hermitian_tits_core_intersection_corank
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (Representation.SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup)
    (hRQ : (K ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    2 ≤ subgroupCorank (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (reducedSubgroup (L ⊔ (T : Subgroup G)) ⊓ (K ⊔ (T : Subgroup G)).pCoreIn 2) := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let R := (K ⊔ (T : Subgroup G)).pCoreIn 2
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hBR : B ⊓ R ≤ omegaOneCenterAmbient R := by
    intro b hb
    have hbB : b ∈ omegaOneCenterAmbient Q := h.reduced_enlargement_eq_omega_core ▸ hb.1
    obtain ⟨_,hb2,hbc⟩ := (mem_omegaOneCenterAmbient_iff Q b).mp hbB
    exact (mem_omegaOneCenterAmbient_iff R b).mpr
      ⟨hb.2,hb2,(centralizer_le hRQ) hbc⟩
  have hKC : K ≤ centralizer (B ⊓ R : Set G) := by
    have hc := original_hermitian_tits_component_centralizes_omega
      h hout hm hM₁ hCM₁ hK hnot hq e
    rw [commutator_comm] at hc
    exact (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le hBR)
  have hr := full_reduced_hermitian_one_lt_globalR h hout hm (by decide : 1 < 2)
  have hE := full_reduced_hermitian_hypothesisE61 h hm
  change 2 ≤ subgroupCorank B (B ⊓ R)
  by_contra! hh
  have hsmall : (subgroupCorank B (B ⊓ R) : ℕ∞) < globalR B :=
    lt_of_le_of_lt (by exact_mod_cast (show subgroupCorank B (B ⊓ R) ≤ 1 by omega)) hr
  exact hnot (hKC.trans ((centralizer_le_normalizer_of_corank_lt_globalR inf_le_left hsmall).trans
    hE.normalizer_le))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
