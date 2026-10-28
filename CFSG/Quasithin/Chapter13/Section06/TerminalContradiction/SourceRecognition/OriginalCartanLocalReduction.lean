module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523CartanEscape
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.Baumann
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNoncentralExclusion
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryMaximal

/-!
# Original local Cartan escape inside the singular centralizer

The intrinsic local source leaves the exceptional conclusion or a binary
triality container. In the latter case the same containing component is
normal in the whole original singular centralizer: its proven local
maximality applies because it centralizes the original Sylow omega-center,
which contains the marked line. The actual residual, full Sylow and
quotient model are retained.

This is a reduction of the original terminal source. The binary container
is not excluded here, and no initial exceptional candidate is asserted.
Source: Aschbacher--Smith 5.1.12--13 and 13.6.27, pp.635--638,934--935.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Section05.A5Source CentralizerReduction
open Components.SuzukiIsolation Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H A B Y : Subgroup G}

/-- Local Cartan escape in the original Context gives either the genuine
5.2.3 local alternative or an actual normal triality component of C_G(V₁). -/
theorem original_local_cartan_exceptional_or_binary_point_component
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    Source523.LocalAlternative T L H V 2 ∨
      ∃ X : Subgroup G,
        residual H ≤ X ∧ X ≤ omegaCentralizer T ∧
        X ∈ Chapter1.LStar G (T : Subgroup G) ∧
        (X.subgroupOf (centralizer (V₁ : Set G))).IsCComponent ∧
        (X.subgroupOf (centralizer (V₁ : Set G))).Normal ∧
        Triality.Standard.IsTrialityGroupAt 2 (X ⧸ pCore 2 X) := by
  have h := Section02.A5Outside.OriginalCentralization.rankOne_input_of_many d hmany
  rcases localCartan_escape_binary_or_exceptional h hH hgen c hY hescape with he |
      ⟨K,hKH,_,_,hKT,hKL,hR,C,hC,_,hKC,_,_,_,_,hKR,hbin⟩
  · exact Or.inl (source523_local_of_cartan_conclusion d he.2)
  · obtain ⟨_,_,hm,_⟩ := hbin
    have hs := BinaryOmega.original_binary_triality_omega_normalizers
      h hH hgen c hKH hKL hKT hR hY hescape C hC hKC hm
    have hmax := BinaryOmega.original_binary_triality_maximal
      h hH hgen c hKH hKL hKT hR hY hescape C hC hKC hm
    have hV₁ : V₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := by
      rw [←d.flag.flag.line_eq]
      exact zpowers_le.mpr d.flag.flag.z_central
    have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
      d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two _ d.flag.one_card)
    have hVC : V₁ ≤ (centralizer (V₁ : Set G)).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (T.isPGroup'.to_le
        (d.flag.one_le_two.trans (d.flag.two_le_V.trans d.flag.V_le_T)))
        ((d.flag.one_le_two.trans (d.flag.two_le_V.trans d.flag.V_le_T)).trans hTC)
        (Subgroup.centralizer_le_normalizer _)
    have hpoint : centralizer (V₁ : Set G) ∈ Chapter1.H G := by
      intro hz
      have he : V₁ = ⊥ := bot_unique (hVC.trans_eq hz)
      have hc := d.flag.one_card
      simp only [he,card_bot] at hc
      contradiction
    have hXC : C.map Y.subtype ≤ centralizer (V₁ : Set G) :=
      hs.2.1.trans (centralizer_le hV₁)
    have hpointOver : centralizer (V₁ : Set G) ∈ Chapter1.HOver G
        ((C.map Y.subtype ⊔ (T : Subgroup G) : Subgroup G) : Set G) :=
      ⟨hpoint,sup_le hXC hTC⟩
    obtain ⟨hcomp,hnorm,_⟩ :=
      (BinaryOmega.original_binary_triality_overgroup_control
        h hH hgen c hKH hKL hKT hR hY hescape C hC hKC hm).2 _ hpointOver
    exact Or.inr ⟨C.map Y.subtype,hs.1,hs.2.1,hmax,hcomp,hnorm,hs.2.2.2.2.1⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
