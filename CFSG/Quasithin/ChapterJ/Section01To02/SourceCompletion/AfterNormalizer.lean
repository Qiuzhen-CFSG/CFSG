module

public import CFSG.Quasithin.ChapterJ.Section01To02.SourceCompletion.Cubic
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.LocalSource
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.OddPrimeCompletion

/-!
# The source consumers of the normalizer-fusion argument

The independent J.2.7 normalizer argument supplies its marked Aut(A6)
quotient and transposition fusion. Every earlier cubic and Sylow premise
is discharged here from Ru1/Ru2, yielding the actual triple cover and ambient
Sylow-three subgroup. Likewise H-control of s-fusion promotes the original
T_s to Sylow in C_G(s); the diagonal-involution small-model embedding then
supplies the already proved Suzuki recognition argument.

The normalizer marking and fusion hypotheses are precisely the intervening
source conclusions whose producer is developed independently. No triple-cover,
ambient Sylow, or Suzuki conclusion is an input to these two consumers.

Source: Aschbacher–Smith, J.2.7(1),(11) and J.2.9, printed pp.437–438.
-/

public section
namespace CFSG.Quasithin.ChapterJ.SourceCompletion
open Subgroup Centralizers
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The triple cover and ambient cubic Sylow on the original marked kernel. -/
theorem cubic_after_normalizer
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (h7 : CubicSylow.TranspositionFusion c e) :
    c.B ≤ c.LB ∧
    (∃ a : c.LB ≃* Atlas.Codes.HexEvenAutomorphisms,
      Atlas.Codes.hexEvenCoordinate.comp a.toMonoidHom = c.residualA6Map e hM ∧
      (c.B.subgroupOf c.LB).map a.toMonoidHom = Atlas.Codes.hexEvenCoordinate.ker) ∧
    ∃ S : Sylow 3 G, Nat.card S = 27 ∧ IsExtraspecial 3 S ∧ Monoid.exponent S = 3 ∧
      (center S).map (S : Subgroup G).subtype = c.B ∧
      (_root_.commutator S).map (S : Subgroup G).subtype = c.B ∧
      ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g*x*g⁻¹ = y := by
  obtain ⟨P, hP⟩ := source_sylowThree_H c
  exact c.triple_cover_and_order_three_fusion (B_card c) P hP (z_order c) e hM h7

/-- The source Suzuki conclusion, with the original Sylow and local-centralizer
premises constructed from genuine earlier source results. -/
theorem suzuki_after_fusion
    (hsfusion : ∀ t ∈ d.toTypeRuSetup.H, IsConj c.s t →
      ∃ h ∈ d.toTypeRuSetup.H, h*c.s*h⁻¹ = t)
    {t : G} (hst : IsConj c.s t)
    (f : Multiplicative (ZMod 2) × BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 →*
      centralizer ({t} : Set G)) (hf : Function.Injective f)
    (hzfusion : ∀ u : Multiplicative (ZMod 2) × BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0,
      u.1 = 1 → orderOf u = 2 → IsConj c.z (f u : G)) :
    Nonempty c.SuzukiSourceConclusion := by
  obtain ⟨P, hP⟩ := c.Ts_sylow_of_H_fusion (H_inf_Gs_eq_Ts c) hsfusion
  exact c.suzuki_recognition_of_J27 P hP (H_inf_Gs_eq_Ts c) hsfusion hst f hf hzfusion

end CFSG.Quasithin.ChapterJ.SourceCompletion
