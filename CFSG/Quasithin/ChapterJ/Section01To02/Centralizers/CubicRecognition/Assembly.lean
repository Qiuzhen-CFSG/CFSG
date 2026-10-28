module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.TripleCover

/-!
# The two cubic stages of J.2.7

The first stage uses the marked local J.2.5 data, J.2.6 fusion, and exactly
I.4.1(2) to prove the literal M₁₀ quotient and ambient involution fusion.
The second stage, available separately in `TripleCover`, takes the later
Aut(A₆) marking and transposition clause (7), constructs the cubic Sylow,
and identifies the perfect residual with the marked hexacode triple cover.

The combined theorem records clauses (1),(2),(9),(11). The source owners
must still supply the earlier local witnesses and I.4.1, and the centralizer
assembly must construct clauses (3),(7). Neither stage assumes the output
of the other through a cyclic source dependency.

Source: Aschbacher–Smith, J.2.7, printed pp.435–437 (PDF pp.446–448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
universe u
open Subgroup
variable {G : Type u} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The opening cubic stage, before the normalizer marking is constructed. -/
theorem cubic_quotient_and_involution_fusion
    (hI : SemidihedralRecognition.DihedralEightRecognition.{u})
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b) :
    (∃ e : c.CubicQuotient ≃* AlternatingSix.M10.extension,
      (pResidual 2 c.CubicQuotient).map e.toMonoidHom =
        AlternatingSix.ShadowLocal.inner.subgroupOf AlternatingSix.M10.extension) ∧
    ∀ i : G, i ∈ c.GB → orderOf i = 2 → IsConj i c.z :=
  ⟨c.quotient_marked_M10_recognition hI hB t h25 h26 b hb hcontrol,
    t.involutions_GB_fused h26⟩

/-- The four cubic clauses of J.2.7, conditional on the precise earlier
source witnesses and the intervening normalizer/fusion geometry. -/
theorem cubic_source_clauses
    (hI : SemidihedralRecognition.DihedralEightRecognition.{u})
    (hB : Nat.card c.B = 3) (t : CubicLocalTwo c)
    (h25 : Fusion.SourceJ25 d.toTypeRuSetup c.sylowThree)
    (h26 : Fusion.SourceJ26 d.toTypeRuSetup c.z)
    (b : G) (hb : c.B = zpowers b)
    (hcontrol : ∀ x : G, x ∈ d.toTypeRuSetup.H → IsConj b x →
      ∃ h : d.toTypeRuSetup.H, (h : G) * x * (h : G)⁻¹ = b)
    (P : Sylow 3 d.toTypeRuSetup.H)
    (hP : (P : Subgroup d.toTypeRuSetup.H).map d.toTypeRuSetup.H.subtype = c.B)
    (e : c.NormalizerQuotient ≃* MulAut (alternatingGroup (Fin 6)))
    (hM : c.centralizerImage.map e.toMonoidHom = AlternatingSix.M10.extension)
    (h7 : CubicSylow.TranspositionFusion c e) :
    Nonempty (c.LB ≃* Atlas.Codes.HexEvenAutomorphisms) ∧
    Nonempty (c.CubicQuotient ≃* AlternatingSix.M10.extension) ∧
    (∀ i : G, i ∈ c.GB → orderOf i = 2 → IsConj i c.z) ∧
    ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g * x * g⁻¹ = y := by
  obtain ⟨_, ⟨a, _, _⟩, S, _, _, _, _, _, hfusion⟩ :=
    c.triple_cover_and_order_three_fusion hB P hP t.z_order e hM h7
  exact ⟨⟨a⟩, c.quotient_M10_recognition hI hB t h25 h26 b hb hcontrol,
    t.involutions_GB_fused h26, hfusion⟩

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
