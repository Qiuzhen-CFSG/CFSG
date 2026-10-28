module

public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.Assembly
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.CubicRecognition.SemidihedralRecognition.EightSource

/-!
# Applying the proved D8 recognition in the cubic assembly

The exact I.4.1(2) theorem discharges the recognition input in the two-stage
cubic proof. The literal M₁₀ quotient, triple cover, involution fusion and
single cubic class now depend only on earlier J.2.5–6 witnesses and the
intervening J.2.7 normalizer marking and transposition fusion. Constructing
those intervening clauses remains with the centralizer assembly.

The quotient cardinality also fixes |C_G(B)| = 2160 before identifying
the triple cover; in particular its five-subgroups have order at most five.

Source: Aschbacher–Smith, J.2.7, printed pp.435–437 (PDF pp.446–448).
-/

public section
namespace CFSG.Quasithin.ChapterJ.Centralizers.Choices
universe u
open Subgroup
variable {G : Type u} [Group G] [Finite G] {d : LocalSetup G} (c : Choices d)

/-- The centralizer order follows from the genuine cubic kernel and M₁₀ quotient. -/
theorem GB_card_of_M10 (hB : Nat.card c.B = 3)
    (e : c.CubicQuotient ≃* AlternatingSix.M10.extension) : Nat.card c.GB = 2160 := by
  rw [card_eq_card_quotient_mul_card_subgroup c.cubicKernel, c.cubicKernel_card hB,
    Nat.card_congr e.toEquiv, AlternatingSix.M10.Action.card_extension]

/-- The four cubic clauses with exact I.4.1(2) supplied by its proved source theorem. -/
theorem cubic_source_clauses_of_source
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
    ∀ x y : G, orderOf x = 3 → orderOf y = 3 → ∃ g : G, g * x * g⁻¹ = y :=
  c.cubic_source_clauses SemidihedralRecognition.dihedralEightRecognition_source
    hB t h25 h26 b hb hcontrol P hP e hM h7

end CFSG.Quasithin.ChapterJ.Centralizers.Choices
