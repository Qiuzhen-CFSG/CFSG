module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.BaseOpposite

/-!
# Original-completion input to the Iz-centralizer argument

The actual source completion supplies the marked involution fusion; all
opposite-SL₂ placement and scalar data are then constructed in the original
ambient group, with exactly the original B₅, I and Iz.
Source: Aschbacher–Smith, before J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer

/-- Actual source K≤C_G(Iz), its original five-subgroup, normalizing torus,
and specified cyclic-four generator, with no extra fusion premise. -/
theorem source_base_opposite {D : Type*} [Group D] (q : Completion D)
    {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : D →* G)
    (hleft : ∀ a : first, f (q.left a) = (e a : G)) (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ (K : Subgroup G) (s : G), K = (oppositePair c B5 (sourceU e)).conjBy s ∧
      s ∈ normalizer (sourceI e : Set G) ∧
      s * sourceU e * s⁻¹ = sourceU e ∧ s * c.z * s⁻¹ = sourceU e * c.z ∧
      B5Image B5 ≤ K ∧ sourceI e ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (sourceIz e : Set G) ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      ∃ i : G, sourceIz e = zpowers i ∧ orderOf i = 4 ∧ i ^ 2 = c.z :=
  exists_source_base_opposite c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
