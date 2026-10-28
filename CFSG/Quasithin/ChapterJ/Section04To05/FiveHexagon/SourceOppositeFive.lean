module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.TwoSourceFives

/-!
# The original-completion opposite five

The genuine compatible completion gives fusion through its marked short
path. Its original torus then selects exactly two five-subgroups in the
constructed SL₂(5), including the original B₅ and its unique opposite.
Source: Aschbacher–Smith, discussion before J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer

/-- Construct the exact opposite five and its intrinsic uniqueness inside
the original SL₂(5), retaining all marked ambient subgroups. -/
theorem source_opposite_five {D : Type*} [Group D] (q : Completion D)
    {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : D →* G)
    (hleft : ∀ a : first, f (q.left a) = (e a : G)) (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ K B' : Subgroup G, B5Image B5 ≤ K ∧ sourceI e ≤ normalizer (K : Set G) ∧
      K ≤ centralizer (sourceIz e : Set G) ∧
      Nonempty (K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
      Nat.card B' = 5 ∧ B' ≠ B5Image B5 ∧ sourceI e ≤ normalizer (B' : Set G) ∧
      K = B5Image B5 ⊔ B' ∧
      ∀ C : Subgroup G, C ≤ K → Nat.card C = 5 → sourceI e ≤ normalizer (C : Set G) →
        C = B5Image B5 ∨ C = B' :=
  exists_source_opposite_five c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
