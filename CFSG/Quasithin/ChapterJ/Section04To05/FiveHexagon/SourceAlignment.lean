module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.AlignedPair
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.PathTransport

/-!
# Original-completion pair alignment

Short-path transport in the original compatible completion supplies the
needed fusion, so its simultaneous pair conjugator can be chosen in the
normalizer of the very same marked I. The original ambient map and both
endpoint markings are retained; no smallness or recognition is used.
Source: Aschbacher–Smith, before J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer

/-- The actual source pair conjugator preserves the same marked torus. -/
theorem source_pair_alignment {K : Type*} [Group K] (q : Completion K)
    {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
    (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    {F : Subgroup G} (e : first ≃* F) (f : K →* G)
    (hleft : ∀ a : first, f (q.left a) = (e a : G)) (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ g : G, g * sourceU e * g⁻¹ = c.z ∧
      (fixedFive B5 (sourceU e)).conjBy g = B5Image B5 ∧
      (sourceI e).conjBy g = sourceI e :=
  source_pair_conjugacy_preserving_I c B5 e hz hfive
    (PathTransport.source_fusion q c e f hleft hz)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
