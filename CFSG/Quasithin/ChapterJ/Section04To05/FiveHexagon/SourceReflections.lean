module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SwappedReflection

/-!
# Original-completion pair of marked reflections

The literal completion supplies the involution fusion by short-path
transport. Both wreath reflections, their actual five-normalizers, and the
actor interchanging the marked involutions follow with the same source I.
Source: Aschbacher–Smith, before J.4.8, printed p.443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open Subgroup Centralizers Centralizers.Choices MarkedInverter MarkedNormalizer
variable {K : Type*} [Group K] (q : Completion K)
  {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F) (f : K →* G)
  (hleft : ∀ a : first, f (q.left a) = (e a : G)) (hz : (e modelZ : G) = c.z)
  (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5)
include q f hleft hz hfive

/-- Both actual marked source transvections and their five-normalizers. -/
theorem source_two_transvections :
    ∃ r s : G, r ∈ normalizer (sourceI e : Set G) ∧ s ∈ normalizer (sourceI e : Set G) ∧
      r * c.z * r⁻¹ = c.z ∧ r * sourceU e * r⁻¹ = c.z * sourceU e ∧
      s * sourceU e * s⁻¹ = sourceU e ∧ s * c.z * s⁻¹ = sourceU e * c.z ∧
      r ∈ normalizer (B5Image B5 : Set G) ∧
      s ∈ normalizer (fixedFive B5 (sourceU e) : Set G) :=
  exists_source_two_transvections c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)

/-- A source actor interchanges z and u inside the normalizer of the same I. -/
theorem source_mark_swap :
    ∃ a : G, a ∈ normalizer (sourceI e : Set G) ∧
      a * c.z * a⁻¹ = sourceU e ∧ a * sourceU e * a⁻¹ = c.z :=
  exists_source_mark_swap c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
