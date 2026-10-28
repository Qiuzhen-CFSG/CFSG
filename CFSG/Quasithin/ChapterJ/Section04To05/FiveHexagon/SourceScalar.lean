module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.Scalar
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.PathTransport

/-!
# Original-completion scalar for the opposite five-pair

The genuine earlier compatible endpoint completion supplies fusion of its
literal marked involution by the proved short-path transport. Applying the
faithful prime-plane action then gives the cyclic four in the same original
I, centralizing the actual opposite SL₂(5). No smallness or recognition of
the generated completion is used.

Source: Aschbacher–Smith, discussion before J.4.8, printed p.443.
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
  (hleft : ∀ a : first, f (q.left a) = (e a : G))
  (hz : (e modelZ : G) = c.z)
  (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5)

include q f hleft hz hfive

/-- The literal completion constructs the scalar; its ambient fusion premise
is discharged by the same marked short path. -/
theorem source_scalar_four :
    ∃ i : G, i ∈ sourceI e ∧ orderOf i = 4 ∧ i ^ 2 = c.z * sourceU e ∧
      i ∈ centralizer (oppositePair c B5 (sourceU e) : Set G) ∧
      ∀ x ∈ edge B5 (sourceU e), i * x * i⁻¹ = x ^ 2 :=
  exists_source_scalar_four c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)

/-- The source cyclic four is a subgroup of the original I, with its generator,
marked square and centralization of the original opposite pair retained. -/
theorem source_scalar_subgroup :
    ∃ (C : Subgroup G) (i : G), C = zpowers i ∧ Nat.card C = 4 ∧
      C ≤ sourceI e ∧ C ≤ centralizer (oppositePair c B5 (sourceU e) : Set G) ∧
      i ^ 2 = c.z * sourceU e := by
  obtain ⟨i,hi,horder,hsq,hcentral,_⟩ := source_scalar_four q c B5 e f hleft hz hfive
  exact ⟨zpowers i,i,rfl,(Nat.card_zpowers i).trans horder,
    zpowers_le.mpr hi,zpowers_le.mpr hcentral,hsq⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
