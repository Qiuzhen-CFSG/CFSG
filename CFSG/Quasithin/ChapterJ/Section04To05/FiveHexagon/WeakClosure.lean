module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedComplement
public import Theory.GroupTheory.CyclicFourWreathWeakClosure

/-!
# Weak closure of the original marked torus in its source complement

The earlier source construction extends the literal transported I to a
cyclic-four wreath complement R. Its abelian sixteen is unique, so every
ambient conjugate of I that lies in R is I. This is the weak-closure step
needed to align the exchanged source pairs without changing the original I.
No compatibility or weak-closure premise is added to the source factory.

Source: Aschbacher–Smith, paragraph before J.4.8, printed pp.442–443.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Subgroup Centralizers Centralizers.Choices MarkedInverter
open Tits.ExceptionalParabolics.FullRee
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- Every conjugate of the same marked I contained in a source wreath
complement is exactly I. -/
theorem sourceI_weakly_closed_in_complement (R : Subgroup G) (hIR : sourceI e ≤ R)
    (hR : Nonempty (R ≃* RegularWreathProduct (Multiplicative (ZMod 4))
      (Multiplicative (ZMod 2)))) (g : G) (hg : (sourceI e).conjBy g ≤ R) :
    (sourceI e).conjBy g = sourceI e := by
  obtain ⟨eR⟩ := hR
  obtain ⟨eI⟩ := sourceI_equiv e
  apply CyclicFourWreathTwo.abelian_sixteen_weakly_closed (sourceI e) R hIR eR
    (sourceI_card e) _ g hg
  intro x hx y hy
  have he : (⟨x,hx⟩:sourceI e)*⟨y,hy⟩=⟨y,hy⟩*(⟨x,hx⟩:sourceI e) := by
    apply eI.injective
    rw [map_mul,map_mul,mul_comm]
  exact congrArg Subtype.val he

/-- The original source supplies the complement and its weak closure
simultaneously, with its actual normalizer and central involution. -/
theorem exists_source_weakly_closed_complement
    (hz : (e modelZ : G) = c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom) = B5Image B5) :
    ∃ R : Subgroup G, sourceI e ≤ R ∧ R ≤ d.toTypeRuSetup.H ∧
      R ≤ normalizer (B5Image B5 : Set G) ∧ Nat.card R = 32 ∧ CQ B5 ≤ R ∧
      Disjoint (fiveOddPart B5) R ∧
      normalizer (B5Image B5 : Set G) = fiveOddPart B5 ⊔ R ∧
      Nonempty (R ≃* RegularWreathProduct (Multiplicative (ZMod 4)) (Multiplicative (ZMod 2))) ∧
      c.z ∈ (center R).map R.subtype ∧
      ∀ g : G, (sourceI e).conjBy g ≤ R → (sourceI e).conjBy g = sourceI e := by
  obtain ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,he,hzR⟩ :=
    exists_source_complement c B5 e hz hfive
  exact ⟨R,hIR,hRH,hRN,hR32,hCQ,hd,hgen,he,hzR,
    fun g hg => sourceI_weakly_closed_in_complement e R hIR he g hg⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
