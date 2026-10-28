module

public import Theory.SpecificGroups.SymmetricFive.SquareNormalizer
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.DiagonalCentralizer.Quotient

/-!
# The original inverter selects two quotient pentagons

The marked first endpoint supplies its actual order-four actor t in I,
with t squared equal to u and quotient image of order four. The lower
square-normalizer theorem therefore identifies its pentagons with those
of u, and the existing involution count gives exactly two. The original
H-to-S5 quotient map and the selected actor are retained throughout.

Source: Aschbacher--Smith, the E(z) paragraph before J.4.8, printed p.443.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
open Centralizers Centralizers.Choices MarkedInverter DiagonalCentralizer
open Tits.ExceptionalParabolics.FullRee
open Theory.SpecificGroups.SymmetricFive.SquareNormalizer
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
  (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
  {F : Subgroup G} (e : first ≃* F)

/-- The same original order-four actor and its square determine precisely
 two pentagons in the actual Ru2 quotient. -/
theorem source_quotient_pentagons
    (hz : (e modelZ:G)=c.z)
    (hfive : (zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    ∃ t : d.toTypeRuSetup.H, (t:G)∈sourceI e ∧ (t:G)^2=sourceU e ∧
      orderOf (d.ru2.quotientMap t)=4 ∧
      (∀ P:Subgroup S5,Nat.card P=5 →
        (d.ru2.quotientMap (t^2)∈normalizer (P:Set S5) ↔
        d.ru2.quotientMap t∈normalizer (P:Set S5))) ∧
      Nat.card {P:Sylow 5 S5 //
        d.ru2.quotientMap (t^2)∈normalizer ((P:Subgroup S5):Set S5)}=2 := by
  obtain ⟨t,ht,ht2,ho,_⟩ := exists_order_four_image c B5 e hz hfive
  refine ⟨t,ht,ht2,ho,?_,?_⟩
  · intro P hP
    rw [map_pow]
    exact normalizer_square_iff P hP _ ho
  · rw [map_pow]
    exact sylow_square_normalizer_count _ ho

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedNormalizer
