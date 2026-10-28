module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SourceOppositeFive

/-!
# The fixed-five labels of the original base neighbors

Any order-five subgroup commuting with B5 lies in the actual O5 of its
centralizer. Intersecting with C(z), C(u), or C(zu) leaves the corresponding
order-five fixed subgroup. Thus the base label of a possible parabolic
neighbor is forced. The completion supplies the inverter and its fusion,
so the source consumer retains no extra fixed-group or core premise.

Source: the adjacency argument for J.4.10, printed p.444. This formulation
uses the actual parabolic labels and does not assert closure of a chosen
six-subgroup set under the wreath reflections.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
open Centralizers Centralizers.Choices
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)

/-- A commuting five in one of the three involution centralizers is the
corresponding fixed subgroup of the actual extraspecial five-core. -/
theorem commuting_five_eq_fixed (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H) (v:G) (hv:Nat.card (fixedFive B5 v)=5)
    (A:Subgroup G) (hA:Nat.card A=5) (hc:A≤centralizer (B5Image B5:Set G))
    (hvc:A≤centralizer ({v}:Set G)) : A=fixedFive B5 v := by
  exact eq_of_le_of_card_ge (le_inf (five_le_oddPart c B5 hA hc) hvc) (hv ▸ hA.ge)

/-- At the base central involution the only commuting five is the original B5. -/
theorem commuting_five_at_base (c:Choices d) (B5:Sylow 5 d.toTypeRuSetup.H) (A:Subgroup G) (hA:Nat.card A=5)
    (hc:A≤centralizer (B5Image B5:Set G)) (hz:A≤centralizer ({c.z}:Set G)) :
    A=B5Image B5 := by
  obtain ⟨q⟩:=c.fiveQuaternionData_source B5
  have hfix:fixedFive B5 c.z=B5Image B5 := c.fiveOddPart_inf_centralizer_z d.card_Z B5 q
  have hcard:Nat.card (fixedFive B5 c.z)=5 := hfix ▸ B5Image_card d.card_Z B5
  exact (commuting_five_eq_fixed c B5 c.z hcard A hA hc hz).trans hfix

open CFSG.Quasithin.ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee
open MarkedInverter MarkedNormalizer

/-- For the actual completion, the source inverter and its product with z
each have exactly their specified commuting five over the base B5. -/
theorem source_base_five_neighbors {D:Type*} [Group D] (q:Completion D)
    {F:Subgroup G} (e:first≃*F) (f:D→*G)
    (hleft:∀a:first,f (q.left a)=(e a:G)) (hz:(e modelZ:G)=c.z)
    (hfive:(zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5) :
    (∀A:Subgroup G,Nat.card A=5 → A≤centralizer (B5Image B5:Set G) →
      A≤centralizer ({c.z}:Set G) → A=B5Image B5) ∧
    (∀A:Subgroup G,Nat.card A=5 → A≤centralizer (B5Image B5:Set G) →
      A≤centralizer ({sourceU e}:Set G) → A=fixedFive B5 (sourceU e)) ∧
    (∀A:Subgroup G,Nat.card A=5 → A≤centralizer (B5Image B5:Set G) →
      A≤centralizer ({c.z*sourceU e}:Set G) → A=fixedFive B5 (c.z*sourceU e)) := by
  obtain ⟨hu,hi⟩:=source_inverter c B5 e hz hfive
  have hs:=source_three_fives c B5 (sourceU e) hu
    (PathTransport.source_fusion q c e f hleft hz) hi
  exact ⟨commuting_five_at_base c B5,
    commuting_five_eq_fixed c B5 (sourceU e) hs.1,
    commuting_five_eq_fixed c B5 (c.z*sourceU e) hs.2.1⟩
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon
