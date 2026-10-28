module
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SmallFromCommutingFives.Eight
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicHexagon.SmallFromCommutingFives.SourceAlgebra

/-!
# Smallness from the original fixed-five placement

Choose a nontrivial element of the original fixed-five factor and lift it
through the literal placement in the fourth point stabilizer. Earlier
source algebra supplies its order-five central-label product and its
commutation with the unchanged base rotation. The exact distance-eight
argument then proves Small for the original completion.

The placement input is the earlier J.4 source j/six-cycle construction;
its final discharge belongs to SourceAmalgam's original completion assembly.
No commuting, graph-action, girth, or recognition premise is introduced.
Source: Aschbacher–Smith J.4.10, printed p.445.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
open FiveHexagon FiveHexagon.MarkedInverter FiveHexagon.PathTransport Centralizers.Choices
open ChapterF.SourceCompletion.BinaryRee
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open Subgroup.CosetGeometry.RankTwo
variable {K:Type*} [Group K] (q:Completion K)
  {G:Type*} [Group G] [Finite G] {d:LocalSetup G}
  (c:Centralizers.Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
  {F:Subgroup G} (e:first≃*F) (f:K→*G)

 theorem source_small_of_fixedFive_placement
    (hf:Function.Injective f) (hleft:∀a:first,f (q.left a)=(e a:G))
    (hz:(e modelZ:G)=c.z)
    (hfive:(zpowers modelRotation).map (F.subtype.comp e.toMonoidHom)=B5Image B5)
    (hplace:fixedFive B5 (sourceU e)≤
      (stabilizer q.family (completionFourthWord q•basePoint q)).map f) : q.Small := by
  have hcard:Nat.card (fixedFive B5 (sourceU e))=5:=
    (source_fixed_pair c B5 e hz hfive (PathTransport.source_fusion q c e f hleft hz)).1
  have hex:∃a:G,a∈fixedFive B5 (sourceU e) ∧ a≠1:=by
    by_contra hh
    push Not at hh
    have hbot:fixedFive B5 (sourceU e)=⊥:=eq_bot_iff.mpr (fun a ha=>hh a ha)
    rw [hbot,card_bot] at hcard
    contradiction
  obtain ⟨a,ha,ha1⟩:=hex
  obtain ⟨b,hb,he⟩:=hplace ha
  subst a
  apply small_of_fourth_fixer q b hb
  · exact fixed_five_label_product q c B5 e f hf hleft hz hfive b ha ha1
  · exact fixed_five_commutes_rotation q B5 e f hf hleft hfive b ha
end CFSG.Quasithin.ChapterJ.RuSubgroup.ParabolicHexagon.SmallFromCommutingFives
