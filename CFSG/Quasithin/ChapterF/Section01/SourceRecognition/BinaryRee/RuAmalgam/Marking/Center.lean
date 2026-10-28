module
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedInverter
public import CFSG.Quasithin.ChapterJ.Section04To05.ParabolicCentralizers
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveNormalizer.Source
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.AbelianNormalizer

/-!
# The forced central involution marking

Every first-endpoint equivalence sends the model central involution to the
chosen original z. The original centralizer of Q₅ is Z of order two, so the
first endpoint has only one nonidentity central element. This preserves
any subsequent simultaneous conjugation used to mark the five-subgroup.

Source: Aschbacher–Smith J.4.5–7 and the original J.2 setup.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open Centralizers.Choices FiveHexagon.MarkedInverter
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
variable {G:Type*} [Group G] [Finite G] {d:LocalSetup G} {p:Plane d}

 theorem first_equiv_marks_z (c:Centralizers.Choices d) (B5:Sylow 5 d.toTypeRuSetup.H)
    (e:first≃*p.F₁ B5) : (e modelZ:G)=c.z := by
  have hz:modelZ∈center first:=by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (first_eq_centralizer_z ▸ a.property)
  have he:e modelZ∈center (p.F₁ B5):=by
    apply mem_center_iff.mpr
    intro a
    obtain ⟨b,rfl⟩:=e.surjective a
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hz b)
  have heZ:(e modelZ:G)∈d.toTypeRuSetup.Z:=by
    rw [←centralizer_Q₅ d B5]
    intro a ha
    let aF:p.F₁ B5:=⟨a,(show Q₅ d B5≤p.F₁ B5 from le_sup_right.trans le_sup_left) ha⟩
    exact congrArg (fun b:p.F₁ B5=>(b:G)) (mem_center_iff.mp he aF)
  have hmodel:modelZ≠1:=fun h=>FiveNormalizer.z_ne_one (congrArg Subtype.val h)
  have he1:(e modelZ:G)≠1:=by
    intro h
    apply hmodel
    apply e.injective
    exact (Subtype.ext h).trans e.map_one.symm
  have hz1:c.z≠1:=by
    intro h
    have ho:=SourceCompletion.z_order c
    rw [h,orderOf_one] at ho
    omega
  obtain ⟨w,_,hw⟩:=(Nat.card_eq_two_iff' (1:d.toTypeRuSetup.Z)).mp d.card_Z
  have heq:(⟨e modelZ,heZ⟩:d.toTypeRuSetup.Z)=⟨c.z,c.z_mem_Z⟩:=
    (hw _ (fun h=>he1 (congrArg Subtype.val h))).trans
      (hw _ (fun h=>hz1 (congrArg Subtype.val h))).symm
  exact congrArg Subtype.val heq
end CFSG.Quasithin.ChapterJ.RuSubgroup
