module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.MarkedSecondCore
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FullRee.LongRootPaths.ShortSupplement

/-!
# The actual source second core has the required short centralizer supplement

The corrected model Levi lifts are transported through the same literal
second endpoint equivalence as the marked commutator. The established source
quotient identifies its intrinsic core with A. Consequently F₂=A C_F₂(t)
for the original marked short commutator t, with no centralizer premise.
Source: the local calculation in J.4.7, printed p.444.
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
open Subgroup
open scoped Pointwise
open Tits.ExceptionalParabolics.FullRee
open Tits.ExceptionalParabolics.FullRee.LongRootPaths

private theorem internal_supplement :
    pCore 2 second ⊔ centralizer ({modelShort}:Set second)=⊤ := by
  apply Subgroup.map_injective second.subtype_injective
  rw [Subgroup.map_sup,← MonoidHom.range_eq_map,range_subtype,map_subtype_centralizer_singleton]
  change secondCore ⊔ (second ⊓ centralizer ({shortCommutator}:Set (ReeF4.Model 0)))=second
  rw [inf_eq_right.mpr commutator_centralizer_le_second,secondCore_sup_shortCentralizer]

variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)
  (B5 : Sylow 5 d.toTypeRuSetup.H) (X : Sylow 3 p.parabolic)
  (h : Nonempty (((p.F₂ B5 X) ⧸ (p.A B5).subgroupOf (p.F₂ B5 X)) ≃* Equiv.Perm (Fin 3)))
  (e : second ≃* p.F₂ B5 X)

/-- The same source endpoint map carries the short centralizer onto the
literal centralizer intersection, retaining its actual marked element. -/
theorem source_shortCentralizer_map :
    (centralizer ({modelShort}:Set second)).map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)=
      p.F₂ B5 X ⊓ centralizer ({(e modelShort:G)}:Set G) := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    refine ⟨(e a).property,mem_centralizer_singleton_iff.mpr ?_⟩
    change (e a:G)*(e modelShort:G)=(e modelShort:G)*(e a:G)
    simpa only [map_mul,coe_mul] using
      congrArg (fun a:second => (e a:G)) (mem_centralizer_singleton_iff.mp ha)
  · rintro ⟨hx,hc⟩
    obtain ⟨a,ha⟩ := e.surjective ⟨x,hx⟩
    refine ⟨a,?_,congrArg Subtype.val ha⟩
    apply mem_centralizer_singleton_iff.mpr
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul,coe_mul,ha] using mem_centralizer_singleton_iff.mp hc

include h in
/-- The original A and the centralizer of the literal short commutator
supplement one another in the source F₂. -/
theorem source_shortCentralizer_supplement :
    p.A B5 ⊔ (p.F₂ B5 X ⊓ centralizer ({(e modelShort:G)}:Set G))=p.F₂ B5 X := by
  have hh := congrArg (fun K:Subgroup second =>
    K.map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)) internal_supplement
  rw [Subgroup.map_sup,source_shortCentralizer_map p B5 X e] at hh
  have hp : (pCore 2 second).map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)=p.A B5 := by
    rw [← Subgroup.map_map,pCore_map_iso 2 e,p.F₂_core B5 X h]
    exact map_subgroupOf_eq_of_le (p.A_le_F₂ B5 X)
  have ht : (⊤:Subgroup second).map ((p.F₂ B5 X).subtype.comp e.toMonoidHom)=p.F₂ B5 X := by
    rw [← Subgroup.map_map,Subgroup.map_top_of_surjective e.toMonoidHom e.surjective,
      ← MonoidHom.range_eq_map,range_subtype]
  simpa only [hp,ht] using hh

include h in
/-- The supplement is the actual set product in the original ambient group. -/
theorem source_shortCentralizer_product :
    (p.F₂ B5 X:Set G)=(p.A B5:Set G)*
      ((p.F₂ B5 X ⊓ centralizer ({(e modelShort:G)}:Set G):Subgroup G):Set G) := by
  calc
    (p.F₂ B5 X:Set G) = ((p.A B5 ⊔ (p.F₂ B5 X ⊓
        centralizer ({(e modelShort:G)}:Set G)):Subgroup G):Set G) :=
      congrArg (fun K:Subgroup G => (K:Set G)) (source_shortCentralizer_supplement p B5 X h e).symm
    _ = _ := coe_mul_of_right_le_normalizer_left _ _
      (inf_le_left.trans ((p.F₂_le_parabolic B5 X).trans (p.A_normalized B5)))

end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.MarkedSecondCore
