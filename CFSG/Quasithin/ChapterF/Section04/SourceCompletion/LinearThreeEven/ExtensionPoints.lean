module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.PointComparison
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.Inner
public import Theory.SpecificGroups.PSL3.SmallCompletion.AffinePoints
public import Theory.GroupAction.RankTwoCosetGeometry.ExtensionGeometry

/-!
# Native points inside full type-preserving extensions

The whole middle supplements the inner group, so every full-extension flag
has a native representative. This gives the actual point-set comparison and
transfers the triangle metric. A faithful collineation is determined by points.

Source: Aschbacher–Smith F.4.8–9, printed pp.278–279.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.SourceExtension
variable {F : Type*} [Field F] [Finite F] (E : SourceExtension F)
abbrev model := E.completion (parabolics_sup_eq_top F)

theorem model_pre (i : Bool) : (E.model.cosetFamily i).comap E.baseHom=parabolic F i := by
  rw [E.completion_family]
  ext x
  exact E.baseHom_mem_family_iff (native_conj_injective F) i x

theorem model_rep (a : E.carrier) :
    ∃b : PSL(3,F),(E.baseHom b)⁻¹*a ∈ E.model.cosetFamily false ⊓ E.model.cosetFamily true := by
  obtain ⟨b,d,hd,he⟩ := E.factor a a.property
  refine ⟨b,?_⟩
  rw [E.completion_family]
  have hh : ((E.baseHom b)⁻¹*a).val=d := by
    change (MulAut.conj b)⁻¹*a.val=d
    rw [he,inv_mul_cancel_left]
  change ((E.baseHom b)⁻¹*a).val∈E.middle
  rw [hh]
  exact hd

def modelGraphIso : RankTwo.graph (parabolic F) ≃g RankTwo.graph E.model.cosetFamily :=
  ExtensionGeometry.graphIso (parabolic F) E.model.cosetFamily E.baseHom
    (model_pre E) (model_rep E)

def modelPointEquiv : AffinePoints.Points F ≃ Point E.model.cosetFamily :=
  E.modelGraphIso.toEquiv.subtypeEquiv (fun _ => Iff.rfl)

theorem modelPointEquiv_smul (g : PSL(3,F)) (x : AffinePoints.Points F) :
    E.modelPointEquiv (g • x)=E.baseHom g • E.modelPointEquiv x :=
  Subtype.ext (ExtensionGeometry.vertex_smul _ _ _ _ g x.val)

theorem modelPointEquiv_origin : E.modelPointEquiv (AffinePoints.origin F)=
    (⟨base E.model.cosetFamily false,rfl⟩ : Point E.model.cosetFamily) :=
  Subtype.ext (ExtensionGeometry.vertex_base _ _ _ _ false)

theorem model_left_native (x : pointParabolic F) : E.model.left (E.nativeLeft x)=E.baseHom x.val := rfl

theorem model_right_native (x : lineParabolic F) : E.model.right (E.nativeRight x)=E.baseHom x.val := rfl

/-- Full right endpoint orbits equal the native line orbit; all outer factors fix the root. -/
theorem model_line_orbit (x : AffinePoints.Points F) :
    (∃a : E.right,E.modelPointEquiv x=E.model.right a • (⟨base E.model.cosetFamily false,rfl⟩ : Point E.model.cosetFamily)) ↔
      ∃b : lineParabolic F,x=b.val • AffinePoints.origin F := by
  constructor
  · rintro ⟨a,ha⟩
    obtain ⟨b,hb,d,hd,he⟩ := E.right_factor (native_conj_injective F) a a.property
    let d' : E.middle := ⟨d,hd⟩
    have ha' : a=E.nativeRight ⟨b,hb⟩ * E.amalgam.right d' := Subtype.ext he
    have hfix : E.model.middle d' • (⟨base E.model.cosetFamily false,rfl⟩ : Point E.model.cosetFamily)=
        ⟨base E.model.cosetFamily false,rfl⟩ := by
      apply Subtype.ext
      change E.model.middle d' ∈ stabilizer E.model.cosetFamily (base E.model.cosetFamily false)
      rw [stabilizer,base,CosetGeometry.stabilizer_base]
      exact E.model.middle_le_left ⟨d',rfl⟩
    have hm := DFunLike.congr_fun E.model.compatible d'
    change E.model.middle d'=E.model.right (E.amalgam.right d') at hm
    rw [ha',map_mul,mul_smul,←hm,hfix,model_right_native] at ha
    refine ⟨⟨b,hb⟩,E.modelPointEquiv.injective ?_⟩
    rw [modelPointEquiv_smul,modelPointEquiv_origin]
    exact ha
  · rintro ⟨b,rfl⟩
    exact ⟨E.nativeRight b,by rw [modelPointEquiv_smul,modelPointEquiv_origin,model_right_native]⟩

variable [CharP F 2]
theorem model_diameter {n : ℕ} (hF : Nat.card F=2^n) :
    ∀v w,(RankTwo.graph E.model.cosetFamily).dist v w≤3 := by
  intro v w
  obtain ⟨v,rfl⟩ := E.modelGraphIso.surjective v
  obtain ⟨w,rfl⟩ := E.modelGraphIso.surjective w
  have hn : ∀v w,(RankTwo.graph (parabolic F)).dist v w≤3 := by
    rw [←model_family F]
    exact native_model_diameter F hF
  obtain ⟨p,_,hp⟩ := (RankTwo.connected (parabolic F) (parabolics_sup_eq_top F)).exists_path_of_dist v w
  exact (SimpleGraph.dist_le (p.map E.modelGraphIso.toHom)).trans
    (by rw [SimpleGraph.Walk.length_map,hp]; exact hn v w)

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.SourceExtension

namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
open Configuration
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {E : SourceExtension F} {G : Type*} [Group G] [Finite G]
variable (c : Completion E G)
/-- The original point action is faithful as soon as the triangle geometry closes. -/
theorem point_action_injective (ho : c.left.range⊓c.right.range=c.middle.range)
    {n : ℕ} (hF : Nat.card F=2^n) (hd : ∀v w,c.graph.dist v w≤3) :
    Function.Injective (MulAction.toPermHom G (Point c.family)) := by
  let _ := projectivePlaneOfGeometry c.family c.generated
    (c.uniqueGeodesicsBelow_three ho hF) hd (Nat.card F) Finite.one_lt_card
    (c.card_neighbors ho hF)
  intro g h he
  have hh : Collineation.ofAction G (Point c.family) (Line c.family) g =
      Collineation.ofAction G (Point c.family) (Line c.family) h := by
    apply Collineation.ext_points
    intro x
    exact Equiv.congr_fun he x
  apply c.vertex_action_injective ho
  apply Equiv.Perm.ext
  intro v
  change g • v=h • v
  cases ht : v.type with
  | false => exact congrArg Subtype.val (Equiv.congr_fun he ⟨v,ht⟩)
  | true => exact congrArg Subtype.val (congrArg (fun a : Collineation (Point c.family) (Line c.family) =>
      Collineation.lineHom (Point c.family) (Line c.family) a ⟨v,ht⟩) hh)
end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
