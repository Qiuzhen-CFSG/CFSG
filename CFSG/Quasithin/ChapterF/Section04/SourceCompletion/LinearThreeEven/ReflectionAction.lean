module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.LinearThreeEven.ExtensionPoints

/-!
# Determining the native reflection on every point

Unique short paths give coordinates equivariant for the full left endpoint.
The native torus has a unique fixed point off the marked line. Its normalizing
reflection fixes that point, and its conjugation on the affine translation
group determines its action on every remaining point. On the marked line the
original right endpoint action already agrees. This retains the prescribed
reflection and the full projective scalar quotient, also over the field of four.

Source: the linear-three recognition in Aschbacher–Smith F.4.8, p.278.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
namespace CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {E : SourceExtension F} {G : Type*} [Group G]
variable (c : Completion E G)
variable (ho : c.left.range⊓c.right.range=c.middle.range) {n : ℕ} (hF : Nat.card F=2^n)
variable (dc : ∀v w,c.graph.dist v w≤3)

def nativeCoordinates : Point c.family ≃ AffinePoints.Points F :=
  (c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)).trans
    E.modelPointEquiv.symm

def origin : Point c.family := ⟨base c.family false,rfl⟩

theorem nativeCoordinates_origin : c.nativeCoordinates ho hF dc c.origin=AffinePoints.origin F := by
  apply E.modelPointEquiv.injective
  change E.modelPointEquiv (E.modelPointEquiv.symm _) = _
  rw [E.modelPointEquiv.apply_symm_apply,E.modelPointEquiv_origin]
  exact c.pointComparison_base _ _ _ _ _ _

theorem nativeCoordinates_left (a : pointParabolic F) (x : Point c.family) :
    c.nativeCoordinates ho hF dc (c.left (E.nativeLeft a) • x)=a.val • c.nativeCoordinates ho hF dc x := by
  apply E.modelPointEquiv.injective
  rw [E.modelPointEquiv_smul]
  change E.modelPointEquiv (E.modelPointEquiv.symm _) = E.baseHom a.val • E.modelPointEquiv (E.modelPointEquiv.symm _)
  rw [E.modelPointEquiv.apply_symm_apply,E.modelPointEquiv.apply_symm_apply]
  exact c.pointComparison_left _ _ _ _ _ _ (E.nativeLeft a) x

theorem nativeCoordinates_line_iff (x : Point c.family) :
    (∃a : E.right,x=c.right a • c.origin) ↔
      ∃b : lineParabolic F,c.nativeCoordinates ho hF dc x=b.val • AffinePoints.origin F := by
  rw [←E.model_line_orbit]
  constructor
  · rintro ⟨a,rfl⟩
    refine ⟨a,?_⟩
    change E.modelPointEquiv (E.modelPointEquiv.symm _) = _
    rw [E.modelPointEquiv.apply_symm_apply]
    exact c.pointComparison_right_base _ _ _ _ _ _ a
  · rintro ⟨a,ha⟩
    refine ⟨a,?_⟩
    apply (c.pointComparison E.model ho (E.completion_overlap _) hF dc (E.model_diameter hF)).injective
    rw [origin,c.pointComparison_right_base]
    exact (E.modelPointEquiv.apply_symm_apply _).symm.trans ha

def nativeBorelLeft (b : borel F) : pointParabolic F := ⟨b.val,by
  obtain ⟨a,ha,he⟩ := b.property
  exact he ▸ mem_map_of_mem _ ha.1⟩
def nativeBorelRight (b : borel F) : lineParabolic F := ⟨b.val,by
  obtain ⟨a,ha,he⟩ := b.property
  exact he ▸ mem_map_of_mem _ ha.2⟩

def nativeBorel : borel F →* G := c.left.comp (E.nativeLeft.comp
  (inclusion (by
    intro b hb
    obtain ⟨a,ha,rfl⟩ := hb
    exact mem_map_of_mem _ ha.1)))

omit [Finite F] [CharP F 2] in
theorem nativeBorel_left (b : borel F) : c.nativeBorel b=c.left (E.nativeLeft (nativeBorelLeft b)) := rfl

omit [Finite F] [CharP F 2] in
theorem nativeBorel_right (b : borel F) : c.nativeBorel b=c.right (E.nativeRight (nativeBorelRight b)) :=
  DFunLike.congr_fun c.compatible
    ⟨MulAut.conj b.val,(E.nativeLeft (nativeBorelLeft b)).property,(E.nativeRight (nativeBorelRight b)).property⟩

theorem nativeCoordinates_borel (b : borel F) (x : Point c.family) :
    c.nativeCoordinates ho hF dc (c.nativeBorel b • x)=b.val • c.nativeCoordinates ho hF dc x :=
  c.nativeCoordinates_left ho hF dc (nativeBorelLeft b) x

def lineReflection : G := c.right (E.nativeRight ⟨reflection F true,by exact reflection_mem F true⟩)

theorem lineReflection_sq : c.lineReflection*c.lineReflection=1 := by
  change (c.right.comp E.nativeRight) _ * (c.right.comp E.nativeRight) _ = 1
  rw [←map_mul,←pow_two,show (⟨reflection F true,by exact reflection_mem F true⟩ : lineParabolic F)^2=1 from
    Subtype.ext (reflection_sq F true),map_one]

private theorem reflection_conjugates_borel (a b : borel F)
    (h : reflection F true * a.val * reflection F true=b.val) :
    c.lineReflection*c.nativeBorel a*c.lineReflection=c.nativeBorel b := by
  rw [c.nativeBorel_right,c.nativeBorel_right]
  change (c.right.comp E.nativeRight) _ * (c.right.comp E.nativeRight) _ * (c.right.comp E.nativeRight) _ = _
  rw [←map_mul,←map_mul]
  exact congrArg (c.right.comp E.nativeRight) (Subtype.ext h)

def torusBorel (d : Fˣ×Fˣ) : borel F := ⟨torusMap F d,torus_le_borel F ⟨d,rfl⟩⟩
def translationBorel (a b : F) : borel F := ⟨AffinePoints.translation F a b,AffinePoints.translation_borel F a b⟩

private theorem reflection_torus (d : Fˣ×Fˣ) : ∃e : Fˣ×Fˣ,
    c.lineReflection*c.nativeBorel (torusBorel d)*c.lineReflection=c.nativeBorel (torusBorel e) := by
  have hn := reflection_normalizes_torus F true
  have hh := (mem_normalizer_iff.mp hn (torusMap F d)).mp ⟨d,rfl⟩
  obtain ⟨e,he⟩ := hh
  refine ⟨e,c.reflection_conjugates_borel (torusBorel d) (torusBorel e) ?_⟩
  have hi : (reflection F true)⁻¹=reflection F true :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using reflection_sq F true)
  simpa only [torusBorel,hi] using he.symm

/-- The transported reflection fixes the unique affine point fixed by the native torus. -/
theorem nativeCoordinates_reflection_affineOrigin (hq : 2 < Nat.card F) :
    c.nativeCoordinates ho hF dc
      (c.lineReflection • (c.nativeCoordinates ho hF dc).symm (AffinePoints.affineOrigin F)) =
      AffinePoints.affineOrigin F := by
  let e := c.nativeCoordinates ho hF dc
  let o := e.symm (AffinePoints.affineOrigin F)
  have hooff : ¬∃a : E.right,o=c.right a • c.origin := by
    rw [c.nativeCoordinates_line_iff ho hF dc]
    change ¬∃a : lineParabolic F,e o=a.val • AffinePoints.origin F
    rw [show e o=AffinePoints.affineOrigin F from e.apply_symm_apply _]
    simpa only [AffinePoints.translation_zero,one_smul] using AffinePoints.affine_not_line F 0 0
  apply AffinePoints.fixed_affine_unique F hq
  · intro hline
    obtain ⟨a,ha⟩ := (c.nativeCoordinates_line_iff ho hF dc _).mpr hline
    apply hooff
    refine ⟨(E.nativeRight ⟨reflection F true,by exact reflection_mem F true⟩)*a,?_⟩
    have hh := congrArg (c.lineReflection • ·) ha
    rw [←mul_smul,c.lineReflection_sq,one_smul,←mul_smul] at hh
    exact hh.trans (by rw [map_mul]; rfl)
  · intro d
    obtain ⟨k,hk⟩ := c.reflection_torus d
    have hkfix : c.nativeBorel (torusBorel k) • o=o := by
      apply e.injective
      rw [c.nativeCoordinates_borel]
      change torusMap F k • e o=e o
      rw [show e o=AffinePoints.affineOrigin F from e.apply_symm_apply _]
      exact AffinePoints.torus_fixes_affineOrigin F k
    have hs : c.nativeBorel (torusBorel d) • (c.lineReflection • o)=c.lineReflection • o := by
      have he : c.nativeBorel (torusBorel d)*c.lineReflection=
          c.lineReflection*c.nativeBorel (torusBorel k) := by
        calc
          _ = (c.lineReflection*c.lineReflection)*c.nativeBorel (torusBorel d)*c.lineReflection := by rw [c.lineReflection_sq,one_mul]
          _ = c.lineReflection*(c.lineReflection*c.nativeBorel (torusBorel d)*c.lineReflection) := by group
          _ = _ := by rw [hk]
      rw [←mul_smul,he,mul_smul,hkfix]
    have hh := congrArg e hs
    exact (c.nativeCoordinates_borel ho hF dc (torusBorel d) _).symm.trans hh

theorem nativeCoordinates_right_native_base (a : lineParabolic F) :
    c.nativeCoordinates ho hF dc (c.right (E.nativeRight a) • c.origin)=a.val • AffinePoints.origin F := by
  apply E.modelPointEquiv.injective
  rw [E.modelPointEquiv_smul,E.modelPointEquiv_origin]
  change E.modelPointEquiv (E.modelPointEquiv.symm _) = _
  rw [E.modelPointEquiv.apply_symm_apply]
  exact c.pointComparison_right_base _ _ _ _ _ _ (E.nativeRight a)

/-- The native line reflection agrees on every point, with its prescribed marking. -/
theorem nativeCoordinates_lineReflection (hq : 2 < Nat.card F) (x : Point c.family) :
    c.nativeCoordinates ho hF dc (c.lineReflection • x)=
      reflection F true • c.nativeCoordinates ho hF dc x := by
  let e := c.nativeCoordinates ho hF dc
  let o := e.symm (AffinePoints.affineOrigin F)
  have heo : e o=AffinePoints.affineOrigin F := e.apply_symm_apply _
  have hso := c.nativeCoordinates_reflection_affineOrigin ho hF dc hq
  rcases AffinePoints.point_cases F (e x) with ⟨a,ha⟩ | ⟨a,b,hab⟩
  · have hx : x=c.right (E.nativeRight a) • c.origin :=
      e.injective (ha.trans (c.nativeCoordinates_right_native_base ho hF dc a).symm)
    rw [hx,←mul_smul]
    change e (((c.right.comp E.nativeRight) _ * (c.right.comp E.nativeRight) a) • c.origin) = _
    rw [←map_mul]
    change e (c.right (E.nativeRight (⟨reflection F true,by exact reflection_mem F true⟩ * a)) • c.origin) = _
    exact (c.nativeCoordinates_right_native_base ho hF dc _).trans
      ((mul_smul _ _ _).trans (congrArg (reflection F true • ·)
        (c.nativeCoordinates_right_native_base ho hF dc a).symm))
  · have hx : x=c.nativeBorel (translationBorel a b) • o := by
      apply e.injective
      rw [c.nativeCoordinates_borel]
      exact hab.trans (congrArg (AffinePoints.translation F a b • ·) heo.symm)
    have hc := c.reflection_conjugates_borel (translationBorel a b) (translationBorel b a)
      (AffinePoints.reflection_translation F a b)
    have hmul : c.lineReflection*c.nativeBorel (translationBorel a b)=
        c.nativeBorel (translationBorel b a)*c.lineReflection := by
      rw [←hc]
      symm
      calc
        _ = c.lineReflection*c.nativeBorel (translationBorel a b)*(c.lineReflection*c.lineReflection) := by group
        _ = _ := by rw [c.lineReflection_sq,mul_one]
    change e (c.lineReflection • x)=reflection F true • e x
    rw [hx,←mul_smul,hmul,mul_smul,c.nativeCoordinates_borel,hso]
    rw [c.nativeCoordinates_borel,heo]
    change AffinePoints.translation F b a • AffinePoints.affineOrigin F =
      reflection F true • (AffinePoints.translation F a b • AffinePoints.affineOrigin F)
    have hw : reflection F true*AffinePoints.translation F a b=
        AffinePoints.translation F b a*reflection F true := by
      rw [←AffinePoints.reflection_translation F a b]
      symm
      have hs : reflection F true*reflection F true=1 := by simpa only [pow_two] using reflection_sq F true
      calc
        _ = reflection F true*AffinePoints.translation F a b*(reflection F true*reflection F true) := by group
        _ = _ := by rw [hs,mul_one]
    rw [←mul_smul,hw,mul_smul,AffinePoints.reflection_affineOrigin]

end CFSG.Quasithin.ChapterF.SourceCompletion.LinearThreeEven.Completion
