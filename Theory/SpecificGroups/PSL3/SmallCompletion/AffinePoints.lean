module
public import Theory.SpecificGroups.PSL3.SmallCompletion.NativePaths
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane

/-!
# Native affine points and their torus fixer

The first-column criterion works through the actual scalar quotient PSL₃.
Every point is on the marked line or has unique coordinates as a translate
of the opposite point. The native torus fixes just that opposite point off
the line, also over the field of four elements. The line reflection fixes
this point and swaps the two translation coordinates.

These are the native action inputs for the small-completion comparison in
Aschbacher–Smith F.4.8 and F.4.10, printed pp.278–279 (`refs/quasithin.pdf`).
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup
open scoped MatrixGroups
open Matrix.PSL3 Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.SmallCompletion
open Subgroup.CosetGeometry hiding Vertex base
open Subgroup.CosetGeometry.RankTwo
namespace Matrix.PSL3.SmallCompletion.AffinePoints
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
abbrev Points := Point (parabolic F)
def origin : Points F := ⟨base (parabolic F) false,rfl⟩
def point (g : PSL(3,F)) : Points F := g • origin F
def affineOrigin : Points F := point F (NativePaths.longest F)
def translationSL (a b : F) : SL(3,F) :=
  ⟨!![1,0,a;0,1,b;0,0,1],by simp [Matrix.det_fin_three]⟩
def translation (a b : F) : PSL(3,F) := projection F (translationSL F a b)

omit [CharP F 2] in
theorem translation_borel (a b : F) : translation F a b∈borel F := by
  exact mem_map_of_mem _ ((mem_borelSL_iff F _).mpr ⟨rfl,rfl,rfl⟩)

omit [Finite F] [CharP F 2] in
theorem translation_mul (a b c d : F) :
    translation F a b * translation F c d = translation F (a+c) (b+d) := by
  unfold translation
  rw [←map_mul]
  congr 1
  apply Subtype.ext
  change (translationSL F a b).val * (translationSL F c d).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [translationSL,Matrix.mul_apply,Fin.sum_univ_three,add_comm]

omit [Finite F] [CharP F 2] in
theorem translation_zero : translation F 0 0=1 := by
  unfold translation
  have h : translationSL F 0 0=1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [translationSL]
  rw [h,map_one]

omit [CharP F 2] in
theorem point_projection_eq_of_column (g h : SL(3,F)) (r : F)
    (he : ∀i,g.val i 0=r*h.val i 0) : point F (projection F g)=point F (projection F h) := by
  apply Subtype.ext
  change mkVertex (parabolic F) false (projection F g * 1)=
    mkVertex (parabolic F) false (projection F h * 1)
  simp only [mul_one]
  apply congrArg (CosetGeometry.Vertex.mk false)
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  change (projection F h)⁻¹ * projection F g∈pointParabolic F
  rw [←map_inv,←map_mul]
  apply mem_map_of_mem
  rw [mem_pointParabolicSL_iff]
  have hm := congrArg Subtype.val (inv_mul_cancel h)
  change h⁻¹.val*h.val=(1 : Matrix (Fin 3) (Fin 3) F) at hm
  have hc (i : Fin 3) : (h⁻¹.val*g.val) i 0 = r*(h⁻¹.val*h.val) i 0 := by
    simp only [Matrix.mul_apply,he,Fin.sum_univ_three]
    ring
  constructor
  · change (h⁻¹.val*g.val) 1 0=0
    rw [hc,hm]
    simp
  · change (h⁻¹.val*g.val) 2 0=0
    rw [hc,hm]
    simp

omit [CharP F 2] in
/-- Equality of points records precisely proportional first columns, including scalar lifts. -/
theorem column_of_point_projection_eq (g h : SL(3,F))
    (he : point F (projection F g)=point F (projection F h)) :
    ∃r : F,∀i,g.val i 0=r*h.val i 0 := by
  have hc : (projection F h : PSL(3,F) ⧸ pointParabolic F)=projection F g := by
    have hh := congrArg (fun x : Points F => (fiberEquivQuotient (parabolic F) false x)) he.symm
    change ((projection F h * 1 : PSL(3,F)) : PSL(3,F) ⧸ pointParabolic F) = (projection F g * 1 : PSL(3,F)) at hh
    simpa only [mul_one] using hh
  have hm : h⁻¹*g∈pointParabolicSL F := by
    rw [←pointParabolic_comap]
    change projection F (h⁻¹*g)∈pointParabolic F
    rw [map_mul,map_inv]
    exact QuotientGroup.eq.mp hc
  obtain ⟨h10,h20⟩ := (mem_pointParabolicSL_iff F (h⁻¹*g)).mp hm
  refine ⟨(h⁻¹*g).val 0 0,?_⟩
  intro i
  have hh : g = h*(h⁻¹*g) := by group
  nth_rw 1 [hh]
  change (h.val*(h⁻¹*g).val) i 0=(h⁻¹*g).val 0 0*h.val i 0
  simp only [Matrix.mul_apply,Fin.sum_univ_three,h10,h20,mul_zero,add_zero]
  rw [mul_comm]

omit [Finite F] in
private theorem affine_matrix_column (a b : F) (i : Fin 3) :
    (translationSL F a b * NativePaths.longestSL F).val i 0 = ![a,b,1] i := by
  change ((translationSL F a b).val * (NativePaths.longestSL F).val) i 0 = _
  fin_cases i <;> simp [translationSL,NativePaths.longestSL,Matrix.mul_apply,Fin.sum_univ_three]

theorem affine_coordinates_injective :
    Function.Injective (fun p : F×F => translation F p.1 p.2 • affineOrigin F) := by
  intro a b he
  have he' : point F (projection F (translationSL F a.1 a.2 * NativePaths.longestSL F)) =
      point F (projection F (translationSL F b.1 b.2 * NativePaths.longestSL F)) := by
    simpa only [map_mul,point,translation,affineOrigin,NativePaths.longest,mul_smul] using he
  obtain ⟨r,hr⟩ := column_of_point_projection_eq F _ _ he'
  simp only [affine_matrix_column] at hr
  have hr1 : r=1 := by simpa using (hr 2).symm
  apply Prod.ext
  · simpa [hr1] using hr 0
  · simpa [hr1] using hr 1

omit [Finite F] [CharP F 2] in
private theorem first_column_nonzero (g : SL(3,F)) :
    g.val 0 0 ≠ 0 ∨ g.val 1 0 ≠ 0 ∨ g.val 2 0 ≠ 0 := by
  by_contra hh
  push Not at hh
  have hd := g.property
  rw [Matrix.det_fin_three,hh.1,hh.2.1,hh.2.2] at hd
  simp at hd

/-- Every point is on the marked line, or has unique affine translation coordinates. -/
theorem point_cases (x : Points F) :
    (∃g : lineParabolic F,x=g.val • origin F) ∨
      ∃a b : F,x=translation F a b • affineOrigin F := by
  obtain ⟨g,hg⟩ := exists_smul_base (parabolic F) x.val
  have hx : x=point F g := Subtype.ext (by
    change x.val = g • base (parabolic F) false
    simpa only [x.property] using hg.symm)
  rw [hx]
  obtain ⟨g,rfl⟩ := projection_surjective F g
  by_cases hz : g.val 2 0=0
  · left
    by_cases hy : g.val 1 0=0
    · have hx0 : g.val 0 0 ≠ 0 := by
        rcases first_column_nonzero F g with h | h | h
        · exact h
        · exact (h hy).elim
        · exact (h hz).elim
      let h : SL(3,F) := ⟨!![g.val 0 0,0,0;0,(g.val 0 0)⁻¹,0;0,0,1],by
        simp [Matrix.det_fin_three,hx0]⟩
      refine ⟨⟨projection F h,mem_map_of_mem _ ((mem_lineParabolicSL_iff F h).mpr ⟨rfl,rfl⟩)⟩,?_⟩
      apply point_projection_eq_of_column F g h 1
      intro i
      fin_cases i <;> simp [h,hy,hz]
    · let h : SL(3,F) := ⟨!![g.val 0 0,(g.val 1 0)⁻¹,0;g.val 1 0,0,0;0,0,1],by
        simp [Matrix.det_fin_three,hy,CharTwo.neg_eq]⟩
      refine ⟨⟨projection F h,mem_map_of_mem _ ((mem_lineParabolicSL_iff F h).mpr ⟨rfl,rfl⟩)⟩,?_⟩
      apply point_projection_eq_of_column F g h 1
      intro i
      fin_cases i <;> simp [h,hz]
  · right
    refine ⟨g.val 0 0 / g.val 2 0,g.val 1 0 / g.val 2 0,?_⟩
    have he := point_projection_eq_of_column F g
      (translationSL F (g.val 0 0 / g.val 2 0) (g.val 1 0 / g.val 2 0) * NativePaths.longestSL F)
      (g.val 2 0) (by
        intro i
        rw [affine_matrix_column]
        fin_cases i <;> simp [hz,div_eq_mul_inv,mul_comm,mul_left_comm])
    simpa only [map_mul,point,translation,affineOrigin,NativePaths.longest,mul_smul] using he

theorem affine_not_line (a b : F) :
    ¬∃g : lineParabolic F,translation F a b • affineOrigin F=g.val • origin F := by
  rintro ⟨g,he⟩
  obtain ⟨h,hh,heh⟩ := g.property
  have he' : point F (projection F (translationSL F a b * NativePaths.longestSL F)) =
      point F (projection F h) := by
    simpa only [map_mul,point,translation,affineOrigin,NativePaths.longest,mul_smul,heh] using he
  obtain ⟨r,hr⟩ := column_of_point_projection_eq F _ _ he'
  have hh2 := hr 2
  rw [affine_matrix_column,(mem_lineParabolicSL_iff F h).mp hh |>.1] at hh2
  simp at hh2

theorem torus_affine (d : Fˣ×Fˣ) (a b : F) :
    torusMap F d • (translation F a b • affineOrigin F) =
      translation F ((d.1:F)*a*(d.2:F)⁻¹) ((↑((d.1*d.2)⁻¹):F)*b*(d.2:F)⁻¹) • affineOrigin F := by
  have he := point_projection_eq_of_column F
    (torusSL F d * (translationSL F a b * NativePaths.longestSL F))
    (translationSL F ((d.1:F)*a*(d.2:F)⁻¹) ((↑((d.1*d.2)⁻¹):F)*b*(d.2:F)⁻¹) * NativePaths.longestSL F)
    (d.2:F) (by
      intro i
      rw [affine_matrix_column]
      change ((torusSL F d).val * (translationSL F a b * NativePaths.longestSL F).val) i 0 = _
      rw [torusSL_val,Matrix.diagonal_mul,affine_matrix_column]
      fin_cases i <;> dsimp <;> field_simp)
  simpa only [map_mul,point,translation,affineOrigin,NativePaths.longest,mul_smul,torusMap,MonoidHom.comp_apply] using he

theorem torus_fixes_affineOrigin (d : Fˣ×Fˣ) : torusMap F d • affineOrigin F=affineOrigin F := by
  simpa only [mul_zero,zero_mul,translation_zero,one_smul] using torus_affine F d 0 0

/-- The full native torus has exactly one fixed point off the marked line. -/
theorem fixed_affine_unique (hq : 2 < Nat.card F) (x : Points F)
    (hoff : ¬∃g : lineParabolic F,x=g.val • origin F)
    (hfix : ∀d : Fˣ×Fˣ,torusMap F d • x=x) : x=affineOrigin F := by
  rcases point_cases F x with h | ⟨a,b,rfl⟩
  · exact (hoff h).elim
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [Nat.card_units]; omega)
  obtain ⟨u,hu⟩ := exists_ne (1:Fˣ)
  have hu' : (u:F) ≠ 1 := fun h => hu (Units.ext h)
  have hui : (↑u⁻¹:F) ≠ 1 := fun h => hu (inv_eq_one.mp (Units.ext h))
  have hh := hfix (u,1)
  rw [torus_affine] at hh
  have he : (((u:F)*a,(↑u⁻¹:F)*b) : F×F) = (a,b) := by
    apply affine_coordinates_injective F
    simpa only [Prod.fst,Prod.snd,Units.val_one,inv_one,mul_one] using hh
  have ha : (u:F)*a=a := by simpa using congrArg Prod.fst he
  have hb : (↑u⁻¹:F)*b=b := by simpa using congrArg Prod.snd he
  have ha0 : a=0 := by
    by_contra h
    exact hu' ((mul_eq_right₀ h).mp ha)
  have hb0 : b=0 := by
    by_contra h
    exact hui ((mul_eq_right₀ h).mp hb)
  rw [ha0,hb0,translation_zero,one_smul]

theorem reflection_affineOrigin : reflection F true • affineOrigin F=affineOrigin F := by
  have he := point_projection_eq_of_column F
    (reflectionSL F true * NativePaths.longestSL F) (NativePaths.longestSL F) 1 (by
      intro i
      change ((reflectionSL F true).val*(NativePaths.longestSL F).val) i 0 = _
      fin_cases i <;> simp [reflectionSL,NativePaths.longestSL,Matrix.mul_apply,Fin.sum_univ_three])
  simpa only [map_mul,point,affineOrigin,NativePaths.longest,reflection,mul_smul] using he

omit [Finite F] in
theorem reflection_translation (a b : F) :
    reflection F true * translation F a b * reflection F true = translation F b a := by
  unfold reflection translation
  rw [←map_mul,←map_mul]
  congr 1
  apply Subtype.ext
  change (reflectionSL F true).val*(translationSL F a b).val*(reflectionSL F true).val = _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [reflectionSL,translationSL,Matrix.mul_apply,Fin.sum_univ_three]
end Matrix.PSL3.SmallCompletion.AffinePoints
