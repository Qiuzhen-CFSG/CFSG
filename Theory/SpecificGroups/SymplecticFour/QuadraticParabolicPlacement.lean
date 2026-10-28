module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.LargeQuadratic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.TwoLocalCover.Geometry
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.ParabolicWings

/-!
# Placing large quadratic actors in a plane radical

The displacement of a quadratic actor of order greater than q is a
self-orthogonal plane. An actual symplectic basis change carries it to the
standard plane, whose pointwise fixers form the literal plane radical.
Thus every small Sylow actor of order at least q² has this containment,
including actors which are not vector spaces over the original field.

The application in NonbinarySymplectic.CriticalReduction.UnequalMovers
uses this containment and the maximizing choice to prove the opening
nonquadratic assertion in MS93 (5.5), printed p.916. No central complement
or field-degree restriction is used.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2] [Algebra (ZMod 2) F]

omit [Finite F] [CharP F 2] [Algebra (ZMod 2) F] in
private theorem plane_fixer_mem_radical (g : Sp F)
    (hfix : ∀ v ∈ plane F, g • v = v) :
    g ∈ (Plane.radical (F := F)).map planeLocal.subtype := by
  have hA : g.val.toBlocks₁₁ = 1 := by
    ext i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inl i)
    simpa [smul_eq_mulVec,e,Matrix.mulVec_single,Matrix.toBlocks₁₁,
      Matrix.one_apply,Pi.single_apply] using h
  have hP : g ∈ planeParabolic := by
    rw [mem_planeParabolic_iff]
    intro i j
    have h := congrFun (hfix (e j) (e_mem_plane j)) (.inr i)
    simpa [smul_eq_mulVec,e,Matrix.mulVec_single] using h
  have hg : g ∈ planeLocal := (Plane.mem_local_iff g).mpr
    ⟨hP,by rw [hA]; exact Matrix.det_one⟩
  refine ⟨⟨g,hg⟩,?_,rfl⟩
  apply Subtype.ext
  exact hA

/-- A quadratic actor larger than a field has a conjugate inside the
literal plane radical, without a scalar-closure assumption. -/
theorem large_quadratic_conjugate_le_plane
    (A : Subgroup (Sp F))
    (hq : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hlarge : Nat.card F < Nat.card A) :
    ∃ g : Sp F, A.map (MulAut.conj g).toMonoidHom ≤
      (wing true).map (unipotent (F := F)).subtype := by
  let W := displacementSpace A
  have hself : (form F).orthogonal W = W :=
    large_quadratic_displacement_self_orthogonal A hq hlarge
  have hd : Module.finrank F W = 2 := by
    have hh := LinearMap.BilinForm.finrank_orthogonal
      (W := W) TwoLocalCover.form_nondegenerate
    rw [hself] at hh
    have hV : Module.finrank F (Vector F) = 4 := by simp [Vector]
    rw [hV] at hh
    omega
  have hne : W ≠ ⊥ := by
    intro he
    rw [he,finrank_bot] at hd
    omega
  obtain ⟨g,hg⟩ := TwoLocalCover.isotropic_subspace_conjugate_standard W hne
    (quadratic_displacement_isotropic A hq)
  have hp : W.map (toLinear g).toLinearMap = plane F := by
    rcases hg with hp | hp
    · have hh := (toLinear g).finrank_map_eq W
      rw [hp,finrank_point,hd] at hh
      omega
    · exact hp
  refine ⟨g,?_⟩
  rintro _ ⟨x,hx,rfl⟩
  rw [←SymplecticConjugatePair.planeRadical_eq_wing]
  apply plane_fixer_mem_radical
  intro v hv
  rw [←hp] at hv
  obtain ⟨w,hw,rfl⟩ := hv
  have hwf := displacementSpace_le_fixedSpace_of_quadratic A hq hw x hx
  change (g*x*g⁻¹) • (g • w) = g • w
  simp only [mul_smul,inv_smul_smul,hwf]

/-- A small Sylow actor of order at least q squared can be placed inside
one whole plane radical at the original degree. -/
theorem large_small_conjugate_le_plane
    (A : Subgroup (unipotent (F := F)))
    (hm : CentralRootGeometry.SmallMovers.movingIndex A ≤ Nat.card F^2)
    (hc : Nat.card F^2 ≤ Nat.card A) :
    ∃ g : Sp F, (A.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ≤
      (wing true).map unipotent.subtype := by
  apply large_quadratic_conjugate_le_plane
  · exact CentralRootGeometry.SmallMovers.Degree.small_quadratic A ⟨hm.trans hc,hm⟩
  · rw [card_map_of_injective unipotent.subtype_injective]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hh : Nat.card F < Nat.card F^2 := by nlinarith
    exact hh.trans_le hc
end Theory.SpecificGroups.SymplecticFour
