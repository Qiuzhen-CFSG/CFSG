module
public import Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry.Placement

/-!
# Parabolic conjugators into the symplectic Sylow center

Every involution of the standard Sylow lies in one of its two elementary
wings. For a plane-radical element, a determinant-one Levi matrix sends
its symmetric shear matrix to one with vanishing lower diagonal entry.
The exceptional graph automorphism transports the same construction to
the point radical. Thus the conjugator belongs to the corresponding
actual parabolic, and both the initial and final elements lie in the
common Sylow. These witnesses can be transported through a compatible
amalgam without an isomorphism of its completion.

Source: the symplectic case of Aschbacher–Smith F.4.27 and F.4.30,
printed pp.288–290 of `refs/quasithin.pdf`.
-/

public noncomputable section
set_option linter.unusedSimpArgs false
open Subgroup Matrix
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
open CentralRootGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem plane_conjugate_center (x : Sp F)
    (hx : x ∈ SymplecticConjugatePair.planeRadical) :
    ∃ g ∈ planeParabolic (F := F),
      g*x*g⁻¹ ∈ (center (unipotent (F := F))).map unipotent.subtype := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨B,rfl⟩ := (SymplecticConjugatePair.mem_planeRadical_iff _).mp hx
  by_cases hb : B.val 1 1 = 0
  · refine ⟨1,one_mem _,?_⟩
    simpa only [one_mul,inv_one,mul_one,SymplecticConjugatePair.sylowCenter] using
      SymplecticConjugatePair.shear_mem_sylowCenter B hb
  obtain ⟨t,ht⟩ := (frobeniusEquiv F 2).surjective (B.val 0 0 / B.val 1 1)
  have ht' : t^2 = B.val 0 0 / B.val 1 1 := ht
  let M : SpecialLinearGroup (Fin 2) F := ⟨!![0,-1;1,t],by simp [det_fin_two]⟩
  refine ⟨Plane.leviSp M,planeLocal_le (Plane.levi M).property,?_⟩
  change (MulAut.conj (Plane.leviSp M)) (Plane.shearSp B) ∈ _
  rw [SymplecticConjugatePair.conjugate_levi_shear]
  apply SymplecticConjugatePair.shear_mem_sylowCenter
  have he : B.val 0 0 + t^2*B.val 1 1 = 0 := by
    rw [ht',div_mul_cancel₀ _ hb,CharTwo.add_self_eq_zero]
  have hs : B.val 0 1 = B.val 1 0 := B.property.apply 1 0
  change (M.val * B.val * M.valᵀ) 1 1 = 0
  simp only [Matrix.mul_apply,Fin.sum_univ_two,transpose_apply,M,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,one_mul,hs]
  calc
    _ = B.val 0 0 + t^2*B.val 1 1 := by ring_nf; simp [CharTwo.two_eq_zero,mul_comm]
    _ = 0 := he

private theorem point_conjugate_center (x : Sp F)
    (hx : x ∈ SymplecticConjugatePair.pointRadical) :
    ∃ g ∈ pointParabolic (F := F),
      g*x*g⁻¹ ∈ (center (unipotent (F := F))).map unipotent.subtype := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let a := graphAut (F := F)
  have hax : a x ∈ SymplecticConjugatePair.planeRadical :=
    SymplecticConjugatePair.graphAut_map_pointRadical_le (mem_map_of_mem _ hx)
  obtain ⟨g,hg,hz⟩ := plane_conjugate_center (a x) hax
  have hag : a.symm g ∈ pointParabolic := by
    have hh : g ∈ pointParabolic.map a.toMonoidHom := by rwa [graphAut_map_point]
    obtain ⟨y,hy,he⟩ := hh
    change y ∈ pointParabolic at hy
    change a y = g at he
    rw [←he,a.symm_apply_apply]
    exact hy
  refine ⟨a.symm g,hag,?_⟩
  have hh : g*a x*g⁻¹ ∈ SymplecticConjugatePair.sylowCenter.map a.toMonoidHom := by
    rwa [SymplecticConjugatePair.graphAut_map_sylowCenter]
  obtain ⟨z,hz,he⟩ := hh
  have hh := congrArg a.symm he
  simp only [MulEquiv.coe_toMonoidHom,a.symm_apply_apply,map_mul,map_inv] at hh
  exact hh ▸ hz

/-- An involution in the native Sylow is conjugated into its center by an
actual element of one of the two parabolics. -/
theorem involution_parabolic_conjugate_center (x : unipotent (F := F)) (hx : x^2=1) :
    ∃ g : Sp F, (g ∈ pointParabolic ∨ g ∈ planeParabolic) ∧
      ∃ z : unipotent (F := F), z ∈ center (unipotent (F := F)) ∧
        g*x.val*g⁻¹=z.val := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have hbv : b*v=0 := by
    rw [element_square,←element_zero,theta,element_eq_iff] at hx
    exact hx.2.2.1
  have hp : (element b u w v).val ∈ SymplecticConjugatePair.pointRadical ∨
      (element b u w v).val ∈ SymplecticConjugatePair.planeRadical := by
    rcases mul_eq_zero.mp hbv with rfl | rfl
    · right
      rw [SymplecticConjugatePair.planeRadical_eq_wing]
      exact mem_map_of_mem _ ((element_mem_wing true _ _ _ _).mpr rfl)
    · left
      rw [SymplecticConjugatePair.pointRadical_eq_wing]
      exact mem_map_of_mem _ ((element_mem_wing false _ _ _ _).mpr rfl)
  rcases hp with hp | hp
  · obtain ⟨g,hg,z,hz,he⟩ := point_conjugate_center _ hp
    exact ⟨g,Or.inl hg,z,hz,he.symm⟩
  · obtain ⟨g,hg,z,hz,he⟩ := plane_conjugate_center _ hp
    exact ⟨g,Or.inr hg,z,hz,he.symm⟩
end Theory.SpecificGroups.SymplecticFour.SourceFusionOrder
