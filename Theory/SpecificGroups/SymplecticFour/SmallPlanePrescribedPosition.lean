module
public import Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration
import all Theory.SpecificGroups.SymplecticFour.SmallPlaneGeneration

/-!
# The same small-plane selector with both plane positions

The witnesses are reconstructed from the original plane/root coordinates,
the original plane-preserving shear, and the standard root-plane selector.
One coordinate sends the original plane to the opposite standard plane and
the selected conjugate to the upper plane. The original root and its selected
conjugate retain their exact first and third lower-root images.

Source: MS93 (5.6)(b--d), printed pp.917--918; the plane-position information
is retained for the prescribed full-root actors in (5.12)(3), printed p.927.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.SmallPlanePrescribedPosition
open CentralRootGeometry SmallPlaneGeneration
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

/-- The original selector, including both plane positions in one coordinate. -/
theorem exists_subplane_root_generators_positioned (hF : 2 < Nat.card F)
    (P E A : Subgroup (Sp F))
    (hP : ∃ k : Sp F, P.map (MulAut.conj k).toMonoidHom =
      (wing true).map (unipotent (F := F)).subtype)
    (hEP : E ≤ P) (hAE : A ≤ E) (hcE : Nat.card F < Nat.card E)
    (hcA : Nat.card A = Nat.card F)
    (hdA : Module.finrank F (displacementSpace A) = 1) :
    ∃ g x c : Sp F,
      (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔
        A.map (MulAut.conj x).toMonoidHom = ⊤ ∧
      (P.map (MulAut.conj g).toMonoidHom ⊔
        (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = ⊤) ∧
      x ∈ normalizer (P : Set (Sp F)) ∧
      P.map (MulAut.conj c).toMonoidHom =
        ((wing true).map (unipotent (F := F)).subtype).map
          (MulAut.conj (TwoConjugate.opposition (F := F))).toMonoidHom ∧
      (P.map (MulAut.conj g).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        (wing true).map (unipotent (F := F)).subtype ∧
      A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 ∧
      (A.map (MulAut.conj x).toMonoidHom).map (MulAut.conj c).toMonoidHom =
        RootSubgroup.group 3 := by
  obtain ⟨h,hh,ha⟩ := SelectedPositioning.plane_root_coordinates P A hP (hAE.trans hEP) hcA hdA
  obtain ⟨k,hk,hgen⟩ := exists_plane_preserving_three_roots hF
    (E.map (MulAut.conj h).toMonoidHom) (hh ▸ map_mono hEP)
    (ha ▸ map_mono hAE) (by rwa [card_map_of_injective (MulAut.conj h).injective])
  obtain ⟨x₀,hroot,hpair,hpos⟩ := SelectedPlaneGeneration.exists_standard_root_plane_selector (F := F)
  let o := TwoConjugate.opposition (F := F)
  let c := o*h
  have h01 : (RootSubgroup.group (F := F) 0).map (MulAut.conj o).toMonoidHom =
      RootSubgroup.group 1 := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hz
      change o * rootElement 0 t * o⁻¹ ∈ _
      rw [(TwoConjugate.opposition_central_axes t).1]
      exact subset_closure ⟨t,rfl⟩
    · intro hy
      obtain ⟨t,rfl⟩ := (RootSubgroup.mem_group_iff _ _).mp hy
      exact ⟨rootElement 0 t,subset_closure ⟨t,rfl⟩,(TwoConjugate.opposition_central_axes t).1⟩
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←map_conj_mul,ha,h01]
  have htop : (⊤ : Subgroup (Sp F)).map (MulAut.conj c).toMonoidHom = ⊤ :=
    map_top_of_surjective _ (MulAut.conj c).surjective
  refine ⟨c⁻¹*(k*h),c⁻¹*x₀*c,c,?_,?_,?_,?_,?_,hAc,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_conj_mul,map_conj_mul,hAc,htop]
    rw [show c*(c⁻¹*(k*h))=k*h by group,
      show c*(c⁻¹*x₀*c)=x₀*c by group,←map_conj_mul A x₀ c,hAc,hroot,←map_conj_mul E k h]
    exact hgen
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,map_conj_mul,map_conj_mul,map_conj_mul,htop]
    rw [show c*(c⁻¹*(k*h))=k*h by group,
      show c*(c⁻¹*x₀*c)⁻¹*(c⁻¹*(k*h))=x₀⁻¹*(k*h) by group,
      ←map_conj_mul P x₀⁻¹ (k*h),←map_conj_mul P k h,hh,hk]
    exact hpair
  · rw [mem_normalizer_iff_map_conj_eq]
    change P.map (MulAut.conj (c⁻¹*x₀*c)).toMonoidHom = P
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [map_conj_mul,hh]
    have heq : h*(c⁻¹*x₀*c)=(o⁻¹*x₀*o)*h := by dsimp [c]; group
    rw [heq,←map_conj_mul,hh]
    exact mem_normalizer_iff_map_conj_eq.mp hpos

  · change P.map (MulAut.conj (o*h)).toMonoidHom = _
    rw [←map_conj_mul,hh]
  · rw [map_conj_mul,show c*(c⁻¹*(k*h))=k*h by group,←map_conj_mul,hh,hk]
  · rw [map_conj_mul,show c*(c⁻¹*x₀*c)=x₀*c by group,←map_conj_mul,hAc,hroot]

end Theory.SpecificGroups.SymplecticFour.SmallPlanePrescribedPosition
