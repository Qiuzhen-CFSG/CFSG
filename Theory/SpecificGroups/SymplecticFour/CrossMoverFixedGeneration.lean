module
public import Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
public import Theory.SpecificGroups.SymplecticFour.LargePlaneGeneration

/-!
# Root selection with opposite plane radicals

Align the critical long root by an element preserving its containing plane.
The cross-mover root calculation then uses the same conjugator as a pair
of opposite plane radicals. The latter pair generates the whole symplectic
group, so its common fixed subgroup on any full cover is ambient-fixed.

The actual quotient-kernel lift and individual-mover application are in
NonbinarySymplectic.CriticalReduction.CrossFixedSelection. This proves the
root-case fixed-layer step of MS93 (5.5)(b), printed pp.915--917; generation
by individual unequal movers and the exception in (c) are separate claims.
-/

public noncomputable section
open Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
open CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- For a full root in the original plane, one conjugator gives both
cross-mover generation and generation by the two full plane radicals. -/
theorem exists_cross_mover_plane_root_selector (hq : 2 < Nat.card F)
    (J E : Subgroup (unipotent (F := F))) [J.Normal]
    (hc : Nat.card F^2 ≤ Nat.card J)
    (hm : SmallMovers.movingIndex J ≤ Nat.card F^2)
    (hJE : J ≤ E) (hout : ¬ E ≤ wing true)
    (A : Subgroup (Sp F))
    (hAP : A ≤ (wing true).map unipotent.subtype)
    (hcA : Nat.card A = Nat.card F)
    (hdA : Module.finrank F (displacementSpace A) = 1) :
    let P := (wing true).map (unipotent (F := F)).subtype
    ∃ g : Sp F, ((E.map unipotent.subtype).map (MulAut.conj g).toMonoidHom ⊔ A = ⊤) ∧
      P.map (MulAut.conj g).toMonoidHom ⊔ P = ⊤ := by
  dsimp only
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let P := (wing true).map (unipotent (F := F)).subtype
  have hgen := cross_mover_long_root_generate hq J E hc hm hJE hout
  obtain ⟨h,hP,hh⟩ := SelectedPositioning.plane_root_coordinates P A
    ⟨1,by rw [show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext y; simp,Subgroup.map_id]⟩
    hAP hcA hdA
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
  have hmaps (B : Subgroup (Sp F)) (g h : Sp F) :
      (B.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
        B.map (MulAut.conj (g*h)).toMonoidHom := by
    rw [Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hAc : A.map (MulAut.conj c).toMonoidHom = RootSubgroup.group 1 := by
    rw [←hmaps,hh,h01]
  refine ⟨c⁻¹,?_,?_⟩
  · apply Subgroup.map_injective (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective
    rw [Subgroup.map_sup,hmaps,hAc,mul_inv_cancel,show (MulAut.conj (1 : Sp F)).toMonoidHom = MonoidHom.id _ by ext y; simp,Subgroup.map_id,hgen]
    rw [←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (MulAut.conj c).surjective]
  · have hplane : P.map (MulAut.conj o).toMonoidHom ⊔ P = ⊤ := by
      rw [show P = SymplecticConjugatePair.planeRadical from
        SymplecticConjugatePair.planeRadical_eq_wing.symm]
      apply LargePlaneGeneration.opposite_plane_large_subactor_generate _ le_rfl
      rw [SymplecticConjugatePair.card_planeRadical]
      nlinarith [Nat.zero_le (Nat.card F * (Nat.card F - 1)^2)]
    apply Subgroup.map_injective (f := (MulAut.conj h).toMonoidHom) (MulAut.conj h).injective
    rw [Subgroup.map_sup,hmaps,hP]
    have hhc : h*c⁻¹=o := by dsimp [c,o]; rw [mul_inv_rev, mul_inv_cancel_left,TwoConjugate.opposition_inv]
    rw [hhc,hplane,map_top_of_surjective _ (MulAut.conj h).surjective]

end Theory.SpecificGroups.SymplecticFour.CrossMoverGeneration
