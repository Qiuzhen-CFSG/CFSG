module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.Actors.FixedBounds.Catalogue

/-!
# Displacement certificates bound the literal common fixed space

Selected displacement rows vanish on every common fixed quotient class.
A right inverse makes those equations surjective, hence they descend to a
surjection from the quotient by the common fixed space. This proves the
required lower bound on fixed codimension without identifying fixed classes
with ordinary matrix centralizers.

Source: Guralnick–Malle Lemma 4.5 and Proposition 4.8 step 3A.
-/

set_option backward.isDefEq.respectTransparency false
public section
open Representation Representation.BinaryOffender Matrix
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds

theorem catalogueSubgroup_le_standardActors (i : Fin 60) :
    catalogueSubgroup i ≤ standardActors := by
  apply (Subgroup.closure_le standardActors).2
  rintro _ ⟨c, _, rfl⟩
  exact codeActor_mem_standardActors c

/-- The selected equations come from the actual generators of each subgroup. -/
theorem selectedRow_mem : ∀ (i : Fin 60) (j : Fin (certificateSize i)),
    (selectedRow i j).1 ∈ catalogueGenerators i := by
  decide

private theorem codim_ge_of_equations {V W : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
    (C : Submodule (ZMod 2) V) (D : V →ₗ[ZMod 2] W)
    (hker : C ≤ D.ker) (hs : Function.Surjective D) :
    Module.finrank (ZMod 2) W ≤ Module.finrank (ZMod 2) (V ⧸ C) := by
  apply LinearMap.finrank_le_finrank_of_surjective (f := C.liftQ D hker)
  intro w
  obtain ⟨v, hv⟩ := hs w
  exact ⟨C.mkQ v, hv⟩

private theorem matrix_surjective_of_right_inverse {m n : ℕ}
    (D : Matrix (Fin m) (Fin n) (ZMod 2)) (Q : Matrix (Fin n) (Fin m) (ZMod 2))
    (h : D * Q = 1) : Function.Surjective D.mulVecLin := by
  intro w
  refine ⟨Q *ᵥ w, ?_⟩
  change D *ᵥ (Q *ᵥ w) = w
  rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]

/-- A checked right inverse supplies enough independent common-fixed-space
constraints on the literal quotient. -/
theorem certificateSize_le_fixedCodim (i : Fin 60)
    (hcert : displacementMatrix i * rightInverse i = 1) :
    certificateSize i ≤ fixedCodim (normalizerRepresentation adjoint) (catalogueSubgroup i) := by
  let C := fixedSpace (normalizerRepresentation adjoint) (catalogueSubgroup i)
  let D : Adjoint →ₗ[ZMod 2] (Fin (certificateSize i) → ZMod 2) :=
    (displacementMatrix i).mulVecLin.comp coordinateEquiv.toLinearMap
  have hker : C ≤ D.ker := by
    intro v hv
    change displacementMatrix i *ᵥ coordinateEquiv v = 0
    ext j
    have hmem : codeActor (selectedRow i j).1 ∈ catalogueSubgroup i :=
      Subgroup.subset_closure ⟨_, selectedRow_mem i j, rfl⟩
    have hfix : normalizerRepresentation adjoint (codeActor (selectedRow i j).1) v = v :=
      hv ⟨_, hmem⟩
    have hact : actMatrix (selectedRow i j).1 *ᵥ coordinateEquiv v = coordinateEquiv v := by
      rw [actMatrix_mulVec, coordinateEquiv.symm_apply_apply, hfix]
    change ((actMatrix (selectedRow i j).1 - 1) *ᵥ coordinateEquiv v) (selectedRow i j).2 = 0
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hact, sub_self]
    rfl
  have hs : Function.Surjective D :=
    (matrix_surjective_of_right_inverse _ _ hcert).comp coordinateEquiv.surjective
  have hd := codim_ge_of_equations C D hker hs
  change certificateSize i ≤ Module.finrank (ZMod 2) (Adjoint ⧸ C)
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using hd

theorem catalogue_gap_of_certificate (i : Fin 60)
    (hcert : displacementMatrix i * rightInverse i = 1) :
    2 * (catalogueGenerators i).length <
      fixedCodim (normalizerRepresentation adjoint) (catalogueSubgroup i) := by
  have h := certificateSize_le_fixedCodim i hcert
  unfold certificateSize at h
  omega

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement.Endpoint.FixedBounds
