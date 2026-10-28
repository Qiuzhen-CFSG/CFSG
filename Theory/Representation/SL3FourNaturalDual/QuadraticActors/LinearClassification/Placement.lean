module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.Coordinates
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.RootPlane
public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.Displacements
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Placing quadratic actors in a root plane

The common-image-line branch of the displacement flag is put on the first
coordinate axis by extending an isomorphism of one-dimensional subspaces.
Quadraticity fixes this axis, so the conjugated matrices lie in the literal
root plane. In the common-fixed-hyperplane branch, inverse transpose has
its common image in the one-dimensional annihilator. Interchanging the
natural and dual summands supplies its equivariant coordinates. Recovering
the binary parameters then gives an equality of actual subgroups.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open Matrix BinaryOffender

/-- Recover the binary parameter space of a subgroup lying in a root plane. -/
def parameters (B : Subgroup SL) : Submodule (ZMod 2) (F × F) where
  carrier := {p | plane p ∈ B}
  zero_mem' := by
    change plane 0 ∈ B
    simpa only [plane_zero] using B.one_mem
  add_mem' {p q} hp hq := by
    change plane (p + q) ∈ B
    rw [plane_add]
    exact B.mul_mem hp hq
  smul_mem' a p hp := by
    change plane p ∈ B at hp
    fin_cases a
    · change plane ((0 : ZMod 2) • p) ∈ B
      simpa only [zero_smul, plane_zero] using B.one_mem
    · change plane ((1 : ZMod 2) • p) ∈ B
      simpa only [one_smul] using hp

lemma planeActor_parameters (B : Subgroup SL) (hB : ∀ g ∈ B, ∃ p, plane p = g) :
    planeActor (parameters B) = B := by
  ext g
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hg
    obtain ⟨p, rfl⟩ := hB g hg
    exact ⟨p, hg, rfl⟩

private lemma coordinates_of_nonzero (x : W) (hx : x ≠ 0) :
    ∃ e : W ≃ₗ[F] W, e x = ![1, 0, 0] := by
  have hz : (![1, 0, 0] : W) ≠ 0 := by
    intro h
    exact one_ne_zero (congrFun h 0)
  let ex := LinearEquiv.toSpanNonzeroSingleton F W x hx
  let ez := LinearEquiv.toSpanNonzeroSingleton F W ![1, 0, 0] hz
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ez)
  refine ⟨e, ?_⟩
  have h := he (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ez] using h.symm

private lemma plane_of_axis_and_tail (g : SL)
    (haxis : g.val.mulVec ![1, 0, 0] = ![1, 0, 0])
    (htail : ∀ w : W, (g.val.mulVec w) 1 = w 1 ∧ (g.val.mulVec w) 2 = w 2) :
    plane (g 0 1, g 0 2) = g := by
  have h00 : g 0 0 = 1 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun haxis 0
  have h1 (j : Fin 3) : g 1 j = (Pi.single j (1 : F) : W) 1 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using (htail (Pi.single j 1)).1
  have h2 (j : Fin 3) : g 2 j = (Pi.single j (1 : F) : W) 2 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using (htail (Pi.single j 1)).2
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [plane, h00, h1, h2]

/-- A one-dimensional common image, contained in the common fixed space,
puts every matrix in a single literal root plane. -/
theorem imageLine_placement (A : Subgroup SL) (hq : IsQuadratic representation A)
    (hline : Module.finrank F (naturalMoved A) = 1) :
    ∃ (e : W ≃ₗ[F] W) (D : Submodule (ZMod 2) (F × F)),
      A.map (coordinateAut e).toMonoidHom = planeActor D := by
  have hne : naturalMoved A ≠ ⊥ := Submodule.one_le_finrank_iff.mp (by omega)
  obtain ⟨x, hx, hxn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hspan : naturalMoved A = Submodule.span F {x} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hline hx hxn
  obtain ⟨e, he⟩ := coordinates_of_nonzero x hxn
  have hmatrix (a : A) : ∃ p, plane p = coordinateAut e a := by
    have hfix : a.val.val.mulVec x = x := by
      have hf := naturalFixed_le_ker A a (naturalMoved_le_naturalFixed A hq hx)
      exact sub_eq_zero.mp hf
    have haxis : (coordinateAut e a).val.mulVec ![1, 0, 0] = ![1, 0, 0] := by
      rw [← he, coordinateAut_natural, e.symm_apply_apply, hfix]
    have htail : ∀ w : W, ((coordinateAut e a).val.mulVec w) 1 = w 1 ∧
        ((coordinateAut e a).val.mulVec w) 2 = w 2 := by
      intro w
      have hm : naturalDisplacement a (e.symm w) ∈ Submodule.span F {x} := by
        rw [← hspan]
        exact range_le_naturalMoved A a ⟨e.symm w, rfl⟩
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
      have hd : (coordinateAut e a).val.mulVec w - w = c • ![1, 0, 0] := by
        calc
          (coordinateAut e a).val.mulVec w - w = e (naturalDisplacement a (e.symm w)) := by
            rw [coordinateAut_natural]
            change e (a.val.val.mulVec (e.symm w)) - w =
              e (a.val.val.mulVec (e.symm w) - e.symm w)
            rw [map_sub, e.apply_symm_apply]
          _ = c • ![1, 0, 0] := by rw [← hc, map_smul, he]
      constructor
      · apply sub_eq_zero.mp
        simpa using congrFun hd 1
      · apply sub_eq_zero.mp
        simpa using congrFun hd 2
    exact ⟨_, plane_of_axis_and_tail _ haxis htail⟩
  refine ⟨e, parameters (A.map (coordinateAut e).toMonoidHom), ?_⟩
  apply (planeActor_parameters _ ?_).symm
  rintro g ⟨a, ha, rfl⟩
  exact hmatrix ⟨a, ha⟩

/-- Inverse transpose as an actual automorphism, with the interchange of
natural and dual summands as its intertwiner. -/
def graphAut : SL ≃* SL where
  toFun := Matrix.SpecialLinearGroup.inverseTranspose
  invFun := Matrix.SpecialLinearGroup.inverseTranspose
  left_inv := inverseTranspose_involutive
  right_inv := inverseTranspose_involutive
  map_mul' := map_mul Matrix.SpecialLinearGroup.inverseTranspose

lemma graphAut_equivariant (g : SL) (v : V) :
    graphSwap (representation g v) = representation (graphAut g) (graphSwap v) :=
  graphSwap_equivariant g v

/-- The annihilator, expressed as coordinate covectors in the natural carrier. -/
def coordinateAnnihilator (C : Submodule F W) : Submodule F W :=
  C.dualAnnihilator.map (dotProductEquiv F (Fin 3)).symm.toLinearMap

lemma mem_coordinateAnnihilator (C : Submodule F W) (w : W) :
    w ∈ coordinateAnnihilator C ↔ ∀ x ∈ C, w ⬝ᵥ x = 0 := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩ x hx
    have h : dotProductEquiv F (Fin 3) ((dotProductEquiv F (Fin 3)).symm φ) x = 0 := by
      rw [LinearEquiv.apply_symm_apply]
      exact (Submodule.mem_dualAnnihilator _).mp hφ x hx
    exact h
  · intro h
    refine ⟨dotProductEquiv F (Fin 3) w, ?_, LinearEquiv.symm_apply_apply _ w⟩
    exact (Submodule.mem_dualAnnihilator _).mpr h

lemma coordinateAnnihilator_finrank (C : Submodule F W) :
    Module.finrank F (coordinateAnnihilator C) = Module.finrank F (W ⧸ C) := by
  have he := (Submodule.equivMapOfInjective (dotProductEquiv F (Fin 3)).symm.toLinearMap
    (dotProductEquiv F (Fin 3)).symm.injective C.dualAnnihilator).finrank_eq
  have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq C
  have hq := C.finrank_quotient_add_finrank
  change Module.finrank F C.dualAnnihilator = Module.finrank F (coordinateAnnihilator C) at he
  omega

/-- Inverse transpose turns a common fixed hyperplane into a common image
line, using the actual annihilator pairing. -/
lemma graph_naturalMoved_le (A : Subgroup SL) :
    naturalMoved (A.map graphAut.toMonoidHom) ≤ coordinateAnnihilator (naturalFixed A) := by
  apply iSup_le
  rintro ⟨g, hg⟩
  obtain ⟨a, ha, rfl⟩ := hg
  rintro _ ⟨w, rfl⟩
  apply (mem_coordinateAnnihilator _ _).mpr
  intro x hx
  have hf := naturalFixed_le_ker A ⟨a⁻¹, A.inv_mem ha⟩ hx
  have hfix : (a⁻¹).val.mulVec x = x := sub_eq_zero.mp hf
  change ((a⁻¹).val.transpose.mulVec w - w) ⬝ᵥ x = 0
  rw [sub_dotProduct, dotProduct_comm ((a⁻¹).val.transpose.mulVec w) x,
    Matrix.dotProduct_transpose_mulVec, hfix, sub_self]

lemma graph_naturalMoved_finrank (A : Subgroup SL) (hA : A ≠ ⊥)
    (hC : Module.finrank F (W ⧸ naturalFixed A) = 1) :
    Module.finrank F (naturalMoved (A.map graphAut.toMonoidHom)) = 1 := by
  have hB : A.map graphAut.toMonoidHom ≠ ⊥ := by
    intro h
    apply hA
    apply Subgroup.map_injective (f := graphAut.toMonoidHom) graphAut.injective
    simpa only [Subgroup.map_bot] using h
  have hl : 1 ≤ Module.finrank F (naturalMoved (A.map graphAut.toMonoidHom)) :=
    Submodule.one_le_finrank_iff.mpr (naturalMoved_ne_bot _ hB)
  have hu := Submodule.finrank_mono (graph_naturalMoved_le A)
  rw [coordinateAnnihilator_finrank, hC] at hu
  omega

lemma graph_quadratic (A : Subgroup SL) (hq : IsQuadratic representation A) :
    IsQuadratic representation (A.map graphAut.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  obtain ⟨u, rfl⟩ := graphSwap.surjective v
  have h := congrArg graphSwap (hq a ha b hb u)
  simpa only [map_sub, graphAut_equivariant, MulEquiv.coe_toMonoidHom] using h

/-- Every nontrivial internal quadratic actor admits genuine equivariant
coordinates in a literal root plane. Both flag orientations are included. -/
theorem exists_rootPlane_coordinates (A : Subgroup SL) (hA : A ≠ ⊥)
    (hq : IsQuadratic representation A) :
    ∃ (f : SL ≃* SL) (E : V ≃ₗ[ZMod 2] V) (D : Submodule (ZMod 2) (F × F)),
      (∀ g v, E (representation g v) = representation (f g) (E v)) ∧
        A.map f.toMonoidHom = planeActor D := by
  rcases natural_flag_dichotomy A hA hq with hline | hplane
  · obtain ⟨e, D, hD⟩ := imageLine_placement A hq hline
    exact ⟨coordinateAut e, coordinateChange e, D, coordinateChange_equivariant e, hD⟩
  · obtain ⟨e, D, hD⟩ := imageLine_placement (A.map graphAut.toMonoidHom)
      (graph_quadratic A hq) (graph_naturalMoved_finrank A hA hplane)
    refine ⟨graphAut.trans (coordinateAut e), graphSwap.trans (coordinateChange e), D, ?_, ?_⟩
    · intro g v
      change coordinateChange e (graphSwap (representation g v)) = _
      rw [graphAut_equivariant, coordinateChange_equivariant]
      rfl
    · rw [Subgroup.map_map] at hD
      exact hD

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
