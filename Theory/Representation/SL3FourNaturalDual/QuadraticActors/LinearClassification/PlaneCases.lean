module

public import Theory.Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification.Codimension

/-!
# Numerical classification inside a root plane

The F₄-span of a nonzero binary parameter space has dimension one or two.
The exact fixed-codimension formula and the small-codimension inequality
force the line case to be the full binary rank-two root group. In the plane
case they force rank at least three, so simultaneous parameter coordinates
supply a full root and an independent root. Every alternative carries a
`LinearMarking` with its intertwining equation.

Source: Aschbacher--Smith, proof of 13.8.20, printed p.955 (PDF p.972).
-/

@[expose] public section
noncomputable section
namespace Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
open BinaryOffender

lemma parameterSpan_ne_bot (D : Submodule (ZMod 2) (F × F)) (hD : D ≠ ⊥) :
    parameterSpan D ≠ ⊥ := by
  intro h
  apply hD
  apply le_bot_iff.mp
  intro p hp
  have hs : p ∈ parameterSpan D := Submodule.subset_span hp
  simpa only [h, Submodule.mem_bot] using hs

lemma binary_le_parameterSpan (D : Submodule (ZMod 2) (F × F)) :
    D ≤ (parameterSpan D).restrictScalars (ZMod 2) :=
  fun _ hp => Submodule.subset_span hp

lemma parameterSpan_binary_finrank (D : Submodule (ZMod 2) (F × F)) :
    Module.finrank (ZMod 2) ((parameterSpan D).restrictScalars (ZMod 2)) =
      2 * Module.finrank F (parameterSpan D) := by
  exact (Module.finrank_mul_finrank (ZMod 2) F (parameterSpan D)).symm.trans
    (congrArg (fun n => n * Module.finrank F (parameterSpan D)) finrank_field)

lemma root_marking_of_full_line (D : Submodule (ZMod 2) (F × F)) (p : F × F)
    (hp : p ≠ 0) (hline : ∀ a : F, a • p ∈ D) :
    ∃ m : LinearMarking representation, ∀ a : F, m.actor (root a) ∈ planeActor D := by
  have hproper : Submodule.span F {p} ≠ ⊤ := by
    intro h
    have hd := finrank_span_singleton (K := F) hp
    rw [h, finrank_top] at hd
    simp [Module.finrank_prod] at hd
  obtain ⟨q, hq⟩ := SetLike.exists_not_mem_of_ne_top (Submodule.span F {p}) hproper
  obtain ⟨e, he, _⟩ := coordinates_of_independent p q hp hq
  refine ⟨coordinateMarking (parameterChange e), ?_⟩
  intro a
  change (coordinateAut (parameterChange e)).symm (root a) ∈ planeActor D
  have h : (coordinateAut (parameterChange e)).symm (root a) = plane (a • p) := by
    apply (coordinateAut (parameterChange e)).injective
    rw [MulEquiv.apply_symm_apply, coordinateAut_plane, map_smul, he]
    simp only [Prod.smul_mk, smul_eq_mul, mul_zero, mul_one, plane_root]
  rw [h]
  exact (mem_planeActor D _).mpr (hline a)

/-- Complete classification once the actor has been placed in the literal
root plane. No marking or numerical alternative is assumed. -/
theorem criticalShapes_planeActor (D : Submodule (ZMod 2) (F × F))
    (hD : D ≠ ⊥)
    (hsmall : fixedCodim representation (planeActor D) ≤ 2 * rank (planeActor D))
    (hrank : rank (planeActor D) ≤ 4) : CriticalShapes representation (planeActor D) := by
  have hc := fixedCodim_planeActor D hD
  have hl : 1 ≤ Module.finrank F (parameterSpan D) :=
    Submodule.one_le_finrank_iff.mpr (parameterSpan_ne_bot D hD)
  have hu : Module.finrank F (parameterSpan D) ≤ 2 := by
    simpa only [Module.finrank_prod, Module.finrank_self] using (parameterSpan D).finrank_le
  by_cases hdim : Module.finrank F (parameterSpan D) = 1
  · have hbound := Submodule.finrank_mono (binary_le_parameterSpan D)
    rw [parameterSpan_binary_finrank, hdim] at hbound
    have hr : rank (planeActor D) = 2 := by rw [planeActor_rank] at *; omega
    have hfull : D = (parameterSpan D).restrictScalars (ZMod 2) :=
      Submodule.eq_of_le_of_finrank_eq (binary_le_parameterSpan D) (by
        rw [parameterSpan_binary_finrank, hdim, ← planeActor_rank, hr])
    obtain ⟨p, hp, hpn⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    have hline : ∀ a : F, a • p ∈ D := by
      intro a
      rw [hfull]
      exact (parameterSpan D).smul_mem a (Submodule.subset_span hp)
    exact Or.inl ⟨hr, by omega, root_marking_of_full_line D p hpn hline⟩
  · have hdim2 : Module.finrank F (parameterSpan D) = 2 := by omega
    have hc6 : fixedCodim representation (planeActor D) = 6 := by omega
    have hr3 : 3 ≤ rank (planeActor D) := by omega
    exact Or.inr ⟨hr3, hrank, hc6, Or.inl (planeActor_marking D
      (by rwa [planeActor_rank] at hr3))⟩

end Representation.SL3FourNaturalDual.QuadraticActors.LinearClassification
