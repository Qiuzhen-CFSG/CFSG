module

public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Standard
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual.Weyl
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary

/-!
# Solvable residuals of symplectic root normalizers

For every standard root subgroup in Sp₄(F), the full normalizer is proper.
When F has characteristic two and order 2ⁿ with n > 1, the solvable residual
computed inside that normalizer, embedded back into Sp₄(F), is exactly the
full ambient centralizer of the root subgroup.

Explicit Weyl conjugation reduces the calculation to roots 0 and 4. Their
normalizers and centralizers are the point and plane parabolics and their
respective determinant kernels. The nonbinary local-structure theorems identify
those kernels with the embedded parabolic residuals. Transport uses the actual
isomorphisms on subgroups and their inclusion maps.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed p.250 (PDF p.261), the intrinsic matrix-root calculation used in its proof.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual

private theorem centralizer_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (R : Subgroup A) :
    (centralizer (R : Set A)).map e.toMonoidHom =
      centralizer (R.map e.toMonoidHom : Set B) := by
  ext b
  simp only [mem_map_equiv, mem_centralizer_iff]
  constructor
  · intro h a ha
    apply e.symm.injective
    simpa only [map_mul] using h (e.symm a) (mem_map_equiv.mp ha)
  · intro h a ha
    have he := h (e a) (by simpa)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using congrArg e.symm he

private theorem residual_map_equiv {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (P : Subgroup A) :
    ((solvableResidual P).map P.subtype).map (e : A →* B) =
      (solvableResidual (P.map (e : A →* B))).map (P.map (e : A →* B)).subtype := by
  have he : (P.map (e : A →* B)).subtype.comp (e.subgroupMap P).toMonoidHom =
      (e : A →* B).comp P.subtype := by
    ext x
    rfl
  rw [map_map, ← he, ← map_map,
    map_solvableResidual_eq _ (e.subgroupMap P).surjective]

private theorem proper_normalizer_map {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (R : Subgroup A) (hR : normalizer (R : Set A) ≠ ⊤) :
    normalizer (R.map e.toMonoidHom : Set B) ≠ ⊤ := by
  intro h
  apply hR
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_equiv_normalizer_eq, h, map_top_of_surjective _ e.surjective]

private theorem residual_centralizer_map {A B : Type*} [Group A] [Group B] [Finite A]
    (e : A ≃* B) (R : Subgroup A)
    (hR : (solvableResidual (normalizer (R : Set A))).map
      (normalizer (R : Set A)).subtype = centralizer (R : Set A)) :
    (solvableResidual (normalizer (R.map e.toMonoidHom : Set B))).map
      (normalizer (R.map e.toMonoidHom : Set B)).subtype =
        centralizer (R.map e.toMonoidHom : Set B) := by
  rw [← map_equiv_normalizer_eq]
  calc
    _ = ((solvableResidual (normalizer (R : Set A))).map
        (normalizer (R : Set A)).subtype).map e.toMonoidHom :=
      (residual_map_equiv e (normalizer (R : Set A))).symm
    _ = _ := by rw [hR, centralizer_map]

variable {F : Type*} [Field F] [CharP F 2]

/-- The full normalizer of every matrix root subgroup is proper. -/
theorem normalizer_ne_top (r : Fin 8) :
    normalizer (RootSubgroup.group (F := F) r : Set (Sp F)) ≠ ⊤ := by
  obtain ⟨w, he⟩ := exists_root_conjugation (F := F) r
  rw [← he]
  apply proper_normalizer_map
  split_ifs
  · rw [normalizer_zero_eq]
    exact pointParabolic_ne_top
  · rw [normalizer_four_eq]
    exact planeParabolic_ne_top

variable [Finite F] {n : ℕ}

/-- The embedded solvable residual of a root normalizer is its full ambient root centralizer. -/
theorem solvableResidual_eq_centralizer (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
    (r : Fin 8) :
    (solvableResidual (normalizer (RootSubgroup.group (F := F) r : Set (Sp F)))).map
      (normalizer (RootSubgroup.group (F := F) r : Set (Sp F))).subtype =
        centralizer (RootSubgroup.group (F := F) r : Set (Sp F)) := by
  obtain ⟨w, he⟩ := exists_root_conjugation (F := F) r
  split_ifs at he
  · rw [← he]
    apply residual_centralizer_map
    rw [normalizer_zero_eq, centralizer_zero_eq]
    exact pointParabolic_solvableResidual_eq hcard hn
  · rw [← he]
    apply residual_centralizer_map
    rw [normalizer_four_eq, centralizer_four_eq]
    exact planeParabolic_solvableResidual_eq hcard hn
end Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual
