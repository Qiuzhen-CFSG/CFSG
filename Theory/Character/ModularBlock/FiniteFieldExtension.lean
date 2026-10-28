module

public import Theory.Character.ModularBlock.GaloisOrbitMeet

/-!
# Primitivity of augmentation-one idempotents under finite field extension

A centrally primitive group-algebra idempotent with augmentation one remains
primitive after extending to a finite field. For a nonzero central factor,
its augmentation is zero or one. In the zero case, the Galois orbit product
of its complement has augmentation one and descends to the primitive source,
forcing the factor to vanish. In the one case, the orbit product of the
factor descends and equals the whole source idempotent, forcing equality.

Ported from the MainTheorem section of
`c3503435:glauberman_zStar/Submission/ZStar/FiniteFieldPrimitivity.lean`.
This generic result supports primitivity of compatible local principal blocks.
It uses the shared central-primitivity predicate and actual augmentation.
-/

public section
noncomputable section
namespace ModularBlock.FiniteFieldPrimitivity
attribute [local instance] Fintype.ofFinite
open scoped BigOperators

section MainTheorem

variable (k K : Type*) [Field k] [Field K] [Finite K]
variable [Algebra k K]
variable (H : Type*) [Group H]

/-- An augmentation-one centrally primitive idempotent in a finite-field
group algebra stays centrally primitive after extending to any finite field. -/
theorem map_isCentrallyPrimitive_of_augmentation_eq_one
    (e : MonoidAlgebra k H)
    (hprimitive : IsCentrallyPrimitive e)
    (haugmentation : groupAlgebraAugmentation k H e = 1) :
    IsCentrallyPrimitive
      (MonoidAlgebra.mapRingHom H (algebraMap k K) e) := by
  classical
  let E := MonoidAlgebra.mapRingHom H (algebraMap k K) e
  have hEcenter : E ∈ Set.center (MonoidAlgebra K H) :=
    groupAlgebra_mapRingHom_mem_center (algebraMap k K) e hprimitive.1
  have hEidem : IsIdempotentElem E := by
    change MonoidAlgebra.mapRingHom H (algebraMap k K) e *
        MonoidAlgebra.mapRingHom H (algebraMap k K) e =
      MonoidAlgebra.mapRingHom H (algebraMap k K) e
    rw [← map_mul, hprimitive.2.1]
  have hEaugmentation :
      groupAlgebraAugmentation K H E = 1 := by
    change groupAlgebraAugmentation K H
      (MonoidAlgebra.mapRingHom H (algebraMap k K) e) = 1
    rw [groupAlgebraAugmentation_mapRingHom, haugmentation, map_one]
  have hEne : E ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hEaugmentation
    exact zero_ne_one hEaugmentation
  have hEfixed : ∀ σ : K ≃ₐ[k] K, conjugate k K H σ E = E := by
    intro σ
    exact conjugate_algebraMap k K H σ e
  refine ⟨hEcenter, hEidem, hEne, ?_⟩
  intro f hfcenter hfid hfactor hfne
  let Ez : Subring.center (MonoidAlgebra K H) := ⟨E, hEcenter⟩
  let fz : Subring.center (MonoidAlgebra K H) := ⟨f, hfcenter⟩
  have hEf : E * f = f := by
    calc
      E * f = f * E := (Semigroup.mem_center_iff.mp hEcenter f).symm
      _ = f := hfactor
  have haugIdem : IsIdempotentElem
      (groupAlgebraAugmentation K H f) := by
    change groupAlgebraAugmentation K H f *
        groupAlgebraAugmentation K H f =
      groupAlgebraAugmentation K H f
    rw [← map_mul, hfid]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp haugIdem with haug0 | haug1
  · let cz : Subring.center (MonoidAlgebra K H) := Ez - fz
    have hcid : IsIdempotentElem cz.1 := by
      change IsIdempotentElem (E - f)
      exact hfid.sub hEidem hfactor hEf
    have hcfactor : cz.1 * E = cz.1 := by
      change (E - f) * E = E - f
      rw [sub_mul, hEidem, hfactor]
    have hcaug : groupAlgebraAugmentation K H cz.1 = 1 := by
      change groupAlgebraAugmentation K H (E - f) = 1
      rw [map_sub, hEaugmentation, haug0, sub_zero]
    let nz : Subring.center (MonoidAlgebra K H) := orbitMeet k K H cz
    have hnfixed : ∀ σ : K ≃ₐ[k] K,
        conjugate k K H σ nz.1 = nz.1 := by
      intro σ
      exact orbitMeet_fixed k K H σ cz
    have hnidem : IsIdempotentElem nz.1 :=
      orbitMeet_isIdempotent k K H cz hcid
    have hnfactor : nz.1 * E = nz.1 :=
      orbitMeet_factor k K H Ez cz hEidem hEfixed hcfactor
    have hnne : nz.1 ≠ 0 :=
      orbitMeet_ne_zero_of_augmentation_eq_one k K H cz hcaug
    have hneq : nz.1 = E :=
      fixed_central_idempotent_factor_eq_map_of_source_primitive
        k K H e hprimitive nz.1 hnfixed nz.2 hnidem hnfactor hnne
    have hfzero : f * nz.1 = 0 := by
      exact original_mul_orbitMeet_sub_eq_zero k K H Ez fz hfid hfactor
    rw [hneq] at hfzero
    exact (hfne (hfactor.symm.trans hfzero)).elim
  · let mz : Subring.center (MonoidAlgebra K H) := orbitMeet k K H fz
    have hmfixed : ∀ σ : K ≃ₐ[k] K,
        conjugate k K H σ mz.1 = mz.1 := by
      intro σ
      exact orbitMeet_fixed k K H σ fz
    have hmidem : IsIdempotentElem mz.1 :=
      orbitMeet_isIdempotent k K H fz hfid
    have hmfactor : mz.1 * E = mz.1 :=
      orbitMeet_factor k K H Ez fz hEidem hEfixed hfactor
    have hmne : mz.1 ≠ 0 :=
      orbitMeet_ne_zero_of_augmentation_eq_one k K H fz haug1
    have hmeq : mz.1 = E :=
      fixed_central_idempotent_factor_eq_map_of_source_primitive
        k K H e hprimitive mz.1 hmfixed mz.2 hmidem hmfactor hmne
    have hmulf : mz.1 * f = mz.1 :=
      orbitMeet_mul_original k K H fz hfid
    rw [hmeq] at hmulf
    exact hEf.symm.trans hmulf

end MainTheorem


end ModularBlock.FiniteFieldPrimitivity

