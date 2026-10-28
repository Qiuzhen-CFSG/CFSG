module
public import Theory.GroupTheory.SylowNormalizerCentralQuotient
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SymmetricThreeTwoCore

/-!
# Sylow normalizers in central extensions of S3

Sylow two-subgroups of S3 are self-normalizing of index three. A central
kernel lies in every Sylow normalizer, and the relative Frattini argument
maps that normalizer onto the image normalizer. Thus its index stays three
in a central extension, including the literal S3 times C3 source model.

Source application: Aschbacher--Smith15.2.5, printed p.1107, second action row.
-/
public section
open Subgroup
namespace SymmetricThreeCentralNormalizer
theorem symmetricThree_normalizer_index (P : Sylow 2 (Equiv.Perm (Fin 3))) :
    (normalizer (P : Set (Equiv.Perm (Fin 3)))).index = 3 := by
  have hc : pCore 2 (Equiv.Perm (Fin 3)) = ⊥ := by
    have hh := ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by
        simp only [MonoidHom.ker_id]
        exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  let e := (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  rw [SymmetricThreeTwoCore.sylow_self_normalizing e P]
  exact SymmetricThreeTwoCore.sylow_index_three e P

theorem symmetricThree_central_normalizer_index
    {D : Type*} [Group D] [Finite D]
    (f : D →* Equiv.Perm (Fin 3)) (hf : Function.Surjective f)
    (hk : f.ker ≤ center D) (P : Sylow 2 D) :
    (normalizer (P : Set D)).index = 3 := by
  rw [← P.normalizer_comap_of_central_kernel f hf hk,
    index_comap_of_surjective _ hf]
  exact symmetricThree_normalizer_index _

theorem product_normalizer_index
    (P : Sylow 2 (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) :
    (normalizer (P : Set (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3)))).index = 3 := by
  apply symmetricThree_central_normalizer_index (MonoidHom.fst _ _)
    (fun x => ⟨(x,1),rfl⟩) ?_ P
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  rw [mem_center_iff]
  intro y
  apply Prod.ext
  · change y.1 * x.1 = x.1 * y.1
    change x.1 = 1 at hx
    simp [hx]
  · exact mul_comm _ _
theorem equiv_product_normalizer_index {D : Type*} [Group D] [Finite D]
    (e : D ≃* (Equiv.Perm (Fin 3) × Multiplicative (ZMod 3))) (P : Sylow 2 D) :
    (normalizer (P : Set D)).index = 3 := by
  rw [← index_map_equiv (normalizer (P : Set D)) e,
    ← MulEquiv.toMonoidHom_eq_coe, P.normalizer_map_surjective e.toMonoidHom e.surjective]
  exact product_normalizer_index (P.mapSurjective e.surjective)
end SymmetricThreeCentralNormalizer
