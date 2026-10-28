module

public import Theory.Representation.BinaryPermutation.FiveTensorQuadratic
public import Theory.Representation.BinaryPermutation.FiveSylowQuadratic

/-!
# Sylow four-groups on the natural S₅ tensor module

The actual A₅ × 1 marking restricts to an isomorphism with A₅.
Sylow conjugacy then places both standard double transpositions in a
conjugate of any Sylow two-subgroup. Its order is four, so the tensor
obstruction bounds every quadratic subgroup by two. No placement of an
arbitrary four-group is assumed.

Source: Aschbacher–Smith 13.8.20, printed p.954, the external-X tensor case.
-/

@[expose] public section
open TensorProduct Representation.BinaryOffender
open scoped Pointwise
namespace BinaryPermutation.FiveTensorQuadratic
variable {H D V : Type*} [Group H] [Group D] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Restrict the marked product coordinates to the actual A₅ component. -/
noncomputable def componentEquiv (K : Subgroup H)
    (e : H ≃* Equiv.Perm (Fin 5) × D)
    (hK : K.map e.toMonoidHom = (alternatingGroup (Fin 5)).prod ⊥) :
    K ≃* alternatingGroup (Fin 5) :=
  ((e.subgroupMap K).trans (MulEquiv.subgroupCongr hK)).trans
    ((Subgroup.prodEquiv _ _).trans MulEquiv.prodUnique)

omit [Finite H] in
/-- The restriction has trivial second coordinate. -/
theorem componentEquiv_compatible (K : Subgroup H)
    (e : H ≃* Equiv.Perm (Fin 5) × D)
    (hK : K.map e.toMonoidHom = (alternatingGroup (Fin 5)).prod ⊥) (k : K) :
    e k = ((componentEquiv K e hK k : Equiv.Perm (Fin 5)), 1) := by
  apply Prod.ext
  · rfl
  · have hk : e k ∈ (alternatingGroup (Fin 5)).prod (⊥ : Subgroup D) := by
      rw [← hK]
      exact Subgroup.mem_map.mpr ⟨k, k.property, rfl⟩
    exact hk.2

/-- Both standard double transpositions occur in the same Sylow conjugate. -/
theorem exists_tensor_sylow_marking
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5) × D)
    (eK : K ≃* alternatingGroup (Fin 5))
    (he : ∀ k : K, e k = ((eK k : Equiv.Perm (Fin 5)), 1))
    (P : Sylow 2 K) :
    ∃ g : H,
      e.symm (Equiv.swap 0 1 * Equiv.swap 2 3, 1) ∈
        ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom ∧
      e.symm (Equiv.swap 0 2 * Equiv.swap 1 3, 1) ∈
        ((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P' := P.mapSurjective (f := eK.toMonoidHom) eK.surjective
  obtain ⟨Q, hQ⟩ := BinaryPermutation.CubicFixedSpace.Five.klein_isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) P' Q
  have hp : (P' : Subgroup (alternatingGroup (Fin 5))).map
      (MulAut.conj g).toMonoidHom = Q := by
    have h := congrArg (fun S : Sylow 2 (alternatingGroup (Fin 5)) =>
      (S : Subgroup (alternatingGroup (Fin 5)))) hg
    rwa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h
  have mark (x : alternatingGroup (Fin 5)) (hx : x ∈ Q) :
      e.symm (x.val, 1) ∈ ((P : Subgroup K).map K.subtype).map
        (MulAut.conj (e.symm (g.val, 1))).toMonoidHom := by
    change x ∈ (Q : Subgroup (alternatingGroup (Fin 5))) at hx
    rw [← hp] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨k, hk, hky⟩ := hy
    refine ⟨k.val, ⟨k, hk, rfl⟩, ?_⟩
    apply e.injective
    change e (e.symm (g.val, 1) * k.val * (e.symm (g.val, 1))⁻¹) =
      e (e.symm (x.val, 1))
    rw [map_mul, map_mul, map_inv, e.apply_symm_apply, e.apply_symm_apply, he]
    have h := congrArg Subtype.val hyx
    change g.val * y.val * g.val⁻¹ = x.val at h
    apply Prod.ext
    · simpa only [Prod.fst_mul, Prod.fst_inv, ← hky, MulEquiv.coe_toMonoidHom] using h
    · simp
  exact ⟨e.symm (g.val, 1),
    mark _ (hQ BinaryPermutation.CubicFixedSpace.Five.first_mem),
    mark _ (hQ BinaryPermutation.CubicFixedSpace.Five.second_mem)⟩

omit [Finite H] in
/-- Quadraticity is preserved by the representation at the conjugating element. -/
theorem quadratic_map_conj {ρ : Representation (ZMod 2) H V}
    {A : Subgroup H} (hA : IsQuadratic ρ A) (g : H) :
    IsQuadratic ρ (A.map (MulAut.conj g).toMonoidHom) := by
  have hinv (v : V) : ρ g⁻¹ (ρ g v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ v
  change ρ (g * a * g⁻¹) (ρ (g * b * g⁻¹) v - v) = ρ (g * b * g⁻¹) v - v
  have h := congrArg (ρ g) (hA a ha b hb (ρ g⁻¹ v))
  have hginv (v : V) : ρ g (ρ g⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  simpa only [map_mul, Module.End.mul_apply, map_sub, hinv, hginv] using h

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
/-- A quadratic subgroup in a Sylow two-subgroup of the marked A₅ has order at most two. -/
theorem tensor_card_le_two_in_sylow
    (K : Subgroup H) (e : H ≃* Equiv.Perm (Fin 5) × D)
    (hK : K.map e.toMonoidHom = (alternatingGroup (Fin 5)).prod ⊥)
    (ρ : Representation (ZMod 2) H V) (σ : Representation (ZMod 2) D W)
    (f : V ≃ₗ[ZMod 2] (BinaryPermutation.core (Fin 5) ⊗[ZMod 2] W))
    (heq : ∀ g v, f (ρ g v) = tensorAction σ (e g) (f v))
    (w : W) (hw : w ≠ 0) (P : Sylow 2 K)
    (A : Subgroup H) (hAP : A ≤ (P : Subgroup K).map K.subtype)
    (hq : IsQuadratic ρ A) : Nat.card A ≤ 2 := by
  let eK := componentEquiv K e hK
  obtain ⟨g, ha, hb⟩ := exists_tensor_sylow_marking K e eK
    (componentEquiv_compatible K e hK) P
  have hc := card_le_two_of_quadratic_in_four e ρ σ f heq w hw
    (A.map (MulAut.conj g).toMonoidHom)
    (((P : Subgroup K).map K.subtype).map (MulAut.conj g).toMonoidHom)
    (Subgroup.map_mono hAP)
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact FiveSylowQuadratic.sylow_card K eK P)
    ha hb (quadratic_map_conj hq g)
  rwa [Subgroup.card_map_of_injective (MulAut.conj g).injective] at hc
end BinaryPermutation.FiveTensorQuadratic

end
