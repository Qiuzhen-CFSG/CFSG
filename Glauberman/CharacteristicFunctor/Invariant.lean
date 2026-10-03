module
public import Glauberman.Theorem5_1
public import Theory.GroupAction.Invariant

/-!
# Invariance and normalizers of characteristic-functor values

A characteristic functor preserves invariant subgroups for a supplied group
action: every actor automorphism maps P to itself, and injective-map
naturality therefore maps K(P) to itself. Applying the inverse actor gives
the reverse membership implication. The same principle for conjugation
shows N(P) ≤ N(K(P)). Neither result needs finiteness or a prime-group
hypothesis on P; these are consequences of the functor's naturality fields.

The characteristic functors are those of Glauberman, *A Characteristic
Subgroup of a p-Stable Group*, §5, as defined in `Glauberman.Theorem5_1`.
These reusable consequences supply the literal ZJ subgroup in the invariant
normalizer supplement and in Kurzweil–Stellmacher §11.2's local-to-global
signalizer argument, while retaining the original action instance.
-/

namespace Glauberman.CharacteristicFunctor

/-- An invariant subgroup has an invariant characteristic-functor value. -/
public theorem isInvariant
    {A H : Type*} [Group A] [Group H] [MulDistribMulAction A H]
    {p : ℕ} (K : CharacteristicFunctor p) (P : Subgroup H) [hPI : IsInvariant A H P] :
    IsInvariant A H (K.K P) := by
  have hPmap (a : A) : P.map (MulDistribMulAction.toMulAut A H a).toMonoidHom = P := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact (hPI.invariant a y).mp hy
    · intro x hx
      refine ⟨a⁻¹ • x, (hPI.invariant a⁻¹ x).mp hx, ?_⟩
      exact smul_inv_smul a x
  have hKmap (a : A) : (K.K P).map (MulDistribMulAction.toMulAut A H a).toMonoidHom = K.K P := by
    have h := K.K_map (MulDistribMulAction.toMulAut A H a).toMonoidHom P
      ((MulDistribMulAction.toMulAut A H a).injective.comp P.subtype_injective)
    rw [hPmap a] at h
    exact h.symm
  have forward (a : A) (x : H) (hx : x ∈ K.K P) : a • x ∈ K.K P := by
    rw [← hKmap a]
    exact Subgroup.mem_map_of_mem (MulDistribMulAction.toMulAut A H a).toMonoidHom hx
  exact ⟨fun a x => ⟨forward a x, fun hx => by simpa using forward a⁻¹ (a • x) hx⟩⟩

/-- A subgroup normalizer also normalizes its characteristic-functor value. -/
public theorem normalizer_le_normalizer_K
    {H : Type*} [Group H] {p : ℕ} (K : CharacteristicFunctor p) (P : Subgroup H) :
    Subgroup.normalizer (P : Set H) ≤ Subgroup.normalizer (K.K P : Set H) := by
  intro g hg
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
  have hP : P.map (MulAut.conj g).toMonoidHom = P := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  have h := K.K_conj P g
  rw [hP] at h
  simpa only [MulEquiv.toMonoidHom_eq_coe] using h.symm

end Glauberman.CharacteristicFunctor
