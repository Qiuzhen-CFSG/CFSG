module

public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Disjoint commutator spaces of commuting factors

If L and K commute and [V,L] and [V,K] are disjoint, K fixes [V,L]
pointwise: each displacement lies in both spaces. Conjugating the factors
also conjugates their commutator spaces under the actual representation.

These facts discharge the second-factor action and the exchanged-subspace
identification in Aschbacher–Smith G.11.2(12), printed p.364/PDF p.375,
used in the rank exclusion in 6.2.19, printed p.691/PDF p.708. Conjugation
is written x l x⁻¹; the source exchanging element has square one.
-/

public section

namespace Representation.RankTwo.Imprimitive
open BinaryOffender
variable {H V A : Type*} [Group H] [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- Commuting groups with disjoint moved spaces fix each other's moved space. -/
theorem fixes_commutator_of_disjoint (ρ : Representation (ZMod 2) H V)
    (L K : Subgroup H) (hc : ∀ l ∈ L, ∀ k ∈ K, Commute l k)
    (hd : Disjoint (subspaceCommutator ρ ⊤ L) (subspaceCommutator ρ ⊤ K))
    (k : H) (hk : k ∈ K) (v : V) (hv : v ∈ subspaceCommutator ρ ⊤ L) :
    ρ k v = v := by
  let P := subspaceCommutator ρ ⊤ L
  have hinv : P ≤ P.comap (ρ k) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨l, hl, w, _, rfl⟩
    change ρ k (ρ l w - w) ∈ P
    have hkl : ρ k (ρ l w) = ρ l (ρ k w) :=
      LinearMap.congr_fun ((hc l hl k hk).symm.map ρ).eq w
    rw [map_sub, hkl]
    exact Submodule.subset_span ⟨l, hl, ρ k w, Submodule.mem_top, rfl⟩
  have hP : ρ k v - v ∈ P := P.sub_mem (hinv hv) hv
  have hK : ρ k v - v ∈ subspaceCommutator ρ ⊤ K :=
    Submodule.subset_span ⟨k, hk, v, Submodule.mem_top, rfl⟩
  exact sub_eq_zero.mp (hd.le_bot ⟨hP, hK⟩)

/-- Conjugate factors have conjugate commutator spaces, with the actual map ρ x. -/
theorem map_commutator_of_swaps_factors (ρ : Representation (ZMod 2) H V)
    (i : (A × A) →* H) (x : H) (hx : x * x = 1)
    (hconj : ∀ a : A, x * i (a,1) * x⁻¹ = i (1,a)) :
    (subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inl A A)).range).map (ρ x) =
      subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inr A A)).range := by
  have hswap (a : A) (w : V) : ρ x (ρ (i (a,1)) w) = ρ (i (1,a)) (ρ x w) := by
    have h := congrArg (fun b : H => b * x) (hconj a)
    have he : x * i (a,1) = i (1,a) * x := by simpa only [mul_assoc, inv_mul_cancel, mul_one] using h
    simpa only [map_mul, Module.End.mul_apply] using congrArg (fun b : H => ρ b w) he
  have hxx (w : V) : ρ x (ρ x w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, hx, map_one, Module.End.one_apply]
  apply le_antisymm
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a, rfl⟩, w, _, rfl⟩
    change ρ x (ρ (i (a,1)) w - w) ∈
      subspaceCommutator ρ ⊤ (i.comp (MonoidHom.inr A A)).range
    rw [map_sub, hswap]
    exact Submodule.subset_span ⟨i (1,a), ⟨a,rfl⟩, ρ x w, Submodule.mem_top, rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨a,rfl⟩, w, _, rfl⟩
    refine ⟨ρ (i (a,1)) (ρ x w) - ρ x w,
      Submodule.subset_span ⟨i (a,1), ⟨a,rfl⟩, ρ x w, Submodule.mem_top, rfl⟩, ?_⟩
    change ρ x (ρ (i (a,1)) (ρ x w) - ρ x w) = ρ (i (1,a)) w - w
    rw [map_sub, hswap, hxx]

end Representation.RankTwo.Imprimitive
