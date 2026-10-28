module

public import CFSG.Quasithin.ChapterK.Section01To04.Symplectic.Recognition.CubicSelection.OuterSchurDegree.Model

/-!
# From paired component coordinates to the actual outer swap

If the component is identified with a tensor product of a half representation
and its conjugate by an ambient involution, interchange implements the same
component automorphism as the actual absolute actor. Schur's lemma compares
the two operators, and their squares force the scalar to be one in
characteristic two. Faithfulness of the original action detects nontrivial
commuting inner involutions on the half representation.

The paired coordinates remain an explicit input; this result supplies the
operator comparison, not the construction of those coordinates.
Source: Guralnick--Malle, Classification of 2F-modules II, Section 3.5 and
Proposition 6.2(2--3); Aschbacher--Smith K.3.4, printed pp.456--457.
-/

@[expose] public section

open Representation Representation.FrobeniusTensor
open scoped TensorProduct

namespace CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur

private theorem involutive_intertwiner_unique
    {k H M : Type*} [Field k] [IsAlgClosed k] [CharP k 2]
    [Group H] [AddCommGroup M] [Module k M] [FiniteDimensional k M]
    (σ : Representation k H M) [IsIrreducible σ]
    (a : MulAut H) (ha : a ^ 2 = 1)
    (T S : Module.End k M) (hT : T ^ 2 = 1) (hS : S ^ 2 = 1)
    (hTi : ∀ u, T * σ u = σ (a u) * T)
    (hSi : ∀ u, S * σ u = σ (a u) * S) : T = S := by
  let C : IntertwiningMap σ σ :=
    { toLinearMap := S * T
      isIntertwining' := by
        intro u
        change (S * T) * σ u = σ u * (S * T)
        have hau : a (a u) = u := DFunLike.congr_fun ha u
        rw [mul_assoc, hTi, ← mul_assoc, hSi, hau, mul_assoc] }
  obtain ⟨c, hc⟩ :=
    (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
      (ρ := σ)).surjective C
  have hC : S * T = c • (1 : Module.End k M) :=
    (congrArg IntertwiningMap.toLinearMap hc).symm
  have hTS : T = c • S := by
    have hh := congrArg (fun U : Module.End k M => S * U) hC
    simpa only [← mul_assoc, ← pow_two, hS, one_mul, mul_smul_comm, mul_one] using hh
  have hc2 : c ^ 2 = 1 := by
    let : Nontrivial M := Subrepresentation.irreducible_module_nontrivial σ
    have hh : c ^ 2 • (1 : Module.End k M) = (1 : k) • (1 : Module.End k M) := by
      simpa only [hTS, smul_pow, hS, one_smul] using hT
    exact (smul_left_injective k (one_ne_zero : (1 : Module.End k M) ≠ 0)) hh
  have hc1 : c = 1 := by
    have hh : c ^ 2 = (1 : k)^2 := by simpa using hc2
    exact (frobenius_inj k 2) hh
  simpa only [hc1, one_smul] using hTS

variable {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G)
  [IsIrreducible (ρ.comp L.subtype)] [L.Normal]

/-- Component coordinates alone: the two factors differ by the actual ambient
conjugation. The action of the outer element itself is not assumed. -/
structure PairedTensorCoordinates (t : G) where
  size : ℕ
  four_le : 4 ≤ size
  half : Representation (Closure (ρ.comp L.subtype)) L
    (Fin size → Closure (ρ.comp L.subtype))
  equivalence : AbsoluteSpace (ρ.comp L.subtype) ≃ₗ[Closure (ρ.comp L.subtype)]
    ((Fin size → Closure (ρ.comp L.subtype)) ⊗[Closure (ρ.comp L.subtype)]
      (Fin size → Closure (ρ.comp L.subtype)))
  component_action : ∀ (u : L) v, equivalence (absoluteRep (ρ.comp L.subtype) u v) =
    TensorProduct.map (half u) (half (MulAut.conjNormal t u)) (equivalence v)

variable {ρ L}

/-- Schur comparison turns paired component coordinates into the actual swap,
including the faithful diagonal actions of commuting inner involutions. -/
theorem tensorSwapRealization_of_pairedCoordinates (hfaith : Function.Injective ρ)
    (t : G) (ht : IsSchurLinear ρ L t) (ht2 : t ^ 2 = 1)
    (P : PairedTensorCoordinates ρ L t) : Nonempty (TensorSwapRealization ρ L t ht) := by
  let K := Closure (ρ.comp L.subtype)
  let W := Fin P.size → K
  let e := P.equivalence
  let swap := TensorProduct.comm K W W
  let S : Module.End K (AbsoluteSpace (ρ.comp L.subtype)) :=
    e.symm.toLinearMap ∘ₗ swap.toLinearMap ∘ₗ e.toLinearMap
  have hS (v) : e (S v) = swap (e v) := by simp [S]
  have hSS : S ^ 2 = 1 := by
    apply LinearMap.ext
    intro v
    apply e.injective
    simp [pow_two, Module.End.mul_apply, hS, swap]
  have haa : (MulAut.conjNormal t : MulAut L) ^ 2 = 1 := by
    rw [← map_pow, ht2, map_one]
  have hSi (u : L) : S * absoluteRep (ρ.comp L.subtype) u =
      absoluteRep (ρ.comp L.subtype) (MulAut.conjNormal t u) * S := by
    apply LinearMap.ext
    intro v
    apply e.injective
    have huu : MulAut.conjNormal t (MulAut.conjNormal t u) = u :=
      DFunLike.congr_fun haa u
    change e (S (absoluteRep (ρ.comp L.subtype) u v)) =
      e (absoluteRep (ρ.comp L.subtype) (MulAut.conjNormal t u) (S v))
    rw [hS, P.component_action, P.component_action, huu, hS]
    exact (TensorProduct.map_comm _ _ _).symm
  have houter : absoluteActor ρ L t ht = S :=
    involutive_intertwiner_unique (absoluteRep (ρ.comp L.subtype))
      (MulAut.conjNormal t) haa _ S (absoluteActor_square ρ L t ht ht2) hSS
      (absoluteActor_intertwines ρ L t ht) hSi
  refine ⟨⟨P.size, P.four_le, e, ?_, ?_⟩⟩
  · intro v
    rw [houter]
    exact hS v
  · intro u hu2 htu
    have hfix : MulAut.conjNormal t u = u := by
      apply Subtype.ext
      change t * (u : G) * t⁻¹ = (u : G)
      rw [htu.eq, mul_inv_cancel_right]
    refine ⟨P.half u, ?_, ?_, ?_⟩
    · rw [← map_pow, hu2, map_one]
    · intro hune he
      apply hune
      apply absoluteRep_injective (ρ.comp L.subtype) (hfaith.comp Subtype.val_injective)
      rw [map_one]
      apply LinearMap.ext
      intro v
      apply e.injective
      change P.equivalence (absoluteRep (ρ.comp L.subtype) u v) = P.equivalence v
      rw [P.component_action, hfix, he, TensorProduct.map_one]
      rfl
    · intro v
      simpa only [hfix] using P.component_action u v

end CFSG.Quasithin.ChapterK.Symplectic.Recognition.OuterSchur
