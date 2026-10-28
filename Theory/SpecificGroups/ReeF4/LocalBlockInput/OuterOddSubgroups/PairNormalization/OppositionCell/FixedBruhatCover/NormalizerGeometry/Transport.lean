module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairNormalization.OppositionCell.FixedBruhatCover.Basic

/-!
# Propagation of exact root transport through normalizer words

Conjugation by a product composes the root permutations and multiplies the
corresponding parameter scalars. Inversion uses the inverse permutation and
the reciprocal scalar at its preimage. Hence a root-transport calculation for
each nonzero rank-one word suffices for the entire generated subgroup.

The generator calculations remain explicit premises here. This module proves
neither those calculations nor Bruhat coverage. Source: the propagation of
GLS3 1.12.1(h) to the normalizer in 2.3.8(b), using left conjugation.
-/

@[expose] public section
open Theory.AlgebraicGroup
namespace ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover

namespace NormalizerGeometry

/-- The identity has the identity root action. -/
noncomputable def rootTransport_one (m : ℕ) : RootTransport (1 : SplitGroup m) where
  perm := Equiv.refl _
  scale := fun _ => 1
  conj_root := by intros; simp

/-- Composition of exact root actions, with their nonzero parameter scalars. -/
noncomputable def rootTransport_mul {m : ℕ} {n k : SplitGroup m}
    (a : RootTransport n) (b : RootTransport k) : RootTransport (n * k) where
  perm := a.perm * b.perm
  scale := fun r => a.scale (b.perm r) * b.scale r
  conj_root := by
    intro r t
    change (n * k) * rootGeneratorInGroup m r t * (n * k)⁻¹ = _
    calc
      _ = n * (k * rootGeneratorInGroup m r t * k⁻¹) * n⁻¹ := by group
      _ = rootGeneratorInGroup m (a.perm (b.perm r))
          ((a.scale (b.perm r) : CoefficientField m) *
            ((b.scale r : CoefficientField m) * t)) := by
        change (MulAut.conj n) ((MulAut.conj k) _) = _
        rw [b.conj_root, a.conj_root]
      _ = _ := by simp [Equiv.Perm.mul_apply, mul_assoc]

/-- Inverse root action, with the reciprocal scalar at the inverse image. -/
noncomputable def rootTransport_inv {m : ℕ} {n : SplitGroup m}
    (a : RootTransport n) : RootTransport n⁻¹ where
  perm := a.perm.symm
  scale := fun r => (a.scale (a.perm.symm r))⁻¹
  conj_root := by
    intro r t
    have he : n * rootGeneratorInGroup m (a.perm.symm r)
        (((a.scale (a.perm.symm r))⁻¹ : (CoefficientField m)ˣ) * t) * n⁻¹ =
        rootGeneratorInGroup m r t := by
      change (MulAut.conj n) _ = _
      rw [a.conj_root, a.perm.apply_symm_apply]
      simp
    change n⁻¹ * rootGeneratorInGroup m r t * (n⁻¹)⁻¹ = _
    rw [inv_inv, ← he]
    group

end NormalizerGeometry

/-- Exact transport for the generators propagates to all normalizer words.
The rank-one transport premise must still be established by matrix calculation. -/
theorem rootTransport_of_mem_splitNormalizerWords_of_rankOne {m : ℕ}
    (hgen : ∀ (r : F4Chevalley.Root) (t : (CoefficientField m)ˣ),
      Nonempty (RootTransport (rankOneRepresentative m r t)))
    {n : SplitGroup m} (hn : n ∈ splitNormalizerWords m) :
    Nonempty (RootTransport n) := by
  induction hn using Subgroup.closure_induction with
  | mem n hn =>
    obtain ⟨r, t, rfl⟩ := hn
    exact hgen r t
  | one => exact ⟨NormalizerGeometry.rootTransport_one m⟩
  | mul n k _ _ hn hk =>
    obtain ⟨a⟩ := hn
    obtain ⟨b⟩ := hk
    exact ⟨NormalizerGeometry.rootTransport_mul a b⟩
  | inv n _ hn =>
    obtain ⟨a⟩ := hn
    exact ⟨NormalizerGeometry.rootTransport_inv a⟩

end ReeF4.LocalBlockInput.PairNormalization.OppositionCell.FixedBruhatCover
