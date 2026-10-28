module

public import BenderSuzuki.MatrixGroups.Suzuki
public import Theory.GroupAction.AutomorphismOddOuter
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.FieldAction
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.Normalization
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex.Rigidity

/-!
# The outer index of the concrete Suzuki group

GLS, Volume 4, Chapter 4, Lemma 3.1(a,b), deduces odd outer order from
coverage of all automorphisms by inner and field automorphisms. The upstream
source is GLS, Volume 3, Theorem 2.5.12(b--f).

For `m ≥ 1`, inner conjugation normalizes any automorphism on the standard
root group, split torus and Weyl element. Coordinate rigidity identifies the
normalized automorphism with a genuine entrywise field automorphism. Thus
every automorphism is a product of an inner and a field automorphism.

The field automorphism group consequently surjects onto the quotient of the
full automorphism group by its normal subgroup of inner automorphisms. Its
order is `2m+1`, so the full outer index divides `2m+1` and is odd. Here the
source field exponent `n` is exactly `2m+1`.
-/

namespace BenderSuzuki.MatrixGroups

open PFAppendixIII

/-- Inner-field coverage makes the full outer index divide the field degree. -/
public theorem suzuki_outer_index_dvd_of_inner_field (m : ℕ)
    (hcover : ∀ α : MulAut (SuzukiMatrixGroup m),
      ∃ (g : SuzukiMatrixGroup m)
        (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)),
        α = MulAut.conj g * suzukiFieldAut m σ) :
    (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range.index ∣
      2 * m + 1 := by
  let I := (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range
  let f := (QuotientGroup.mk' I).comp (suzukiFieldAutHom m)
  have hf : Function.Surjective f := by
    intro q
    obtain ⟨α, rfl⟩ := QuotientGroup.mk'_surjective I q
    obtain ⟨g, σ, rfl⟩ := hcover α
    refine ⟨σ, ?_⟩
    have hg : QuotientGroup.mk' I (MulAut.conj g) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change QuotientGroup.mk' I (suzukiFieldAutHom m σ) = _
    rw [map_mul, hg, one_mul, suzukiFieldAutHom_apply]
  have hdiv := Subgroup.card_dvd_of_surjective f hf
  rw [suzukiFieldAut_card] at hdiv
  exact hdiv

/-- Inner-field coverage implies oddness of the full outer index. -/
public theorem suzuki_odd_outer_index_of_inner_field (m : ℕ)
    (hcover : ∀ α : MulAut (SuzukiMatrixGroup m),
      ∃ (g : SuzukiMatrixGroup m)
        (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)),
        α = MulAut.conj g * suzukiFieldAut m σ) :
    Odd (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range.index :=
  (show Odd (2 * m + 1) from ⟨m, by omega⟩).of_dvd_nat
    (suzuki_outer_index_dvd_of_inner_field m hcover)

/-- Every automorphism of the nondegenerate concrete Suzuki group is an inner
automorphism composed with an entrywise defining-field automorphism. -/
public theorem suzukiAut_eq_inner_mul_field (m : ℕ) (hm : 1 ≤ m)
    (α : MulAut (SuzukiMatrixGroup m)) :
    ∃ (g : SuzukiMatrixGroup m)
      (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1)),
      α = MulAut.conj g * suzukiFieldAut m σ := by
  obtain ⟨g, hU, hT, hw⟩ := suzukiAut_exists_normalized m hm α
  obtain ⟨σ, hσ⟩ := suzukiAut_eq_fieldAut_of_normalized m hm
    (MulAut.conj g * α) hU hT hw
  refine ⟨g⁻¹, σ, ?_⟩
  rw [map_inv, ← hσ, inv_mul_cancel_left]

/-- The index of the inner subgroup in the full Suzuki automorphism group
divides the defining-field degree. -/
public theorem suzuki_outer_index_dvd (m : ℕ) (hm : 1 ≤ m) :
    (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range.index ∣
      2 * m + 1 :=
  suzuki_outer_index_dvd_of_inner_field m (suzukiAut_eq_inner_mul_field m hm)

/-- GLS IV, Chapter 4, Lemma 3.1(b), for the concrete Suzuki group: its full
outer automorphism group has odd order. -/
public theorem suzuki_odd_outer_index (m : ℕ) (hm : 1 ≤ m) :
    Odd (MulAut.conj : SuzukiMatrixGroup m →* MulAut (SuzukiMatrixGroup m)).range.index :=
  (show Odd (2 * m + 1) from ⟨m, by omega⟩).of_dvd_nat (suzuki_outer_index_dvd m hm)

end BenderSuzuki.MatrixGroups
