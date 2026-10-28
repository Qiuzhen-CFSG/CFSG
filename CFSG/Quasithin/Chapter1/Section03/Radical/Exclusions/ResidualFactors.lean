module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Swapped.Local

/-!
# Constructing the two residual factors of X

Set W = O²(X ∩ K). Odd-order elements of P ∩ K belong to W. Since X
normalizes K, it also normalizes W, and the chosen t normalizes X. The
conjugate decomposition of P, together with generation of X by its odd
complement, now proves X = W Wᵗ. Residual transport identifies Wᵗ with
O²(X ∩ Kᵗ). Commutation follows when the distinct-block theorem supplies
[K,Kᵗ] = 1; it is not assumed in the generation proof.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.514. Every residual is O², and each normalizer
acts on the displayed ambient subgroup.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open XiEmbedding
variable {G : Type*} [Group G]

/-- A normalizer of X which also normalizes K normalizes O²(X ∩ K). -/
theorem normalizes_blockResidual {X K D : Subgroup G}
    (hDX : D ≤ normalizer X) (hDK : D ≤ normalizer K) :
    D ≤ normalizer (blockResidual X K) :=
  ((le_inf hDX hDK).trans inf_normalizer_le_normalizer_inf).trans
    (normalizer_le_normalizer_characteristic_image (X ⊓ K) (pResidual 2 (X ⊓ K : Subgroup G)))

/-- The chosen block residual transports under an actual normalizer of X. -/
theorem blockResidual_conjBy [Finite G] {X K : Subgroup G} {t : G} (ht : t ∈ normalizer X) :
    (blockResidual X K).conjBy t = blockResidual X (K.conjBy t) := by
  change ((pResidual 2 (X ⊓ K : Subgroup G)).map (X ⊓ K).subtype).map
    (MulAut.conj t).toMonoidHom = _
  rw [map_embedded_pResidual]
  have he : (X ⊓ K).map (MulAut.conj t).toMonoidHom = X ⊓ K.conjBy t := by
    rw [map_inf _ _ _ (MulAut.conj t).injective]
    exact congrArg (fun D => D ⊓ K.conjBy t) (mem_normalizer_iff_map_conj_eq.mp ht)
  rw [he]
  rfl

private theorem odd_intersection_le_blockResidual {p : ℕ} {P X K : Subgroup G}
    (hp : Odd p) (hP : IsPGroup p P) (hPX : P ≤ X) :
    P ⊓ K ≤ blockResidual X K := by
  intro a ha
  let a₀ : (X ⊓ K : Subgroup G) := ⟨a, hPX ha.1, ha.2⟩
  refine mem_map.mpr ⟨a₀, mem_pResidual_of_orderOf_coprime ?_, rfl⟩
  have hc := (hP.orderOf_coprime (Nat.coprime_two_right.mpr hp) ⟨a, ha.1⟩).symm
  simpa only [← Subgroup.orderOf_coe] using hc

/-- The odd conjugate factors generate the two-residual factors in X.
This constructs W = O²(X ∩ K), without assuming a block decomposition. -/
theorem BinaryBlockEmbedding.residual_factorization [Finite G] {p : ℕ}
    {T X P H₀ K : Subgroup G} (h : BinaryBlockEmbedding p T X P H₀ K) :
    ∃ t : G, t ∈ T ⊓ normalizer P ∧ t ∉ normalizer K ∧
      X = blockResidual X K ⊔ (blockResidual X K).conjBy t ∧
      (blockResidual X K).conjBy t = blockResidual X (K.conjBy t) := by
  let _ : Fact p.Prime := ⟨h.local_input.prime⟩
  obtain ⟨t, ht, htn, hgen, _, _⟩ := h.swapped.2
  have htX : t ∈ normalizer X := h.local_input.invariant ht.1
  have htXe : X.map (MulAut.conj t).toMonoidHom = X :=
    mem_normalizer_iff_map_conj_eq.mp htX
  have hXK : X ≤ normalizer K := h.containment.trans
    (cComponentOrbit_le_normalizer h.component (le_sup_right.trans h.local_input.overgroup))
  let W := blockResidual X K
  have hWX : W ≤ X := (blockResidual_le X K).trans inf_le_left
  have hXW : X ≤ normalizer W := normalizes_blockResidual X.le_normalizer hXK
  have hXWt : X ≤ normalizer (W.conjBy t) := by
    have hh := (map_mono (f := (MulAut.conj t).toMonoidHom) hXW).trans
      (W.le_normalizer_map (MulAut.conj t).toMonoidHom)
    rwa [htXe] at hh
  have hWtX : W.conjBy t ≤ X := by
    have hh := map_mono (f := (MulAut.conj t).toMonoidHom) hWX
    rwa [htXe] at hh
  have hPW : P ⊓ K ≤ W := odd_intersection_le_blockResidual h.local_input.odd
    h.local_input.odd_complement.isPGroup h.local_input.complement_le
  have hPWW : P ≤ W ⊔ W.conjBy t := by
    rw [hgen]
    exact sup_le_sup hPW (map_mono (f := (MulAut.conj t).toMonoidHom) hPW)
  have hXWW : X ≤ normalizer (W ⊔ W.conjBy t : Subgroup G) :=
    (le_inf hXW hXWt).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  refine ⟨t, ht, htn, le_antisymm ?_ (sup_le hWX hWtX), blockResidual_conjBy htX⟩
  apply h.local_input.generation.symm.le.trans
  apply (Subgroup.closure_le (K := W ⊔ W.conjBy t)).mpr
  rintro a ⟨n, hn, b, hb, rfl⟩
  exact (mem_normalizer_iff.mp (hXWW (pCoreIn_le 2 X hn)) b).mp (hPWW hb)

/-- Commutation of distinct blocks passes to the constructed residual factors. -/
theorem blockResidual_commute {X K : Subgroup G} {t : G}
    (hcomm : ⁅K, K.conjBy t⁆ = ⊥) :
    ⁅blockResidual X K, (blockResidual X K).conjBy t⁆ = ⊥ := by
  apply bot_unique
  rw [← hcomm]
  exact commutator_mono ((blockResidual_le X K).trans inf_le_right)
    (map_mono (f := (MulAut.conj t).toMonoidHom) ((blockResidual_le X K).trans inf_le_right))

end CFSG.Quasithin.Chapter1.RadicalExclusions
