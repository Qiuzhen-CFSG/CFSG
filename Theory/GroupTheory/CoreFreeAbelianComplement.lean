module

public import Theory.GroupTheory.SubgroupConjugation

/-!
# Normal subgroups in conjugates of a core-free complement

Let `B` be a core-free maximal subgroup complementary to a normal abelian
subgroup `K`. A subgroup `V ≤ B` normalized by `B` can lie in a conjugate of
`B` only if `V` is trivial or that conjugate equals `B`. The result applies
to arbitrary groups, without finiteness or solvability assumptions.

Maximality makes the normalizer of `V` either `B` or the whole group. In the
latter case `V` is normal and lies in the trivial normal core of `B`. Otherwise,
the subgroup product API writes the conjugating element as `kernel * complement`.
The complement component fixes `B`. Conjugate containment forces each
commutator of the kernel component with `V` into `K ⊓ B = ⊥`. Thus the kernel
component centralizes `V`, lies in its normalizer `B`, and is itself trivial.
This argument actually does not need commutativity of `K`; the abelian
hypothesis is retained in the intended complement interface.

This elementary lemma supplies the core-free quotient step in the normal-Sylow
conjugate-maximal argument motivated by Stellmacher, Journal of Algebra 190
(1997), the proof of (9.2), p. 48. The proof here is independent of that
campaign and uses only subgroup conjugation, normalizers, and normal cores.
-/

open scoped Pointwise

universe u

namespace Subgroup

/-- A normal subgroup of a core-free maximal complement cannot lie in a
distinct conjugate of that complement unless it is trivial. -/
public theorem normal_subgroup_le_conjugate_corefree_complement
    {R : Type u} [Group R] (K B V : Subgroup R)
    (hKnormal : K.Normal) (hKcomm : IsMulCommutative K)
    (hB : IsCoatom B) (hcore : B.normalCore = ⊥)
    (hKB : K ⊓ B = ⊥) (htop : K ⊔ B = ⊤)
    (hVB : V ≤ B) (hnormal : B ≤ Subgroup.normalizer V)
    (actor : R) (hactor : V ≤ B.conjBy actor) :
    V = ⊥ ∨ B.conjBy actor = B := by
  let _ : K.Normal := hKnormal
  let _ : IsMulCommutative K := hKcomm
  rcases hB.le_iff.mp hnormal with hnorm | hnorm
  · left
    let _ : V.Normal := normalizer_eq_top_iff.mp hnorm
    apply le_bot_iff.mp
    simpa [hcore] using (normal_le_normalCore.mpr hVB)
  · right
    have hactorTop : actor ∈ K ⊔ B := by rw [htop]; trivial
    have hproduct : (↑(K ⊔ B) : Set R) = (K : Set R) * (B : Set R) :=
      coe_mul_of_right_le_normalizer_left K B le_normalizer_of_normal
    change actor ∈ (↑(K ⊔ B) : Set R) at hactorTop
    rw [hproduct] at hactorTop
    obtain ⟨kernel, hkernel, complement, hcomplement, hdecomp⟩ := hactorTop
    have hfix : B.conjBy complement = B :=
      mem_normalizer_iff_map_conj_eq.mp (B.le_normalizer hcomplement)
    rw [← hdecomp, conjBy_mul, hfix] at hactor ⊢
    have hcentral : kernel ∈ centralizer (V : Set R) := by
      rw [mem_centralizer_iff]
      intro element helement
      obtain ⟨preimage, hpreimage, heq⟩ := hactor helement
      change kernel * preimage * kernel⁻¹ = element at heq
      have hconj : kernel⁻¹ * element * kernel ∈ B := by
        simpa [← heq, mul_assoc] using hpreimage
      have hdiffK : kernel⁻¹ * element * kernel * element⁻¹ ∈ K := by
        simpa [mul_assoc] using
          K.mul_mem (K.inv_mem hkernel) (hKnormal.conj_mem kernel hkernel element)
      have hdiffB : kernel⁻¹ * element * kernel * element⁻¹ ∈ B :=
        B.mul_mem hconj (B.inv_mem (hVB helement))
      have hdiff : kernel⁻¹ * element * kernel * element⁻¹ = 1 := by
        have hmem : kernel⁻¹ * element * kernel * element⁻¹ ∈ K ⊓ B :=
          ⟨hdiffK, hdiffB⟩
        simpa [hKB] using hmem
      calc
        element * kernel = kernel * (kernel⁻¹ * element * kernel * element⁻¹) * element := by
          simp [mul_assoc]
        _ = kernel * element := by rw [hdiff]; simp
    have hkernelB : kernel ∈ B := by
      rw [← hnorm]
      exact centralizer_le_normalizer (V : Set R) hcentral
    have hkernelOne : kernel = 1 := by
      have hmem : kernel ∈ K ⊓ B := ⟨hkernel, hkernelB⟩
      simpa [hKB] using hmem
    rw [hkernelOne, conjBy_one]

end Subgroup
