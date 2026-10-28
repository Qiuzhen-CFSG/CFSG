module

public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Theory.GroupAction.Defs
public import Theory.PGroupCore

/-!
# Centralizers of the center of a self-centralizing core

Suppose that the p-core Q of a finite group G is self-centralizing and that
[G,Q] lies in Z(Q). Then the centralizer of Z(Q) in G is exactly Q.

Conjugation by an element centralizing Z(Q) fixes both Z(Q) and Q/Z(Q).
The kernel of this paired automorphism action is a p-group. The kernel
of conjugation on Q is also a p-group by self-centralization, so the
preimage of the paired kernel is a normal p-group of G and lies in Q.
The reverse containment is the defining property of Z(Q).

This standard automorphism-kernel argument supplies the central-core step
in the class-two case of Niles's pushing-up theorem (1979, Theorem 7.7).
-/

namespace Subgroup

open scoped commutatorElement

/-- A self-centralizing p-core with central ambient commutators is the full
centralizer of its center. -/
public theorem centralizer_centerIn_pCore_eq
    {G : Type*} [Group G] [Finite G] (p : ℕ)
    (hcentral : centralizer (pCore p G : Set G) ≤ pCore p G)
    (hcomm : ⁅(⊤ : Subgroup G), pCore p G⁆ ≤ centerIn (pCore p G)) :
    centralizer (centerIn (pCore p G) : Set G) = pCore p G := by
  let Q := pCore p G
  have hQ : IsPGroup p Q := pCore_isPGroup
  let conjugation : G →* MulAut Q := MulAut.conjNormal
  let K := (automorphismPair (center Q)).ker.comap conjugation
  have hconjker : conjugation.ker ≤ Q := by
    intro g hg
    apply hcentral
    rw [mem_centralizer_iff]
    intro q hq
    have hfix := congrArg (fun a : MulAut Q => (a ⟨q, hq⟩ : G))
      (MonoidHom.mem_ker.mp hg)
    change g * q * g⁻¹ = q at hfix
    exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  have hK : IsPGroup p K :=
    (isPGroup_automorphism_pair_kernel (center Q) (hQ.to_subgroup _)).comap_of_ker_isPGroup
      conjugation (hQ.to_le hconjker)
  have hKQ : K ≤ Q := le_sSup ⟨inferInstance, hK⟩
  apply le_antisymm
  · intro g hg
    apply hKQ
    change automorphismPair (center Q) (conjugation g) = 1
    rw [automorphismPair_apply]
    apply Prod.ext
    · apply MulEquiv.ext
      intro z
      apply Subtype.ext
      apply Subtype.ext
      change g * (z : G) * g⁻¹ = (z : G)
      have hz : (z : G) ∈ centerIn Q := by
        rw [centerIn_eq_map_center]
        exact mem_map_of_mem Q.subtype z.property
      rw [← hg (z : G) hz]
      simp only [mul_assoc, mul_inv_cancel, mul_one]
    · apply MulEquiv.ext
      intro v
      obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
      change quotientAut (center Q) (conjugation g)
        (QuotientGroup.mk' (center Q) q) = QuotientGroup.mk' (center Q) q
      rw [quotientAut_apply_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      have hm : (((conjugation g q / q : Q) : G)) ∈ centerIn Q := by
        change (g * (q : G) * g⁻¹) / (q : G) ∈ centerIn Q
        rw [div_eq_mul_inv, ← commutatorElement_def]
        exact hcomm (commutator_mem_commutator (mem_top g) q.property)
      rw [centerIn_eq_map_center] at hm
      obtain ⟨z, hz, he⟩ := hm
      exact (Subtype.ext he : z = conjugation g q / q) ▸ hz
  · intro q hq z hz
    exact (hz.2 q hq).symm

end Subgroup
