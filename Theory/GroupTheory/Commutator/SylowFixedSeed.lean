module

public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.ConjugateSpanOrder

/-!
# Normal actors on a span of Sylow-fixed seeds

Suppose that a group D normalizes A and B, with B contained in A, and that
A is contained in B S. If S centralizes a seed Z, then A and B have the
same commutator on the D-conjugate span of Z. The proof first bounds the
commutator on Z, then propagates it using the normal centralizer modulo
the B-commutator.

In the finite-group application, S is a Sylow subgroup and B is the
prime residual of the normal actor A. This supplies the source-fixed seed
step in Aschbacher--Smith, proof of 13.6.13, printed p.929.
-/

public section
namespace Subgroup
variable {G : Type*} [Group G]

/-- A normal actor and its normal supplement have the same displacement
on a conjugate span when the complementary actor fixes the seed. -/
theorem commutator_conjugateSpan_eq_of_fixed_supplement
    (Z D A B S : Subgroup G)
    (hZD : Z ≤ D) (hBD : B ≤ D) (hSD : S ≤ D)
    (hDA : D ≤ normalizer (A : Set G))
    (hDB : D ≤ normalizer (B : Set G))
    (hBA : B ≤ A) (hAS : A ≤ B ⊔ S)
    (hZS : Z ≤ centralizer (S : Set G)) :
    ⁅conjugateSpanBy Z D, A⁆ = ⁅conjugateSpanBy Z D, B⁆ := by
  let U := conjugateSpanBy Z D
  let W := ⁅U, B⁆
  have hDW : D ≤ normalizer (W : Set G) := by
    intro d hd
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅U, B⁆).map _ = ⁅U, B⁆
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy Z D hd),
      mem_normalizer_iff_map_conj_eq.mp (hDB hd)]
  have hBZ : ⁅B, Z⁆ ≤ W := by
    rw [commutator_comm B Z]
    exact commutator_mono (le_conjugateSpanBy Z D) le_rfl
  have hSZ : ⁅S, Z⁆ ≤ W := by
    rw [commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hZS)]
    exact bot_le
  have hAZ : ⁅A, Z⁆ ≤ W :=
    (commutator_mono (hAS.trans (sup_le
      (le_commutatorPreimage hBD hBZ) (le_commutatorPreimage hSD hSZ))) le_rfl).trans
        (commutator_commutatorPreimage_le D Z W hDW)
  have hZA : Z ≤ commutatorPreimage D A W := by
    apply le_commutatorPreimage hZD
    rwa [commutator_comm]
  have hUC : U ≤ commutatorPreimage D A W :=
    conjugateSpanBy_le hZA
      (commutatorPreimage_normalized D A W D hDW D.le_normalizer hDA hDW)
  exact le_antisymm
    ((commutator_mono hUC le_rfl).trans
      (commutator_commutatorPreimage_le D A W hDW))
    (commutator_mono le_rfl hBA)

end Subgroup
