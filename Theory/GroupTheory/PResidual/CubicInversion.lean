module
public import Theory.GroupTheory.PResidual.CubicCoreIndex

/-!
# Fixation and inversion in a cubic quotient

If a normal subgroup C and X generate G, an automorphism preserving C
and inverting X modulo a larger normal subgroup N inverts G/N.
When this quotient has order three, any subgroup fixed modulo N lies
in N: each of its images has both square and cube equal to one.

The statement retains the literal automorphism and both normal kernels.
It is used for the external full-product calculation in Aschbacher–Smith
13.8.20, printed p.954/PDF p.971.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

/-- A fixed subgroup vanishes in a cubic quotient inverted by the same automorphism. -/
theorem le_normal_of_fixed_inverted_cubic_quotient
    (B C X N : Subgroup G) [C.Normal] [N.Normal]
    (hgen : C ⊔ X = ⊤) (hCN : C ≤ N)
    (hc : Nat.card (G ⧸ N) = 3) (a : MulAut G)
    (haC : ∀ c ∈ C, a c ∈ C)
    (hinv : ∀ x ∈ X, a x * x ∈ N)
    (hfix : ∀ b ∈ B, a b * b⁻¹ ∈ N) : B ≤ N := by
  let q := QuotientGroup.mk' N
  have hi (g : G) : q (a g) = (q g)⁻¹ := by
    obtain ⟨c, hcC, x, hx, he⟩ := mem_sup_of_normal_left.mp
      (show g ∈ C ⊔ X by rw [hgen]; trivial)
    have hc1 : q c = 1 := (QuotientGroup.eq_one_iff c).mpr (hCN hcC)
    have hac1 : q (a c) = 1 := (QuotientGroup.eq_one_iff _).mpr (hCN (haC c hcC))
    have hx1 : q (a x) = (q x)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (hinv x hx)
    simp only [← he, map_mul, hac1, hc1, one_mul, hx1]
  intro b hb
  apply (QuotientGroup.eq_one_iff b).mp
  change q b = 1
  have hf : q (a b) = q b := by
    apply mul_inv_eq_one.mp
    rw [← map_inv, ← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr (hfix b hb)
  have hs : (q b) ^ 2 = 1 := by
    calc
      (q b) ^ 2 = q (a b) * q b := by rw [hf, pow_two]
      _ = 1 := by rw [hi, inv_mul_cancel]
  have ht : (q b) ^ 3 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  simpa only [pow_succ, hs, one_mul] using ht

/-- Inversion and fixation in the cubic quotient give containment in C O₂(J). -/
theorem le_sup_twoCore_of_fixed_inverted_cubic (B C X J : Subgroup G)
    (hgen : C ⊔ X = J) (hn : J ≤ normalizer (C : Set G)) (hBJ : B ≤ J)
    (hcore : X.pCoreIn 2 ≤ J.pCoreIn 2)
    (hindex : (C ⊔ J.pCoreIn 2).relIndex J = 3)
    (s : normalizer (J : Set G)) (hsC : s.val ∈ normalizer (C : Set G))
    (hinv : ∀ x ∈ X, s.val * x * s.val⁻¹ * x ∈ X.pCoreIn 2)
    (hcomm : ⁅B, zpowers s.val⁆ ≤ J.pCoreIn 2) : B ≤ C ⊔ J.pCoreIn 2 := by
  let N := C ⊔ J.pCoreIn 2
  have hCJ : C ≤ J := hgen ▸ le_sup_left
  have hXJ : X ≤ J := hgen ▸ le_sup_right
  have hNJ : N ≤ J := sup_le hCJ (pCoreIn_le 2 J)
  let _ : (C.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hn
  have hnN : J ≤ normalizer (N : Set G) :=
    (le_inf hn (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let _ : (N.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hNJ).mpr hnN
  have hg : C.subgroupOf J ⊔ X.subgroupOf J = ⊤ := by
    rw [← subgroupOf_sup hCJ hXJ, hgen, subgroupOf_self]
  have hc : Nat.card (J ⧸ N.subgroupOf J) = 3 := by
    rw [← index_eq_card]
    exact hindex
  have hle := le_normal_of_fixed_inverted_cubic_quotient
    (B.subgroupOf J) (C.subgroupOf J) (X.subgroupOf J) (N.subgroupOf J)
    hg (subgroupOf_mono J le_sup_left) hc (J.normalizerMonoidHom s)
    (fun c hc => (mem_normalizer_iff.mp hsC c.val).mp hc)
    (fun x hx => show (J.normalizerMonoidHom s x * x).val ∈ N from
      mem_sup_right (hcore (hinv x.val hx)))
    (fun b hb => show (J.normalizerMonoidHom s b * b⁻¹).val ∈ N from
      mem_sup_right (hcomm (by
        rw [commutator_comm]
        exact commutator_mem_commutator (mem_zpowers s.val) hb)))
  intro b hb
  exact hle (show (⟨b, hBJ hb⟩ : J) ∈ B.subgroupOf J from hb)

/-- Separate two-perfectness removes the intrinsic two-core supplement. -/
theorem le_normal_of_twoPerfect_le_sup_twoCore (B C J : Subgroup G)
    (hCJ : C ≤ J) (hBJ : B ≤ J) (hn : J ≤ normalizer (C : Set G))
    (hp : IsPPerfect 2 B) (hBN : B ≤ C ⊔ J.pCoreIn 2) : B ≤ C := by
  let _ : (C.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hCJ).mpr hn
  have hB : IsPPerfect 2 (B.subgroupOf J) := hp.of_surjective
    (subgroupOfEquivOfLe hBJ).symm.toMonoidHom (subgroupOfEquivOfLe hBJ).symm.surjective
  have hP : IsPGroup 2 ((J.pCoreIn 2).subgroupOf J) :=
    (isPGroup_pCoreIn 2 J).comap_subtype
  have hle : B.subgroupOf J ≤ C.subgroupOf J ⊔ (J.pCoreIn 2).subgroupOf J := by
    rw [← subgroupOf_sup hCJ (pCoreIn_le 2 J)]
    exact subgroupOf_mono J hBN
  have h := le_normal_of_isPPerfect_of_le_sup_pGroup
    (B.subgroupOf J) (C.subgroupOf J) ((J.pCoreIn 2).subgroupOf J) hB hP hle
  intro b hb
  exact h (show (⟨b, hBJ hb⟩ : J) ∈ B.subgroupOf J from hb)

end Subgroup
