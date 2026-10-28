module
public import Theory.GroupTheory.PResidual.CubicInversion
public import Theory.GroupTheory.PResidual.FiniteLocalPair
public import Theory.GroupTheory.PResidual.NormalizedSupplement
public import Theory.GroupTheory.PCoreImage

/-!
# A fixed complement to an inverted cubic residual

Let A and B be mutually normalizing two-perfect subgroups, with cubic
A/O₂(A), two-group intersection, and A not contained in B. If J = AB = AD
with D normal and two-perfect in J, an automorphism inverting A/O₂(A) and
fixing D/O₂(D), while preserving B, forces D = B.

Modulo B O₂(J), the group is cubic; fixedness and inversion force the
image of D to vanish. Two-perfectness removes the two-core, giving D ≤ B.
The product equality and two-group intersection then give B ≤ D.

Source application: Aschbacher–Smith 14.7.41, printed p.1061,
refs/quasithin.pdf, with the original point group and Borel residual.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

/-- A two-perfect fixed supplement coincides with the invariant complement. -/
theorem eq_of_inverted_cubic_fixed_supplement (A B D : Subgroup G)
    (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B) (hD : IsPPerfect 2 D)
    (hc : Nat.card (A ⧸ pCore 2 A) = 3)
    (hAB : A ≤ normalizer (B : Set G)) (hBA : B ≤ normalizer (A : Set G))
    (hDn : A ⊔ B ≤ normalizer (D : Set G))
    (hgen : A ⊔ D = A ⊔ B) (hi : IsPGroup 2 (A ⊓ B : Subgroup G))
    (hne : ¬ A ≤ B) (t : G)
    (ht : t ∈ normalizer (↑(A ⊔ B) : Set G)) (htB : t ∈ normalizer (B : Set G))
    (hinv : ∀ a ∈ A, t * a * t⁻¹ * a ∈ A.pCoreIn 2)
    (hfix : ∀ d ∈ D, t * d * t⁻¹ * d⁻¹ ∈ D.pCoreIn 2) : D = B := by
  let J := A ⊔ B
  have hAJ : A ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  have hDJ : D ≤ J := (le_sup_right : D ≤ A ⊔ D).trans_eq hgen
  have hnA : J ≤ normalizer (A : Set G) := sup_le A.le_normalizer hBA
  have hnB : J ≤ normalizer (B : Set G) := sup_le hAB B.le_normalizer
  have hcoreA : A.pCoreIn 2 ≤ J.pCoreIn 2 := pCoreIn_mono_of_normalizes hAJ hnA
  have hcoreD : D.pCoreIn 2 ≤ J.pCoreIn 2 := pCoreIn_mono_of_normalizes hDJ hDn
  have hind : (B ⊔ J.pCoreIn 2).relIndex J = 3 :=
    cubic_relIndex_sup_pCoreIn B A J (sup_comm B A) hnB
      (isPPerfect_sup A B hA hB) hc hcoreA
      (fun he => hne (he ▸ hAJ))
  let N := B ⊔ J.pCoreIn 2
  have hNJ : N ≤ J := sup_le hBJ (pCoreIn_le 2 J)
  let : (B.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hnB
  let : (D.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hDn
  have hnN : J ≤ normalizer (N : Set G) :=
    (le_inf hnB (J.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image J (pCore 2 J)))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  let : (N.subgroupOf J).Normal := normal_subgroupOf_of_le_normalizer hnN
  have hg : B.subgroupOf J ⊔ A.subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup hBJ hAJ, sup_comm B A, subgroupOf_self]
  have hcard : Nat.card (J ⧸ N.subgroupOf J) = 3 := by
    rw [←index_eq_card]
    exact hind
  have hDN : D ≤ N := by
    have hh := le_normal_of_fixed_inverted_cubic_quotient
      (D.subgroupOf J) (B.subgroupOf J) (A.subgroupOf J) (N.subgroupOf J)
      hg (subgroupOf_mono J le_sup_left) hcard (J.normalizerMonoidHom ⟨t,ht⟩)
      (fun b hb => (mem_normalizer_iff.mp htB b).mp hb)
      (fun a ha => show t * (a : G) * t⁻¹ * a ∈ N from
        mem_sup_right (hcoreA (hinv a ha)))
      (fun d hd => show t * (d : G) * t⁻¹ * (d : G)⁻¹ ∈ N from
        mem_sup_right (hcoreD (hfix d hd)))
    intro d hd
    exact hh (show (⟨d,hDJ hd⟩ : J) ∈ D.subgroupOf J from hd)
  have hDB : D ≤ B := le_normal_of_twoPerfect_le_sup_twoCore D B J
    hBJ hDJ hnB hD hDN
  have hBD : B ≤ D ⊔ (A ⊓ B) := by
    intro b hb
    have hgen' : A.subgroupOf J ⊔ D.subgroupOf J = ⊤ := by
      rw [←subgroupOf_sup hAJ hDJ,hgen,subgroupOf_self]
    obtain ⟨a,ha,d,hd,he⟩ := mem_sup_of_normal_right.mp
      (show (⟨b,hBJ hb⟩ : J) ∈ A.subgroupOf J ⊔ D.subgroupOf J by rw [hgen']; trivial)
    have hab : (a : G) ∈ B := by
      have he' : (a : G) = b * (d : G)⁻¹ := by
        have hh := congrArg Subtype.val he
        exact eq_mul_inv_of_mul_eq hh
      rw [he']
      exact B.mul_mem hb (B.inv_mem (hDB hd))
    have hprod : (a : G) * (d : G) ∈ D ⊔ (A ⊓ B) :=
      (D ⊔ (A ⊓ B)).mul_mem (mem_sup_right ⟨ha,hab⟩) (mem_sup_left hd)
    have hh : (a : G) * (d : G) = b := congrArg Subtype.val he
    rw [←hh]
    exact hprod
  exact le_antisymm hDB (le_of_isPPerfect_of_le_sup_of_normalizes B D (A ⊓ B)
    hB hi ((inf_le_left.trans hAJ).trans hDn) hBD)
end Subgroup
