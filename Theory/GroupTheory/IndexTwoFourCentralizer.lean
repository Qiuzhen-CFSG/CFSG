module

public import GorensteinWalter.KleinFourFixedAutomorphism
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic

/-!
# Four-group centralizers across an index-two extension

Suppose every involution of G lies in an index-two subgroup K, and a
four-group A has no additional centralizer in K. If its normalizer has an
automorphism whose square is nontrivial on A, then C_G(A)=A as well.

For an outside centralizer element x, its square lies in A. All outside
centralizer elements have the same square, since their quotient lies in A.
Consequently every normalizer element fixes x². A four-group automorphism
fixing a nonidentity element has square one, so x²=1. This contradicts the
involution hypothesis. The argument needs neither a complement nor a
classification of the ambient Sylow subgroup.

The consumer is the quadratic PSL₂ branch of Aschbacher--Smith, E.1.14(6),
with the literal tau condition of E.1.1--2, printed pp.209--210 and 214.
-/

public section
open Subgroup GorensteinWalter
namespace Theory.GroupTheory

/-- A four-group with a nontrivial odd normalizer action remains
self-centralizing when an index-two extension introduces no involutions. -/
theorem centralizer_four_eq_of_index_two
    {G : Type*} [Group G] (K A : Subgroup G)
    (hindex : K.index = 2) (hA : IsKleinFour A)
    (hcent : centralizer (A : Set G) ⊓ K ≤ A)
    (hinv : ∀ x : G, orderOf x = 2 → x ∈ K)
    (hnorm : ∃ n ∈ normalizer (A : Set G), n ^ 2 ∉ centralizer (A : Set G)) :
    centralizer (A : Set G) = A := by
  let : IsKleinFour A := hA
  let : K.Normal := normal_of_index_eq_two hindex
  have hAC : A ≤ centralizer (A : Set G) := by
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨b, hb⟩ : A) ⟨a, ha⟩)
  apply le_antisymm _ hAC
  intro x hx
  by_cases hxK : x ∈ K
  · exact hcent ⟨hx, hxK⟩
  have hx1 : x ≠ 1 := fun h => hxK (h ▸ K.one_mem)
  have hsA : x ^ 2 ∈ A := hcent ⟨pow_mem hx 2, sq_mem_of_index_two hindex x⟩
  have hs1 : x ^ 2 ≠ 1 := fun h => hxK (hinv x
    ((orderOf_eq_prime_iff (x := x)).mpr ⟨h, hx1⟩))
  obtain ⟨n, hn, hn2⟩ := hnorm
  let y := n * x * n⁻¹
  have hyC : y ∈ centralizer (A : Set G) :=
    (normal_subgroupOf_iff (centralizer_le_normalizer (A : Set G))).mp
      inferInstance x n hx hn
  have hyK : y ∉ K := by
    intro hy
    have h := (inferInstance : K.Normal).conj_mem y hy n⁻¹
    apply hxK
    simpa [y, mul_assoc] using h
  have hdiff : y * x⁻¹ ∈ A := by
    apply hcent
    refine ⟨(centralizer (A : Set G)).mul_mem hyC
      ((centralizer (A : Set G)).inv_mem hx), ?_⟩
    change y * x⁻¹ ∈ K
    rw [mul_mem_iff_of_index_two hindex]
    simp only [hyK, inv_mem_iff, hxK]
  have hcomm : Commute (y * x⁻¹) x :=
    mem_centralizer_iff.mp hx _ hdiff
  have hdiff2 : (y * x⁻¹) ^ 2 = 1 := by
    rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨y * x⁻¹, hdiff⟩ : A))
  have hysq : y ^ 2 = x ^ 2 := by
    calc
      y ^ 2 = ((y * x⁻¹) * x) ^ 2 := by simp
      _ = (y * x⁻¹) ^ 2 * x ^ 2 := hcomm.mul_pow 2
      _ = x ^ 2 := by rw [hdiff2, one_mul]
  let nn : normalizer (A : Set G) := ⟨n, hn⟩
  let φ := A.normalizerMonoidHom nn
  have hfix : φ ⟨x ^ 2, hsA⟩ = ⟨x ^ 2, hsA⟩ := by
    apply Subtype.ext
    change n * x ^ 2 * n⁻¹ = x ^ 2
    calc
      n * x ^ 2 * n⁻¹ = y ^ 2 := by dsimp [y]; simp only [pow_two]; group
      _ = x ^ 2 := hysq
  have hφ : φ ^ 2 = 1 := mulAut_sq_eq_one_of_fixed_ne_one φ
    (fun h => hs1 (congrArg Subtype.val h)) hfix
  have hk : nn ^ 2 ∈ A.normalizerMonoidHom.ker := by
    change A.normalizerMonoidHom (nn ^ 2) = 1
    rw [map_pow]
    exact hφ
  rw [normalizerMonoidHom_ker] at hk
  exact (hn2 hk).elim

end Theory.GroupTheory
