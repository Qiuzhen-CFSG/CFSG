module
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.QuadraticPointCore
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PairNormalizer

/-!
# Quadratic elementary subgroups normalized by the four-letter alternating group

An elementary subgroup of the pair stabilizer normalized by the embedded A₄
is either supported on the complementary pair, or contains two independent
elements of the even point core. The latter contradicts the quadratic bound
on that core in the actual four-dimensional natural module.

The certificate checks only the 48 pair-stabilizer words. Its hypotheses use
the two explicit generators of A₄; subgroup normality supplies their conjugates.
This is the moved omega-module image calculation in Aschbacher–Smith,
*The Classification of Quasithin Groups*, 3.3.31, printed p.602.
-/

open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.BinaryFlags

private def fourWords : List S := permsOfList [0, 1, 2, 3]
private def pointWords : List S := fourWords ++ fourWords.map (fun g => swap45 * g)
private def conjugate (c g : S) : S := c * g * c⁻¹
private def orbitProducts (g : S) : List S :=
  [g * conjugate cycle012 g, g * conjugate (cycle012^2) g,
   conjugate cycle012 g * conjugate (cycle012^2) g]
private def lineA : S := swap01 * swap23
private def lineB : S := Equiv.swap 0 2 * Equiv.swap 1 3
private theorem normalAbelian_cert : pointWords.all (fun g => decide
    (g ^ 2 = 1 → g * conjugate cycle012 g = conjugate cycle012 g * g →
     g * conjugate cycle013 g = conjugate cycle013 g * g →
     g = 1 ∨ g = swap45 ∨ (lineA ∈ orbitProducts g ∧ lineB ∈ orbitProducts g))) = true := by
  decide +kernel
private theorem mem_fourWords {g : S} (h4 : g 4 = 4) (h5 : g 5 = 5) : g ∈ fourWords := by
  apply mem_permsOfList_of_mem
  intro x hx
  fin_cases x <;> simp_all
private theorem mem_pointWords {g : S} (h : g ∈ H1) : g ∈ pointWords := by
  rcases mem_H1_cases h with h | h
  · exact List.mem_append_left _ (mem_fourWords h.1 h.2)
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨swap45 * g, mem_fourWords ?_ ?_, ?_⟩
    · simp [swap45, Equiv.Perm.mul_apply, h.1]
    · simp [swap45, Equiv.Perm.mul_apply, h.2]
    · simp [swap45, ← mul_assoc]
private theorem quadratic_excludes_generators (A : Subgroup S)
    (hq : Representation.BinaryOffender.IsQuadratic (BinaryPermutation.naturalRepresentation (Fin 6)) A) (ha : lineA ∈ A) (hb : lineB ∈ A) : False := by
  have hae : lineA ∈ pointCoreEven := by
    refine ⟨?_, by change Equiv.Perm.sign _ = 1; decide⟩
    rw [pointCore_eq_closure]
    exact subset_closure (by simp [lineA])
  have hbe : lineB ∈ pointCoreEven := by
    refine ⟨?_, by change Equiv.Perm.sign _ = 1; decide⟩
    rw [pointCore_eq_closure]
    exact subset_closure (by simp [lineB])
  let f : Fin 3 → ↥(A ⊓ pointCoreEven) := ![1, ⟨lineA,ha,hae⟩, ⟨lineB,hb,hbe⟩]
  have hi : Function.Injective f := by
    intro i j he
    have hh := congrArg (fun h : ↥(A ⊓ pointCoreEven) => h.val 0) he
    have cert : ∀ i j : Fin 3,
        (![1,lineA,lineB] i) 0 = (![1,lineA,lineB] j) 0 → i = j := by decide +kernel
    have hf (k : Fin 3) : (f k).val = ![1,lineA,lineB] k := by
      fin_cases k <;> rfl
    rw [hf i,hf j] at hh
    exact cert i j hh
  have hc := Nat.card_le_card_of_injective f hi
  have ht := QuadraticPointCore.even_quadratic_card_le_two (A ⊓ pointCoreEven)
    inf_le_right (fun a ha b hb v => hq a ha.1 b hb.1 v)
  rw [Nat.card_fin] at hc
  omega

/-- A quadratic elementary subgroup normalized by the first-four-letter A₄
is supported on the complementary pair. -/
public theorem elementary_quadratic_normalized_K_le_swap45 (A : Subgroup S)
    (hA : IsElementaryAbelian 2 A) (hAH : A ≤ H1)
    (hn : K ≤ normalizer (A : Set S))
    (hq : Representation.BinaryOffender.IsQuadratic (BinaryPermutation.naturalRepresentation (Fin 6)) A) : A ≤ zpowers swap45 := by
  let := hA
  have hconj {g : S} (hg : g ∈ A) {c : S} (hc : c ∈ K) : conjugate c g ∈ A :=
    (mem_normalizer_iff.mp (hn hc) g).mp hg
  have hc1 : cycle012 ∈ K := by decide
  have hc2 : cycle013 ∈ K := by decide
  have hcomm {g h : S} (hg : g ∈ A) (hh : h ∈ A) : g*h=h*g := by
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨g,hg⟩ : A) ⟨h,hh⟩)
  intro g hg
  have hcert : ∀ g ∈ pointWords, g^2=1 →
      g*conjugate cycle012 g=conjugate cycle012 g*g →
      g*conjugate cycle013 g=conjugate cycle013 g*g →
      g=1 ∨ g=swap45 ∨ (lineA∈orbitProducts g ∧ lineB∈orbitProducts g) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using normalAbelian_cert
  rcases hcert g (mem_pointWords (hAH hg))
    (elemPow_eq_one_of_isElementaryAbelian g hg)
    (hcomm hg (hconj hg hc1)) (hcomm hg (hconj hg hc2)) with rfl | rfl | ⟨ha,hb⟩
  · exact one_mem _
  · exact mem_zpowers _
  · have horbit {x : S} (hx : x ∈ orbitProducts g) : x ∈ A := by
      simp only [orbitProducts,List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact mul_mem hg (hconj hg hc1)
      · exact mul_mem hg (hconj hg (pow_mem hc1 2))
      · exact mul_mem (hconj hg hc1) (hconj hg (pow_mem hc1 2))
    exact (quadratic_excludes_generators A hq (horbit ha) (horbit hb)).elim
end Theory.SpecificGroups.SymmetricSix.BinaryFlags
