module

public import Theory.Representation.FirstCohomologyG2Natural.BinaryPair
public import Theory.AtlasPort.LinearGroups.G2.LongRootNormalGeneration
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Tactic.ReduceModChar

/-!
# Two commutators generate the binary derived G₂ group

For the actual split-octonion automorphism group over a two-element field,
`a = [C(1),S]` and `b = [R,S]` generate its commutator subgroup.

Coordinate identities give `A(1) = a²`, then express `R` using `A(1),b`
and `C(1)` using `a,b,R,S`. Weyl conjugation supplies the other roots.
The torus is trivial over a two-element field, so the pair together with
`S` generates the full automorphism group. Conjugation by `S` inverts
both generators, making their closure normal with cyclic quotient.
It therefore contains the commutator subgroup; the reverse inclusion
holds because the two generators are commutators.

This supplies the binary generation ingredient for Aschbacher--Smith,
I.1.6(5), printed p.408 / PDF p.419, used by the natural-module cocycle
calculation. The root conventions and full-group generation theorem are
from the attributed ATLAS ports imported below; no ATLAS source is copied.
-/

public section

namespace Atlas.G2.Natural
open Atlas.SplitOctonion Explicit
open scoped commutatorElement
variable (K : Type*) [Field K] [CharP K 2]
private def a : Model K := (binaryA K).val
private def b : Model K := (binaryB K).val
private theorem a_apply (x : Carrier K) :
    (a K).val x = ![x 0+x 2+x 3+x 4+x 7, x 1+x 3+x 4+x 5+x 6+x 7, x 2+x 6,
        x 3+x 6+x 7, x 4+x 6+x 7, x 5+x 7, x 6, x 7] := binaryA_apply K x
private theorem b_apply (x : Carrier K) :
    (b K).val x = ![x 5,x 7,x 1,x 3,x 4,x 6,x 0,x 2] := binaryB_apply K x
/-- The square of the first commutator is a sparse long-root map. -/
private theorem rootA_word : rootA (1 : K) = a K * a K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (rootA (1 : K)).val x = (a K).val ((a K).val x)
  ext i
  fin_cases i <;> simp [a_apply, rootA, rootAEquiv, rootALinear, rootAApply,
    CharTwo.neg_eq, sub_eq_add_neg] <;> ring_nf
  all_goals reduce_mod_char!

/-- A word in the long-root map and the cubic Weyl element. -/
private theorem weylR_word : (weylR : Model K) =
    rootA 1 * b K * rootA 1 * b K * rootA 1 * b K * b K * rootA 1 * b K *
      rootA 1 * b K * rootA 1 * b K := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  ext i
  fin_cases i <;> simp [b_apply, rootA, rootAEquiv, rootALinear, rootAApply,
    weylR, weylREquiv, weylRLinear, weylRApply, CharTwo.neg_eq, sub_eq_add_neg] <;> ring_nf
  all_goals reduce_mod_char!
/-- Recover the short-root map after adjoining the two Weyl reflections. -/
private theorem rootC_word : rootC (1 : K) =
    a K * b K * a K * b K * b K * a K * weylR * weylS * a K * weylR := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  simp only [Subgroup.coe_mul, LinearEquiv.mul_apply]
  ext i
  fin_cases i <;> simp [a_apply, b_apply, rootC, rootCEquiv, rootCLinear, rootCApply,
    weylR, weylREquiv, weylRLinear, weylRApply,
    weylS, weylSEquiv, weylSLinear, weylSApply, CharTwo.neg_eq, sub_eq_add_neg] <;> ring_nf
  all_goals reduce_mod_char!
private theorem weylS_rootC_one :
    weylS * rootC (1 : K) * weylS⁻¹ = rootD 1 := by
  rw [weylS_inverse]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [weylS, weylSEquiv, weylSLinear, weylSApply,
    rootC, rootCEquiv, rootCLinear, rootCApply,
    rootD, rootDEquiv, rootDLinear, rootDApply, CharTwo.neg_eq, sub_eq_add_neg]
  ring

private theorem eq_top_of_root_mem (hK : Nat.card K = 2)
    (L : Subgroup (Model K)) (hA : rootA 1 ∈ L) (hC : rootC 1 ∈ L)
    (hR : weylR ∈ L) (hS : weylS ∈ L) : L = ⊤ := by
  have hB : rootB 1 ∈ L := by
    rw [← weylR_rootA]
    exact L.mul_mem (L.mul_mem hR hA) (L.inv_mem hR)
  have hD : rootD 1 ∈ L := by
    rw [← weylS_rootC_one K]
    exact L.mul_mem (L.mul_mem hS hC) (L.inv_mem hS)
  have hE : rootE 1 ∈ L := by
    rw [← weylS_rootB]
    exact L.mul_mem (L.mul_mem hS hB) (L.inv_mem hS)
  have hF : rootF 1 ∈ L := by
    rw [← weylR_rootD]
    exact L.mul_mem (L.mul_mem hR hD) (L.inv_mem hR)
  have h01 (t : K) : t = 0 ∨ t = 1 := by
    obtain ⟨u, _, hu⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
    by_cases ht : t = 0
    · exact Or.inl ht
    · exact Or.inr ((hu t ht).trans (hu 1 one_ne_zero).symm)
  have hu (u : Kˣ) : u = 1 := by
    apply Units.ext
    exact (h01 (u : K)).resolve_left u.ne_zero
  have hroot (f : K → Model K) (h0 : f 0 = 1) (h1 : f 1 ∈ L) (t : K) : f t ∈ L := by
    rcases h01 t with rfl | rfl
    · rw [h0]; exact L.one_mem
    · exact h1
  have hU : unipotent (K := K) ≤ L := by
    rw [unipotent, Subgroup.closure_le]
    simp only [Set.union_subset_iff, Set.range_subset_iff]
    exact ⟨⟨⟨⟨⟨hroot rootA rootA_zero hA, hroot rootB rootB_zero hB⟩,
      hroot rootC rootC_zero hC⟩, hroot rootD rootD_zero hD⟩,
      hroot rootE rootE_zero hE⟩, hroot rootF rootF_zero hF⟩
  apply top_unique
  rw [← generated_eq_top (F := K)]
  apply sup_le
  · rw [rootWeylSubgroup, Subgroup.closure_le]
    rintro g (hg | hg)
    · exact hU hg
    · rcases hg with rfl | hg
      · exact hR
      · exact Set.mem_singleton_iff.mp hg ▸ hS
  · rintro g ⟨⟨l, m⟩, rfl⟩
    change torus l m ∈ L
    rw [hu l, hu m, torus_identity]
    exact L.one_mem

private def pairClosure : Subgroup (Model K) := Subgroup.closure {a K, b K}

omit [CharP K 2] in
private theorem conj_commutator_weylS (g : Model K) :
    (weylS : Model K) * ⁅g, weylS⁆ * weylS⁻¹ = ⁅g, weylS⁆⁻¹ := by
  have hs : (weylS : Model K) * weylS = 1 := by simpa [pow_two] using weylS_sq (K := K)
  simp only [commutatorElement_def, mul_inv_rev, inv_inv, weylS_inverse]
  simp only [mul_assoc, hs, mul_one]

omit [CharP K 2] in
private theorem weylS_mem_normalizer : (weylS : Model K) ∈ Subgroup.normalizer (pairClosure K : Set (Model K)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Subgroup.closure {a K, b K}).map (MulAut.conj weylS).toMonoidHom = _
  rw [MonoidHom.map_closure, Set.image_pair]
  have ha : MulAut.conj weylS (a K) = (a K)⁻¹ := conj_commutator_weylS K (rootC 1)
  have hb : MulAut.conj weylS (b K) = (b K)⁻¹ := conj_commutator_weylS K weylR
  change Subgroup.closure {MulAut.conj weylS (a K), MulAut.conj weylS (b K)} = _
  rw [ha, hb]
  simpa only [Set.inv_insert, Set.inv_singleton, pairClosure] using
    Subgroup.closure_inv ({a K, b K} : Set (Model K))

private theorem pairClosure_sup_weylS (hK : Nat.card K = 2) :
    pairClosure K ⊔ Subgroup.zpowers (weylS : Model K) = ⊤ := by
  let L := pairClosure K ⊔ Subgroup.zpowers (weylS : Model K)
  have hHL : pairClosure K ≤ L := le_sup_left
  have ha : a K ∈ L := hHL (Subgroup.subset_closure (by simp))
  have hb : b K ∈ L := hHL (Subgroup.subset_closure (by simp))
  have hS : (weylS : Model K) ∈ L :=
    (show Subgroup.zpowers (weylS : Model K) ≤ L from le_sup_right) (Subgroup.mem_zpowers _)
  have hA : rootA (1 : K) ∈ L := by
    rw [rootA_word K]
    exact L.mul_mem ha ha
  have hR : (weylR : Model K) ∈ L := by
    rw [weylR_word K]
    repeat' first | exact hA | exact hb | apply L.mul_mem
  have hC : rootC (1 : K) ∈ L := by
    rw [rootC_word K]
    repeat' first | exact ha | exact hb | exact hR | exact hS | apply L.mul_mem
  exact eq_top_of_root_mem K hK L hA hC hR hS

/-- The two explicit commutators generate the actual derived subgroup
over every field of order two. -/
theorem binary_pair_generates [Finite K] (hK : Nat.card K = 2) :
    Subgroup.closure ({binaryA K, binaryB K} : Set (commutator (Model K))) = ⊤ := by
  have hgen := pairClosure_sup_weylS K hK
  have hn : Subgroup.normalizer (pairClosure K : Set (Model K)) = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le (pairClosure K).le_normalizer
      (Subgroup.zpowers_le.mpr (weylS_mem_normalizer K))
  let : (pairClosure K).Normal := Subgroup.normalizer_eq_top_iff.mp hn
  have hd : commutator (Model K) ≤ pairClosure K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hgen inferInstance
  have he : pairClosure K = commutator (Model K) := by
    refine le_antisymm ?_ hd
    change Subgroup.closure {a K, b K} ≤ _
    rw [Subgroup.closure_le]
    rintro g (rfl | hg)
    · exact (binaryA K).property
    · exact Set.mem_singleton_iff.mp hg ▸ (binaryB K).property
  apply Subgroup.map_injective (commutator (Model K)).subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact he
end Atlas.G2.Natural
