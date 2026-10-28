module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.QuotientCentralizers

/-!
# The primed (d) quotient centralizer

Omitting the first Figure 2 generator leaves the same full Mathieu centralizer.
On every nontrivial orbit the omitted permutation agrees with a word in the
remaining generators. It exchanges the two fixed points, whose set is preserved
by every centralizer element. Thus every centralizer element also commutes with
the omitted generator. Source: KW (1988), Proposition 2.3.5, Case (iii).
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image

def primedProduct (k : Fin 8) : StarGroup :=
  binaryProduct (pairRowGenerator 3) (fun i => (2*k.val).testBit i.val)

def primedTable (k : Fin 8) : Fin 24 → Fin 24 :=
  quotientProductTable 1 ⟨2*k.val,by omega⟩

def primedProfile : Fin 24 → ℕ :=
  ![15,15,1,1,255,255,105,85,51,1,1,195,195,165,51,153,85,153,1,1,1,165,1,105]

def omittedWords : Fin 24 → Fin 8 :=
  ![0,0,4,4,0,0,0,1,2,4,4,0,0,0,2,1,1,1,4,4,4,0,4,0]

private theorem product_table : ∀ k,
    (fun i => (primedProduct k).val i) = primedTable k := by decide +kernel

private theorem product_mem (k : Fin 8) : primedProduct k ∈ pairRowImage 3 :=
  binaryProduct_mem _ _ _ (pairRowGenerator_mem _)

private theorem profile_detect : ∀ i j,
    (∀ k, (primedTable k i = i ↔ primedTable k j = j)) →
      primedProfile i = primedProfile j := by decide +kernel

private theorem omitted_word : ∀ i j, i ≠ 4 → i ≠ 5 → primedProfile i = primedProfile j →
    permutation 0 j = primedTable (omittedWords i) j := by decide +kernel

private theorem fixed_pair : ∀ a b, primedProfile a = 255 → primedProfile b = 255 → a ≠ b →
    b = permutation 0 a ∧ a = permutation 0 b := by decide +kernel

private theorem product_commute (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage 3 : Set StarGroup)) (k : Fin 8) (i : Fin 24) :
    p.val (primedTable k i) = primedTable k (p.val i) := by
  have h := congrArg (fun a : StarGroup => a.val i) (hp _ (product_mem k))
  simpa only [coe_mul, Equiv.Perm.mul_apply, ← product_table] using h.symm

private theorem centralizer_profile (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage 3 : Set StarGroup)) (i : Fin 24) :
    primedProfile (p.val i) = primedProfile i := by
  apply profile_detect
  intro k
  rw [← product_commute p hp k i]
  exact p.val.injective.eq_iff

/-- Every element of the whole primed-row centralizer commutes with the
omitted Figure 2 generator as an actual permutation. -/
theorem primed_centralizer_commutes_omitted (p : StarGroup)
    (hp : p ∈ centralizer (pairRowImage 3 : Set StarGroup)) : Commute p (starElement 0) := by
  apply Subtype.ext
  apply Equiv.ext
  intro i
  change p.val (permutation 0 i) = permutation 0 (p.val i)
  have h45 := fixed_pair (p.val 4) (p.val 5) (centralizer_profile p hp 4)
    (centralizer_profile p hp 5) (p.val.injective.ne (by decide))
  by_cases h4 : i = 4
  · subst i
    exact h45.1
  by_cases h5 : i = 5
  · subst i
    exact h45.2
  rw [omitted_word i i h4 h5 rfl, product_commute p hp,
    ← omitted_word i (p.val i) h4 h5 (centralizer_profile p hp i).symm]

theorem primed_d_le_unprimed_d : pairRowImage 3 ≤ pairRowImage 1 := by
  apply (closure_le _).mpr
  rintro _ ⟨j,rfl⟩
  fin_cases j
  · exact (pairRowImage 1).one_mem
  · exact pairRowGenerator_mem 1 1
  · exact pairRowGenerator_mem 1 2
  · exact pairRowGenerator_mem 1 3

/-- The full centralizer of the primed (d) image is the same sixteen-element
unprimed (d) group. -/
theorem primed_d_quotient_centralizer :
    centralizer (pairRowImage 3 : Set StarGroup) = pairRowImage 1 := by
  apply le_antisymm
  · intro p hp
    have hu : p ∈ centralizer (pairRowImage 1 : Set StarGroup) := by
      rw [pairRowImage, centralizer_closure, mem_centralizer_iff]
      rintro _ ⟨j,rfl⟩
      fin_cases j
      · exact (primed_centralizer_commutes_omitted p hp).eq.symm
      · exact hp _ (pairRowGenerator_mem 3 1)
      · exact hp _ (pairRowGenerator_mem 3 2)
      · exact hp _ (pairRowGenerator_mem 3 3)
    exact (pairRow_quotient_self_centralizing 1) ▸ hu
  · exact (pairRowImage 1).le_centralizer.trans (centralizer_le primed_d_le_unprimed_d)

end Janko4.LocalStructure.ElementaryEightGeometry
