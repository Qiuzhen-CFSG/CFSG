module

public import CFSG.Quasithin.Chapter1.Defs
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The block input to component refinement

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 2.3.8(4), printed p.523, and the generation argument in the proof of
Lemma 2.3.9(7), printed p.526.

`BlockDecomposition` retains the ordered product of at most two blocks,
their actual conjugation modules, their subnormality in the local group,
and the identity with their commutator with J(S). In particular, a block
is not asserted to be subnormal in the ambient group G.

`LocalBlockGeneration` is the precise input needed from the local-structure
argument. Two suitable local overgroups generating L force an allowed block
outside M in one of them. Concrete parabolic calculations can contradict
this conclusion using their subnormal subgroups and conjugation modules.
These reductions do not classify the possible groups L.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement

open Subgroup ChapterC

variable {G : Type*} [Group G]

/-- The complete product-and-block conclusion of 2.3.8(4), for a specified
local group H. The block predicates include actual module isomorphisms. -/
structure BlockDecomposition (M S H : Subgroup G) where
  count : ℕ
  count_le_two : count ≤ 2
  block : Fin count → Subgroup H
  allowed : ∀ i, IsChiZeroBlockIn (block i)
  outside : ∀ i, ¬ (block i).map H.subtype ≤ M
  moved : ∀ i, (block i).map H.subtype =
    ⁅(block i).map H.subtype, Stellmacher.elementaryAbelianMaxJ S⁆
  factorization : ∀ h : H, ∃ m : M.subgroupOf H, ∃ b : ∀ i, block i,
    h = (m : H) * (List.ofFn fun i => (b i : H)).prod

/-- Only local overgroups inside ⟨L,S⟩ are needed for the refinement.
`HeOver` includes nontrivial two-core and containment of S. -/
def LocalBlockGeneration (L M S : Subgroup G) : Prop :=
  ∀ H : Subgroup G, H ≤ L ⊔ S → H ∈ Chapter1.HeOver G (S : Set G) →
    ¬ H ≤ M → Nonempty (BlockDecomposition M S H)

/-- An individual block retains both relative subnormality and its actual
module type, as well as its movement by the specified Thompson subgroup. -/
def EscapingBlock (M S H : Subgroup G) (B : Subgroup H) : Prop :=
  IsChiZeroBlockIn B ∧ ¬ B.map H.subtype ≤ M ∧
    B.map H.subtype = ⁅B.map H.subtype, Stellmacher.elementaryAbelianMaxJ S⁆

/-- A model-local obstruction can be proved without any recognition
conclusion: every allowed moved block of H is already inside M. -/
def BlockObstruction (M S H : Subgroup G) : Prop :=
  ∀ B : Subgroup H, IsChiZeroBlockIn B →
    B.map H.subtype = ⁅B.map H.subtype, Stellmacher.elementaryAbelianMaxJ S⁆ →
      B.map H.subtype ≤ M

/-- The exact product factorization implies the expected generation identity. -/
theorem BlockDecomposition.generated {M S H : Subgroup G}
    (d : BlockDecomposition M S H) :
    M.subgroupOf H ⊔ iSup d.block = ⊤ := by
  apply top_unique
  intro h _
  obtain ⟨m, b, rfl⟩ := d.factorization h
  apply Subgroup.mul_mem
  · exact (show M.subgroupOf H ≤ M.subgroupOf H ⊔ iSup d.block from le_sup_left)
      m.property
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (show iSup d.block ≤ M.subgroupOf H ⊔ iSup d.block from le_sup_right)
      ((le_iSup d.block i) (b i).property)

/-- A local group outside M has at least one factor in its block product. -/
theorem BlockDecomposition.count_pos {M S H : Subgroup G}
    (d : BlockDecomposition M S H) (hH : ¬ H ≤ M) : 0 < d.count := by
  by_contra hn
  have hn : d.count = 0 := by omega
  apply hH
  intro h hh
  obtain ⟨m, b, he⟩ := d.factorization ⟨h, hh⟩
  have hnil : (List.ofFn fun i => (b i : H)) = [] := by
    apply List.eq_nil_of_length_eq_zero
    simpa using hn
  rw [hnil, List.prod_nil, mul_one] at he
  have hv := congrArg (fun x : H => (x : G)) he
  have hm : ((m : H) : G) ∈ M := m.property
  change h = ((m : H) : G) at hv
  rwa [← hv] at hm

/-- Extract an actual block, rather than a label for an allowed family. -/
theorem BlockDecomposition.exists_escapingBlock {M S H : Subgroup G}
    (d : BlockDecomposition M S H) (hH : ¬ H ≤ M) :
    ∃ B : Subgroup H, EscapingBlock M S H B := by
  let i : Fin d.count := ⟨0, d.count_pos hH⟩
  exact ⟨d.block i, d.allowed i, d.outside i, d.moved i⟩

/-- The generation step on p.526. No invariant-parabolic or model
classification assertion is hidden in the two local subgroup witnesses. -/
theorem exists_escapingBlock_of_pair {L M S H₁ H₂ : Subgroup G}
    (hblocks : LocalBlockGeneration L M S) (hLM : ¬ L ≤ M)
    (hgen : L ≤ H₁ ⊔ H₂)
    (h₁ : H₁ ≤ L ⊔ S) (h₂ : H₂ ≤ L ⊔ S)
    (he₁ : H₁ ∈ Chapter1.HeOver G (S : Set G))
    (he₂ : H₂ ∈ Chapter1.HeOver G (S : Set G)) :
    (∃ B : Subgroup H₁, EscapingBlock M S H₁ B) ∨
      (∃ B : Subgroup H₂, EscapingBlock M S H₂ B) := by
  by_cases hm₁ : H₁ ≤ M
  · have hm₂ : ¬ H₂ ≤ M := fun hm₂ => hLM (hgen.trans (sup_le hm₁ hm₂))
    obtain ⟨d⟩ := hblocks H₂ h₂ he₂ hm₂
    exact Or.inr (d.exists_escapingBlock hm₂)
  · obtain ⟨d⟩ := hblocks H₁ h₁ he₁ hm₁
    exact Or.inl (d.exists_escapingBlock hm₁)

/-- Two model-local block obstructions rule out the corresponding component.
The premises concern subnormal blocks of the displayed local groups, not
the desired list of surviving components. -/
theorem le_of_pair_blockObstruction {L M S H₁ H₂ : Subgroup G}
    (hblocks : LocalBlockGeneration L M S) (hgen : L ≤ H₁ ⊔ H₂)
    (h₁ : H₁ ≤ L ⊔ S) (h₂ : H₂ ≤ L ⊔ S)
    (he₁ : H₁ ∈ Chapter1.HeOver G (S : Set G))
    (he₂ : H₂ ∈ Chapter1.HeOver G (S : Set G))
    (ho₁ : BlockObstruction M S H₁) (ho₂ : BlockObstruction M S H₂) :
    L ≤ M := by
  by_contra hLM
  rcases exists_escapingBlock_of_pair hblocks hLM hgen h₁ h₂ he₁ he₂ with
    ⟨B, ha, hm, hc⟩ | ⟨B, ha, hm, hc⟩
  · exact hm (ho₁ B ha hc)
  · exact hm (ho₂ B ha hc)

variable {K : Type*} [Group K]

/-- Every allowed block has a nonzero module of even binary dimension.
The A₅ and L₂(4) actions remain distinct in `IsChiZeroBlock`; this necessary
condition does not identify them. -/
theorem chiZero_module_card (h : IsChiZeroBlock K) :
    ∃ n : ℕ, 0 < n ∧ Nat.card (BlockModule K) = 2 ^ (2 * n) := by
  rcases h with ⟨n, hn⟩ | h | h
  · exact ⟨n, lt_trans (by decide : 0 < 1) hn.1,
      by simpa [Nat.mul_comm] using hn.module_card⟩
  · exact ⟨1, by decide, by simpa using h.module_card_odd (by decide)⟩
  · exact ⟨2, by decide, by simpa using h.module_card_odd (by decide)⟩

/-- Odd-dimensional local modules are an obstruction to all three block
types allowed by 2.3.8(4). -/
theorem not_chiZero_of_odd_module_card (d : ℕ)
    (hcard : Nat.card (BlockModule K) = 2 ^ (2 * d + 1)) :
    ¬ IsChiZeroBlock K := by
  intro h
  obtain ⟨n, _, hn⟩ := chiZero_module_card h
  have he : 2 * d + 1 = 2 * n :=
    (Nat.pow_right_injective (by decide : 1 < 2)) (hcard.symm.trans hn)
  omega

end CFSG.Quasithin.Chapter2.ComponentRefinement

end
