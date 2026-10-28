module

public import Theory.PrimeRank
public import Theory.GroupTheory.Covering
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Theory.SpecificGroups.Alternating.E9A4LocalRank

/-!
# Sporadic local obstructions for Lemma A.2.19

This file records the local interfaces used in the sporadic paragraph of
Aschbacher--Smith, section A.2.  A sporadic identification is deliberately supplied
as an explicit multiplicative equivalence by the caller.  In particular, the
certificates below do not identify a group from its order or from a predicate
which already contains the desired classification conclusion.

The order calculation is proved here for the actual model
`Multiplicative (ZMod 3 × ZMod 3)`, the elementary abelian group `E₉`.  The
E₉ × A₄ embedding now gives a genuine two-local rank obstruction, using its
normal subgroup 1 × V₄. Concrete sporadic embeddings, quotient sections and
cover calculations are separate obligations; the interfaces alone do not prove
A.2.19. In the source, F₅ means Harada--Norton, not Lyons (GLS3 Table 5.3w).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
combined manuscript (1 March 2004), Lemma A.2.19, printed pp. 40--41
(PDF pp. 51--52).
-/

namespace CFSG.Quasithin.ChapterA

universe u

open scoped Pointwise

variable {G : Type u} [Group G]

public abbrev E9 := Multiplicative (ZMod 3 × ZMod 3)

public theorem e9_card : Nat.card E9 = 3 ^ 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_prod]
  norm_num [Nat.card_zmod]

/-- The identification used when a local argument has reduced an abstract
group to a concrete sporadic model.  Keeping this as an equivalence prevents
order certificates from being used as recognition theorems. -/
public structure ExplicitSporadicIdentification
    (G M : Type u) [Group G] [Group M] where
  equivalence : Nonempty (G ≃* M)

/-- An explicit proper copy of A12 in a group identified with F5. -/
public structure ProperA12SubgroupData (G : Type u) [Group G] where
  embedding : alternatingGroup (Fin 12) →* G
  injective : Function.Injective embedding
  proper : embedding.range ≠ ⊤

public theorem ProperA12SubgroupData.range_is_proper
    (d : ProperA12SubgroupData G) : d.embedding.range ≠ ⊤ := d.proper

/-- Transport the actual proper subgroup along an identification of ambient groups. -/
public def ProperA12SubgroupData.transport {H : Type*} [Group H]
    (d : ProperA12SubgroupData G) (e : G ≃* H) : ProperA12SubgroupData H where
  embedding := e.toMonoidHom.comp d.embedding
  injective := e.injective.comp d.injective
  proper := by
    intro h
    apply d.proper
    rw [MonoidHom.range_eq_top] at h ⊢
    intro g
    obtain ⟨a, ha⟩ := h (e g)
    exact ⟨a, e.injective ha⟩

/-- Legacy ordinary-rank data. The rank fields alone do not establish a
two-local obstruction; the embedding supplies one by the theorem below. -/
public structure E9A4LocalData (G : Type u) [Group G] where
  embedding : E9 × alternatingGroup (Fin 4) →* G
  injective : Function.Injective embedding
  local_three_rank : ℕ
  local_three_rank_gt_two : 2 < local_three_rank
  local_three_rank_le : local_three_rank ≤ primeRank 3 G

public theorem E9A4LocalData.primeRank_three_gt_two
    (d : E9A4LocalData G) : 2 < primeRank 3 G :=
  lt_of_lt_of_le d.local_three_rank_gt_two d.local_three_rank_le

/-- The E₉ × A₄ embedding itself supplies the missing two-local witness. -/
public theorem E9A4LocalData.twoLocalPrimeRank_three_gt_two [Finite G]
    (d : E9A4LocalData G) : 2 < twoLocalPrimeRank 3 G :=
  Theory.Quasithin.three_le_twoLocalPrimeRank_of_e9_prod_a4_embedding
    d.embedding d.injective

/-- No additional rank assumption is required once the embedding is constructed. -/
public theorem not_quasithin_of_e9_a4_embedding [Finite G]
    (f : E9 × alternatingGroup (Fin 4) →* G) (hf : Function.Injective f) :
    ¬ IsQuasithin G :=
  Theory.Quasithin.not_quasithin_of_e9_prod_a4_embedding f hf

/-- An embedded subgroup in an involution centralizer. This only covers the
special case of a section with trivial kernel; nonsplit covers require the
quotient interface below. -/
public structure InvolutionCentralizerSectionData
    (G S : Type u) [Group G] [Group S] where
  involution : G
  involution_order : orderOf involution = 2
  sectionEmbedding : S →* G
  sectionInjective : Function.Injective sectionEmbedding
  centralizes : ∀ x : S, sectionEmbedding x ∈
    Subgroup.centralizer ({involution} : Set G)

/-- An actual quotient section of an involution centralizer. The kernel is
normal in `numerator`, with no ambient-normality or splitting requirement.
Concrete centralizer tasks must construct the numerator and the surjection. -/
public structure InvolutionCentralizerQuotientData
    (G S : Type*) [Group G] [Group S] where
  involution : G
  involution_order : orderOf involution = 2
  numerator : Subgroup G
  centralizes : numerator ≤ Subgroup.centralizer ({involution} : Set G)
  quotientMap : numerator →* S
  surjective : Function.Surjective quotientMap

/-- A.2.15.3 eliminates a sporadic model as soon as its involution
centralizer contains a simple section outside Theorem C. -/
public theorem eliminate_of_involution_centralizer_section
    {S : Type u} [Group S] [Finite S] [IsSimpleGroup S]
    (inC : Type u → Prop)
    (all_sections_in_C : ∀ (T : Type u) [Group T] [Finite T] [IsSimpleGroup T],
      InvolutionCentralizerSectionData G T → inC T)
    (data : InvolutionCentralizerSectionData G S)
    (section_outside_C : ¬ inC S) : False := by
  exact section_outside_C (all_sections_in_C S data)

/-- If an odd prime is coprime to the central kernel of a finite central
cover, that prime does not divide the kernel order. -/
public theorem odd_prime_not_dvd_central_kernel
    {p k : ℕ} (hp : Nat.Prime p) (hcop : Nat.Coprime p k) : ¬ p ∣ k := by
  intro h
  exact (hp.coprime_iff_not_dvd.mp hcop) h

end CFSG.Quasithin.ChapterA
