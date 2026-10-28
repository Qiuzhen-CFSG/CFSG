module
public import CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination.Irreducible.OrdinaryData

/-!
# The concrete linear-three exclusion and remaining source models

The genuine component Sylow and irreducible normalizer action supply the
containment and unipotent marking required by the proved PSL₃ exclusion.
This rules out an isomorphism of the whole escaping component with PSL₃
in characteristic two. It does not apply that isomorphism to K/O₂(K).

`IrreducibleComponentModels` records the exact carriers needed by the
remaining model sieve and the two independent pushing-up/ordinary consumers.
Both SL₃ and PSL₃ are retained in the quotient. Existence of these models,
the characteristic-two exclusion, and reconstruction in the ordinary branch
are not asserted here. Final assembly of the irreducible branch remains open.

Source: Aschbacher–Smith, 13.1.12(3), printed pp.874–875, case (i).
-/

@[expose] public noncomputable section
open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
open Chapter1 Chapter1.XiEmbedding
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L : Subgroup G} {p : ℕ} [Fact p.Prime]

/-- The source model sieve's two linear-three families, on K/O₂(K).
The odd row retains SL₃ as well as PSL₃, a sufficient wider intermediate list. -/
def IrreducibleComponentModels (p : ℕ) (K : Subgroup G) : Prop :=
  LinearThreeModel p (XiQuotient K) ∨
    ∃ n : ℕ, 2 ≤ n ∧ Even n ∧ Nat.ModEq p (2 ^ n) 1 ∧
      LinearThreeModel (2 ^ n) (XiQuotient K)

/-- The congruence at the actual odd prime rules out the exceptional field-four endpoint. -/
theorem Context.binary_degree_ge_four (h : Context T L p) {n : ℕ}
    (hn : 2 ≤ n) (he : Even n) (hc : Nat.ModEq p (2 ^ n) 1) : 4 ≤ n := by
  have hp := h.prime_gt_three
  by_contra hlt
  have hn2 : n = 2 := by
    obtain ⟨k,hk⟩ := he
    omega
  subst n
  have hh : 4 % p = 1 % p := hc
  have hp5 : 5 ≤ p := by
    obtain ⟨k,hk⟩ := h.odd
    omega
  rw [Nat.mod_eq_of_lt hp5,Nat.mod_eq_of_lt (by omega)] at hh
  omega

/-- The whole-component PSL₃ row is impossible under the literal escape data.
No separate radical-containment, Borel or unipotent-marking premise is needed. -/
theorem Context.not_projective_linear_three (h : Context T L p)
    {u : G} (s : Selected T L u) {K : Subgroup G} (e : Escape T L p u K)
    (hi : ComponentNormalizerIrreducible L K p u)
    (F : Type*) [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    ¬ Nonempty (K ≃* PSL(3,F)) := by
  rintro ⟨f⟩
  obtain ⟨S,_,hSX⟩ := h.component_sylow e
  exact SourceCentralizerComponents.source_centralizer_linearThree_row_excluded_of_sylow
    h.hypothesis.simpleQTKE T h.maximal.1 h.nonquasisimple h.odd h.divides
    u (h.radical_le_local s) hi.local F hn hF K (h.radical_le_component s e hi) f S hSX

end CFSG.Quasithin.Chapter13.Section01.SourceCentralizerStructure.Elimination
