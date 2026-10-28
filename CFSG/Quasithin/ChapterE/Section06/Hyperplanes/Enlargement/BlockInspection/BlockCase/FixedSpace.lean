module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport

/-!
# Fixed spaces of proper block overgroups in E.6.23

An escaping subgroup centralizing a hyperplane has exactly that hyperplane
as its fixed space. A proper block overgroup cannot centralize the same
hyperplane: restriction preserves its relative subnormality, and C.1.9
would make it commute with the nonabelian short group it contains.
The index-two interval between A and U then proves C_V(X) = A.

Only the exact C.1.9 and E.6.21 conclusions remain explicit earlier inputs.
No normality in G, block persistence, or identification of the two distinct
four-dimensional modules is used here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265); C.1.7 and C.1.9, printed p.123.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- A block restricts to the centralizer of a larger subspace when it is contained there. -/
theorem block_restrict {A U X : Subgroup G} (hAU : A ≤ U)
    (hX : CentralizerBlock A X) (hXU : X ≤ centralizer (U : Set G)) :
    CentralizerBlock U X := by
  have hc : centralizer (U : Set G) ≤ centralizer (A : Set G) := centralizer_le hAU
  refine ⟨hXU, inferInstance, ?_, ?_⟩
  · exact (hX.2.short.of_mulEquiv (subgroupOfEquivOfLe hX.1)).of_mulEquiv
      (subgroupOfEquivOfLe hXU).symm
  · exact hX.2.subnormal.comap (Subgroup.inclusion hc)

omit [Finite G] in
private theorem short_not_self_centralizing {L : Subgroup G} (hL : ChapterC.IsShort L) :
    ¬ L ≤ centralizer (L : Set G) := by
  intro hc
  have hz : ChapterC.blockU L ≤ center L := by
    intro x hx
    apply Subgroup.mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp (hc x.property) y y.property)
  exact hL.irreducible.1.ne (inf_eq_left.mpr hz)

/-- C.1.9 rules out a proper overgroup that still centralizes the original hyperplane. -/
theorem proper_block_not_centralizes (h19 : BlockCommutationInput G)
    (h21 : OddCoreFree V) {U A L X : Subgroup G}
    (hU : U ∈ obstructionFamily M V) (hAU : A ≤ U)
    (hL : SmallBlock U L) (hLX : L < X) (hX : CentralizerBlock A X) :
    ¬ X ≤ centralizer (U : Set G) := by
  intro hXU
  rcases centralizerBlocks_equal_or_commute h19 h21 hU.1 hU.2.1
    ⟨hL.1, hL.2.1⟩ (block_restrict hAU hX hXU) with he | hc
  · exact hLX.ne he
  · have hLL : L ≤ centralizer (L : Set G) :=
      (commutator_eq_bot_iff_le_centralizer.mp hc).trans (centralizer_le hLX.le)
    exact short_not_self_centralizing (hL.2.2.elim (fun h => h.2.1) (fun h => h.2.1)) hLL

private theorem relative_index [IsElementaryAbelian 2 V] (B : Subgroup G) :
    B.relIndex V = 2 ^ subgroupCorank V B := by
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank V B

omit [Finite G] in
private theorem index_two_interval {A B C : Subgroup G}
    (hAB : A ≤ B) (hBC : B ≤ C) (hi : A.relIndex C = 2) : B = A ∨ B = C := by
  have ht := relIndex_mul_relIndex A B C hAB hBC
  rw [hi] at ht
  have hd : A.relIndex B ∣ 2 := ⟨B.relIndex C, ht.symm⟩
  rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with h1 | h2
  · exact Or.inl (le_antisymm (relIndex_eq_one.mp h1) hAB)
  · rw [h2] at ht
    have hb : B.relIndex C = 1 := by omega
    exact Or.inr (le_antisymm hBC (relIndex_eq_one.mp hb))

/-- An escaping subgroup centralizing a hyperplane has precisely that fixed space. -/
theorem escaping_fixedSpace [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    {U L : Subgroup G} (hU : IsHyperplane V U)
    (hLU : L ≤ centralizer (U : Set G)) (he : ¬ L ≤ M) :
    V ⊓ centralizer (L : Set G) = U := by
  have hUF : U ≤ V ⊓ centralizer (L : Set G) :=
    le_inf hU.1 (le_centralizer_iff.mp hLU)
  have hi : U.relIndex V = 2 := by rw [relative_index, hU.2]; rfl
  rcases index_two_interval hUF inf_le_left hi with hf | hf
  · exact hf
  · exact (he ((le_centralizer_iff.mpr (hf ▸ inf_le_right)).trans h.centralizer_le)).elim

/-- The full fixed space of a proper block overgroup is exactly the corank-two subspace. -/
theorem proper_block_fixedSpace [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    {U A L X : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hL : SmallBlock U L) (he : ¬ L ≤ M)
    (hLX : L < X) (hX : CentralizerBlock A X) :
    V ⊓ centralizer (X : Set G) = A := by
  have hAF : A ≤ V ⊓ centralizer (X : Set G) :=
    le_inf (hAU.trans hUh.1) (le_centralizer_iff.mp hX.1)
  have hFU : V ⊓ centralizer (X : Set G) ≤ U := by
    rw [← escaping_fixedSpace h hUh hL.1 he]
    exact inf_le_inf_left _ (centralizer_le hLX.le)
  have hiA : A.relIndex V = 4 := by rw [relative_index, hc]; rfl
  have hiU : U.relIndex V = 2 := by rw [relative_index, hUh.2]; rfl
  have ht := relIndex_mul_relIndex A U V hAU hUh.1
  rw [hiA, hiU] at ht
  have hi : A.relIndex U = 2 := by omega
  rcases index_two_interval hAF hFU hi with hf | hf
  · exact hf
  · exact (proper_block_not_centralizes h19 h21 hU hAU hL hLX hX
      (le_centralizer_iff.mpr (hf ▸ inf_le_right))).elim

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
