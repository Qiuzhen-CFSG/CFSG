module

public import ABG.ChapterII.Section6.Defs

/-!
# The Sylow ZJ normalizer factorization

Alperin--Brauer--Gorenstein, Chapter II, Section 7, Theorem 1 (article p. 61,
PDF p. 62; `refs/latex/alperin-brauer-gorenstein-pages/page-062.tex`) states
that a finite, p-constrained, p-stable group with nontrivial p-core, for an
odd prime p, is the product of its p-prime core and the normalizer of the
center of the Thompson subgroup of any Sylow p-subgroup.

The ordinary `ABG.PStable` hypothesis includes the odd-prime and nontrivial
p-core conditions. Its proved `pStable_iff` bridge supplies exactly the
stability predicate of `G_theorem_8_2_11`, which makes the join of the Thompson
center Z with the p-prime core normal. Extend Z to a Sylow subgroup of that
join. The coprime-intersection identity `inf_pPrimeCore_sup_eq` forces the
Sylow subgroup's ambient image to be Z. Frattini's argument now gives the
whole group as the join of the Z-normalizer with the normal join. Absorbing
Z into its normalizer, and using normality of the p-prime core, gives the
actual set-product equality rather than merely a normality statement.

This is the ordinary Sylow result used by the subsequent Section 7
factorizations; no bridge to the different `Glauberman.pStable` is assumed.
-/

open scoped Pointwise

namespace ABG

public theorem zj_sylow_factorization
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hconstrained : PConstrainedGroup (G := G) p)
    (hstable : PStable p G) (P : Sylow p G) :
    (Set.univ : Set G) = (pPrimeCore p G : Set G) *
      (Subgroup.normalizer (thompsonCenter (P : Subgroup G) : Set G) : Set G) := by
  classical
  let Z := thompsonCenter (P : Subgroup G)
  let N := pPrimeCore p G ⊔ Z
  obtain ⟨hpodd, hcore, hstable'⟩ := pStable_iff.mp hstable
  have hnormal : N.Normal := by
    simpa [N, Z, sup_comm] using G_theorem_8_2_11 p hpodd hcore hconstrained hstable' P
  let := hnormal
  have hZP : Z ≤ (P : Subgroup G) := by
    exact (inf_le_left : Z ≤ thompsonSubgroup (P : Subgroup G)).trans
      (sSup_le fun _ hsubgroup => hsubgroup.1)
  have hZp : IsPGroup p Z := P.isPGroup'.to_le hZP
  obtain ⟨S, hZS⟩ := (hZp.comap_of_injective N.subtype Subtype.coe_injective).exists_le_sylow
  have hZmap : Z ≤ (S : Subgroup N).map N.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le (show Z ≤ N from le_sup_right)]
    exact Subgroup.map_mono hZS
  have hmap : (S : Subgroup N).map N.subtype = Z := by
    have hinter := inf_pPrimeCore_sup_eq ((S : Subgroup N).map N.subtype) Z
      (S.isPGroup'.map N.subtype) hZmap
    rw [inf_eq_left.mpr (Subgroup.map_subtype_le _)] at hinter
    exact hinter
  have hfrattini : Subgroup.normalizer (Z : Set G) ⊔ N = ⊤ := by
    simpa [hmap] using S.normalizer_sup_eq_top
  have hsup : pPrimeCore p G ⊔ Subgroup.normalizer (Z : Set G) = ⊤ := by
    apply top_unique
    rw [← hfrattini]
    exact sup_le le_sup_right
      (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right))
  ext element
  simp only [Set.mem_univ, true_iff, Set.mem_mul]
  exact Subgroup.mem_sup_of_normal_left.mp (hsup ▸ Subgroup.mem_top element)

end ABG
