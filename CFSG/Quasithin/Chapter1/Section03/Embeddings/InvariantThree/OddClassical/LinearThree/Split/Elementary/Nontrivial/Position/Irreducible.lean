module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.Position.Model
public import Theory.SpecificGroups.SL3.SplitMonomial.AbelianBasis
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal.NormalizerBound
public import Theory.SpecificGroups.SL3.SplitMonomial.SolvableNormal.WeightKernel

/-!
# The irreducible elementary PSL₃ position

The full inverse image of the solvable projective overgroup contains an
ambient Sylow two-subgroup S. Irreducibility and the involution determinant
argument exclude an abelian inverse image. If all its abelian normal
subgroups were scalar, Fitting self-centralization would give a nonabelian
normal three-subgroup Q. The determinant-one weight-kernel calculation and
the normalizer orbit bound give |S| ≤ 8, contradicting 16 ∣ |S|.

Consequently there is a noncentral abelian normal subgroup A. The same
involution argument makes its restriction reducible. Clifford theory now
produces three pairwise nonisomorphic lines over F, permuted by the full
inverse image, and hence an actual invariant F-basis.

This uses the full ambient Sylow hypothesis to prove the monomial alternative
directly. The normalizer bound uses determinant one in SL₃, including the odd
weight-centralizer kernel; all normality is relative to the linear overgroup.
The entire scalar kernel is retained throughout the passage from PSL₃ to SL₃.

Source: GLS3, the solvable portion of Theorem 6.5.3(b–d) and decomposition
(6.5.1), `refs/KGroup/GLS3/chapter6.tex`; Aschbacher–Smith, proof of
Proposition 1.3.4, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

open Subgroup Matrix.SL3.SplitMonomial Representation
open scoped MatrixGroups

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

private theorem preimage_irreducible {F : Type*} [Field F]
    (H : Subgroup PSL(3,F)) (hirr : ¬ ReduciblePreimage H) :
    IsIrreducible ((specialLinearNatural (k := F) 3).comp (projectivePreimage H).subtype) := by
  classical
  refine ⟨fun W => ?_⟩
  by_cases hb : W.toSubmodule = ⊥
  · exact Or.inl (Subrepresentation.toSubmodule_injective hb)
  by_cases ht : W.toSubmodule = ⊤
  · exact Or.inr (Subrepresentation.toSubmodule_injective ht)
  apply (hirr ⟨W.toSubmodule, hb, ht, ?_⟩).elim
  intro g hg v hv
  exact W.apply_mem_toSubmodule ⟨g, hg⟩ hv

/-- The irreducible solvable geometric alternatives for the genuine elementary
pair. Its full ambient Sylow hypothesis in fact forces the invariant-basis case. -/
public theorem invariantBasis_or_small_of_irreducible
    {F : Type*} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hpodd : Odd p) (hlarge : 3 < p) (_hpmod : p % 3 = 1)
    (hF : Nat.card F = p) (T : Sylow 2 PSL(3,F)) (U : Subgroup PSL(3,F))
    (h : ModelInput T U) (hirr : ¬ ReduciblePreimage (U ⊔ (T : Subgroup _))) :
    HasInvariantBasis (projectivePreimage (U ⊔ (T : Subgroup _))) ∨
      Odd (Nat.card (U ⊔ (T : Subgroup _) : Subgroup _)) ∨
      Nat.card (U ⊔ (T : Subgroup _) : Subgroup _) ∣ 216 := by
  let H := U ⊔ (T : Subgroup _)
  let K := projectivePreimage H
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have h2 : (2 : F) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime F
    (p := p) Nat.prime_two (ne_of_gt (lt_trans (by decide : 2 < 3) hlarge))
  let : Group.IsSolvable H := h.solvable
  have hsolv : Group.IsSolvable K := projectivePreimage_solvable H
  obtain ⟨S, hSK⟩ := exists_sylow_le_projectivePreimage T H le_sup_right
  have hi : IsIrreducible ((specialLinearNatural (k := F) 3).comp K.subtype) :=
    preimage_irreducible H hirr
  have hn : ¬ IsMulCommutative K := by
    intro hc
    let : IsMulCommutative K := hc
    exact AbelianBasis.not_irreducible_of_sylow_two_le_normalizer h2 S K
      (hSK.trans K.le_normalizer) hi
  have hA : HasNoncentralAbelianNormal K := by
    by_contra hno
    obtain ⟨Q, hQK, hQn, hQ, hQna⟩ :=
      exists_nonabelian_normal_three_of_not_hasNoncentralAbelianNormal K hsolv hn hno
    have hSN : (S : Subgroup _) ≤ normalizer (Q : Set SL(3,F)) :=
      hSK.trans ((normal_subgroupOf_iff_le_normalizer hQK).mp hQn)
    have hsmall : Nat.card S ≤ 8 :=
      two_subgroup_card_le_eight_of_odd_weight_kernels p (ne_of_lt hlarge) Q hQ hQna
        (fun A ha hi => odd_card_weightCentralizer_normalizer
          (ne_of_lt hlarge) Q hQ hQna A ha hi) S S.isPGroup' hSN
    have hbig : 16 ≤ Nat.card S := Nat.le_of_dvd (Nat.card_pos (α := S))
      (Matrix.SL3.SplitMonomial.sixteen_dvd_card_sylow (hF ▸ hpodd) S)
    omega
  obtain ⟨A, hAK, hAn, hAc, hAnc⟩ := hA
  let : IsMulCommutative A := hAc
  left
  exact hasInvariantBasis_of_reducible_normal K A hAK hAn hAnc hi
    (AbelianBasis.not_irreducible_of_sylow_two_le_normalizer h2 S A
      (hSK.trans ((normal_subgroupOf_iff_le_normalizer hAK).mp hAn)))

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
