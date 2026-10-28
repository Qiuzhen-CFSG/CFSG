module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ResidualFactors
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.CenterProduct
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.SwappedTrace
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceApplication
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.IndecomposableFactors

/-!
# The concrete factor pair in the binary-block branch of 1.3.8

Choose t in N_T(P) outside N_T(K) and put W = O²(X ∩ K). The residual
factorization gives X = W Wᵗ. Applying C.1.9 inside H₀ gives [W,Wᵗ] = 1;
the global He bridge supplies its additional O₂,₃ fitting hypothesis.
Multiplication identifies X/Z(X) with the product of the two quotient images.
Their odd-order bounds and two-perfectness give direct indecomposability,
and Z(X/Z(X)) = 1 removes the extra center in A.1.15. Pulling the quotient
factors back therefore proves that N_G(X) fixes or swaps WZ(X) and WᵗZ(X).
The first factor has exactly the odd trace P ∩ K.

The theorem constructs these particular subgroups from the configuration;
commutation, indecomposability, permutation, and trace are all proved. Only
the universally quantified source assertions A.1.15 and C.1.9 remain explicit
earlier-source parameters. The parent exclusion argument can apply
`BinaryBlockEmbedding.no_factor_pair` to the resulting pair and trace.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Proposition 1.3.8, printed p.514; A.1.15, p.23; C.1.9, p.123.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions
open BlockRigidity

universe u
variable {G : Type u} [Group G]

private theorem conjugate_pair_permutation {A B : Subgroup G} {d : G}
    (h : (A.conjBy d = A ∨ A.conjBy d = B) ∧
      (B.conjBy d = A ∨ B.conjBy d = B)) :
    (A.conjBy d = A ∧ B.conjBy d = B) ∨
      (A.conjBy d = B ∧ B.conjBy d = A) := by
  have hi : Function.Injective (fun C : Subgroup G => C.conjBy d) :=
    map_injective (MulAut.conj d).injective
  rcases h with ⟨ha | ha, hb | hb⟩
  · have he : A = B := hi (ha.trans hb.symm)
    exact Or.inl ⟨ha, hb.trans he⟩
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · have he : A = B := hi (ha.trans hb.symm)
    exact Or.inl ⟨ha.trans he.symm, hb⟩

/-- The actual residual factors, their normalizer permutation, and their odd
trace in the final paragraph of 1.3.8. Every factor is explicitly identified;
each normalizer element fixes both factors or swaps them. -/
theorem BinaryBlockEmbedding.concrete_factor_pair [Finite G]
    (h115 : SourceA115.{u}) (h19 : SourceC19.{u})
    (T : Sylow 2 G) {p : ℕ} {X P L₀ M H₀ K : Subgroup G}
    (h : BinaryBlockEmbedding p T X P H₀ K)
    (hc : Configuration p T X P L₀ M)
    (hH : H₀ ∈ HOver G (T : Set G))
    (h114 : HOver G (T : Set G) ⊆ He G) :
    ∃ t : G, t ∈ (T : Subgroup G) ⊓ normalizer P ∧ t ∉ normalizer K ∧
      let W := blockResidual X K
      let Z_X := (center X).map X.subtype
      let A := W ⊔ Z_X
      let B := W.conjBy t ⊔ Z_X
      X = W ⊔ W.conjBy t ∧
      W.conjBy t = blockResidual X (K.conjBy t) ∧
      ⁅W, W.conjBy t⁆ = ⊥ ∧
      (∀ d ∈ normalizer (X : Set G),
        (A.conjBy d = A ∧ B.conjBy d = B) ∨
          (A.conjBy d = B ∧ B.conjBy d = A)) ∧
      P ⊓ A = P ⊓ K := by
  obtain ⟨t, ht, htn, hgen, hres⟩ := h.residual_factorization
  have hcomm := blockResidual_commute (X := X)
    (conjugate_commute h19 h h114 hH ht.1 htn)
  obtain ⟨hW, hWt⟩ :=
    h.centerFactors_directlyIndecomposable_of_source T hc hH h114 ht htn
  have hpair := centerFactor_pair_of_source h115 hgen.symm hcomm hW hWt
    (xi_center_quotient_center_eq_bot h114 hc.xi)
  exact ⟨t, ht, htn, hgen, hres, hcomm,
    fun d hd => conjugate_pair_permutation (hpair d hd), h.odd_trace hc h114⟩

end CFSG.Quasithin.Chapter1.RadicalExclusions
