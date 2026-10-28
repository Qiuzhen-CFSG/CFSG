module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Sign
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Transport
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.Residual
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.LinearPosition
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition

/-!
# The odd-characteristic Cartan reduction for invariant Ξ embeddings

The raw A.3.15(3) input uses actual projective rank-three models and an actual
SL₂(q) subgroup. In the noncyclic case its two cyclic factors force the signs
to agree and q > 3. The linear and unitary positioning theorems identify the
cyclic decomposition at the solvable residual of C_D(Z(S)), using the entire
Sylow center. Normality of D makes its intersection with B N_S(B)-invariant.

`CaseThree.canonicalPosition` assembles the sign restriction and both model
calculations, including the actual SL₂(q) isomorphism of the canonical
residual. `CaseThree.canonical_factorization` gives its invariant cyclic
factor. `CaseThree.invariant_factorization` also handles cyclic B, completing
the factor-invariance step from the raw A.3.15(3) input without an additional
positioning premise. It supplies the factors for the irreducibility
obstruction after transport to the original complement action.

Here q is the defining prime and p > 3 is the prime of B. The unitary model
retains fixed-field order q and matrix-field order q². A.3.15 itself remains
an explicit input; invariance of its arbitrary SL₂ witness is not assumed.

Source: Aschbacher–Smith, A.3.15(3), printed pp. 50–51, and the proof of
Proposition 1.3.4, printed pp. 510–511.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
variable {J : Type*} [Group J] [Finite J]
variable {κ : GroupClass} {D B K : Subgroup J} {S : Sylow 2 J}
variable {p q : ℕ} [Fact q.Prime] {δ ε : Sign}

/-- In the noncyclic case, the source signs agree and the cyclic decomposition
is based at the canonical residual `C_D(Z(S))^∞ ≅ SL₂(q)`. All positioning
and field-size premises are discharged from the original source inputs. -/
theorem CaseThree.canonicalPosition
    (hA : AmbientInput κ D B S p) (hC : CaseThree D B (S : Subgroup J) K q δ ε)
    (hn : ¬ IsCyclic B) :
    δ = ε ∧ 3 < q ∧
      CyclicDecomposition B (canonicalResidual D (S : Subgroup J)) ∧
      Nonempty (canonicalResidual D (S : Subgroup J) ≃*
        Matrix.SpecialLinearGroup (Fin 2) (ZMod q)) := by
  let _ : Fact p.Prime := ⟨hA.prime⟩
  have hs := hC.sign_eq hA.p_group (lt_trans (by decide : 2 < 3) hA.large) hn
  have hq := hC.characteristic_gt_three hA.p_group hA.large hn
  refine ⟨hs, hq, ?_⟩
  subst ε
  cases δ with
  | linear => exact hC.linearPosition hA hn hq
  | unitary => exact hC.unitaryPosition hA hn hq

/-- The canonical intersection and its centralizer factor generate B, and
the first is normalized by the actual relative normalizer N_S(B). -/
theorem CaseThree.canonical_factorization
    (hA : AmbientInput κ D B S p) (hC : CaseThree D B (S : Subgroup J) K q δ ε)
    (hn : ¬ IsCyclic B) :
    IsCyclic (canonicalFactor D (S : Subgroup J) B) ∧
      IsCyclic ((centralizer (canonicalResidual D (S : Subgroup J) : Set J)).subgroupOf B) ∧
      canonicalFactor D (S : Subgroup J) B ⊔
        (centralizer (canonicalResidual D (S : Subgroup J) : Set J)).subgroupOf B = ⊤ ∧
      (S : Subgroup J) ⊓ normalizer B ≤
        normalizer ((canonicalFactor D (S : Subgroup J) B).map B.subtype) := by
  let _ : D.Normal := hA.normal
  obtain ⟨hl, hr, hg⟩ := (hC.canonicalPosition hA hn).2.2.1.internal
  exact ⟨hl, hr, hg, canonicalFactor_normalized D (S : Subgroup J) B⟩

/-- A.3.15(3) supplies cyclic factors generating B with the first invariant
under N_S(B). For noncyclic B it is the canonical centralizer-residual
intersection; for cyclic B the trivial factor suffices. -/
theorem CaseThree.invariant_factorization
    (hA : AmbientInput κ D B S p) (hC : CaseThree D B (S : Subgroup J) K q δ ε) :
    ∃ A C : Subgroup B, IsCyclic A ∧ IsCyclic C ∧ A ⊔ C = ⊤ ∧
      (S : Subgroup J) ⊓ normalizer B ≤ normalizer (A.map B.subtype) := by
  by_cases hn : IsCyclic B
  · exact factorization_of_cyclic (S : Subgroup J) hn
  · exact ⟨canonicalFactor D (S : Subgroup J) B,
      (centralizer (canonicalResidual D (S : Subgroup J) : Set J)).subgroupOf B,
      hC.canonical_factorization hA hn⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan
