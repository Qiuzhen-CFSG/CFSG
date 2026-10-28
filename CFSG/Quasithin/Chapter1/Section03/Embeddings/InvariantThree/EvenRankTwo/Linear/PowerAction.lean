module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.LocalPair
public import Theory.GroupAction.PowerInvolutionInvariant

/-!
# From actual field and graph actions to reducibility

Once each two-subgroup of the pair automizer acts by powers together with one
involution, the elementary fixed-subgroup argument produces the required
proper nonzero invariant subgroup of R/Φ(R). The involution may depend on
the two-subgroup. This is a conditional action bridge: the concrete linear
case must still construct the involution and prove the power formulas.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Proposition 1.3.4, printed p.511 (PDF p.528).
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear

/-- The concrete action calculation suffices for the local reducibility conclusion.
Its displayed formula is an obligation for the model-specific proof. -/
theorem pairReducible_of_power_involution {Q : Type*} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (haction : ∀ D : Subgroup (MulAut R),
      D ≤ pairAutomizer (S : Subgroup Q) R → IsPGroup 2 D →
      ∃ g : MulAut (R ⧸ frattini R), g ^ 2 = 1 ∧
        ∀ a ∈ D, ∀ v, quotientAut (frattini R) a v ∈ zpowers v ∨
          quotientAut (frattini R) a v ∈ zpowers (g v)) :
    PairReducible (S : Subgroup Q) R := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let _ : Fact (IsPGroup 3 R) := ⟨h.oddComplement.isPGroup⟩
  let _ : IsElementaryAbelian 3 (R ⧸ frattini R) := isElementaryAbelian_quotient_frattini
  intro D hD htwo
  obtain ⟨g, hg, hp⟩ := haction D hD htwo
  let E := D.map (quotientAut (frattini R))
  obtain ⟨A, hAb, hAt, hA⟩ := MulAut.exists_invariant_of_power_involution
    (OddInvolutionFrattini.noncyclic_frattini_quotient h.oddComplement.not_isCyclic)
    (E : Set (MulAut (R ⧸ frattini R))) g hg (by
      rintro a ⟨b, hb, rfl⟩ v
      exact hp b hb v)
  exact ⟨A, hAb, hAt, fun a ha => hA _ (mem_map_of_mem _ ha)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo.Linear
