module
public import BenderSuzuki.SE.Models
public import Theory.SpecificGroups.PSL2.SylowPointwiseInner
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki

/-!
# Uniform pointwise Sylow innerness for simple Bender groups

The three concrete matrix calculations apply to arbitrary automorphism orders.
Transport along the model isomorphism preserves both the given Sylow subgroup
and the conjugating element. In the unitary case, fixed-field cardinality gives
the required Frobenius formula, and simplicity is inherited from the caller.

This is the quotient automorphism input to GLS4, Chapter 4, Lemma 2.8(c).
The covering Sylow-center calculation is a separate obligation.
-/

namespace BenderSuzuki.ZD.DirectSylowCenters
open _root_.BenderSuzuki.MatrixGroups

/-- Every pointwise Sylow fixer is conjugation by an element of that Sylow. -/
public theorem bender_aut_fixing_sylow_inner
    {B : Type*} [Group B] [Finite B] (hB : IsSimpleBenderGroup B)
    (P : Sylow 2 B) (α : MulAut B) (hfix : ∀ x ∈ P, α x = x) :
    ∃ x ∈ P, α = MulAut.conj x := by
  have hs := hB.isSimple
  rcases hB with ⟨⟨n, hn, ⟨e⟩⟩⟩ | ⟨⟨m, hm, ⟨e⟩⟩⟩ |
    ⟨⟨n, hn, K, hK, hKfin, J, hJ, hcard, hfixed, ⟨e⟩⟩⟩
  · exact MulAut.fixing_sylow_inner_of_equiv e
      Theory.PSL2.aut_fixing_sylow_inner P α hfix
  · apply MulAut.fixing_sylow_inner_of_equiv e _ P α hfix
    intro Q β hβ
    obtain ⟨R, hR⟩ := suzukiRootSubgroup_isSylow m hm
    apply MulAut.fixing_inner_sylow R Q _ β hβ
    intro γ hγ
    change ∀ x ∈ (R : Subgroup _), γ x = x at hγ
    change ∃ x ∈ (R : Subgroup _), γ = MulAut.conj x
    rw [hR] at hγ ⊢
    exact BaseAutomorphisms.suzuki_aut_fixing_root_inner m hm γ hγ
  · let : IsSimpleGroup B := hs
    let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) := e.symm.isSimpleGroup
    apply MulAut.fixing_sylow_inner_of_equiv e _ P α hfix
    exact HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj J hn hcard
      (External.huppert_II_10_4_conj_eq_frobenius J (2 ^ n) hcard hfixed)

end BenderSuzuki.ZD.DirectSylowCenters
