module

public import BenderSuzuki.SE.Models
public import BenderSuzuki.ZD.ProductClosedCentralFactor.ModelGeometry.Fusion
public import BenderSuzuki.Converse.PSL2
public import BenderSuzuki.Converse.PSU3
public import BenderSuzuki.Converse.Sz

/-!
# Distinct commuting conjugates in the simple Bender models

For each of PSL₂(2ⁿ), PSU₃(2ⁿ), and Sz(2²ᵐ⁺¹), the concrete converse
construction supplies both a four-group and Peterfalvi's action Hypothesis (A).
The action gives a strongly embedded point stabilizer, so all involutions
are conjugate. Transporting a commuting pair from the four-group proves the
required geometry for every involution, and actual multiplicative equivalences
transport it to the groups recognized by `IsSimpleBenderGroup`.

For PSU₃ we use the general Hermitian-form construction, retaining both the
matrix-field cardinality and the fixed-field cardinality from the model
predicate. No identification with an unrelated field involution is needed.

Source motivation: Aschbacher--Smith, *The Classification of Quasithin Groups*,
I.8.2, printed pp. 429–430 (PDF pp. 440–441), where Borel action on root
involutions eliminates the extra central involution. The concrete action and
four-group proofs are in `Converse.PSL2`, `Converse.PSU3`, and `Converse.Sz`.
-/

namespace BenderSuzuki
open PFAppendixIII PFchapter1section1 _root_.BenderSuzuki.MatrixGroups

private theorem geometry_of_equiv
    {G K : Type*} [Group G] [Group K] (e : G ≃* K)
    (hK : ∀ i : K, IsInvolution i →
      ∃ g : K, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i))
    (i : G) (hi : IsInvolution i) :
    ∃ g : G, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i) := by
  obtain ⟨g, hne, hc⟩ := hK (e i)
    (IsInvolution.map_of_injective hi e.toMonoidHom e.injective)
  refine ⟨e.symm g, ?_, ?_⟩
  · intro h
    apply hne
    simpa [MulAut.conj_apply] using congrArg e h
  · simpa [MulAut.conj_apply] using hc.map e.symm.toMonoidHom

/-- Every involution of a simple Bender model has a distinct commuting
conjugate. The model parameter restrictions are exactly those in
`IsSimpleBenderGroup`: `n ≥ 2` for PSL₂ and PSU₃, and `m ≥ 1` for Suzuki. -/
public theorem IsSimpleBenderGroup.exists_distinct_commuting_conjugate
    {G : Type*} [Group G] [Finite G] (hG : IsSimpleBenderGroup G)
    (i : G) (hi : IsInvolution i) :
    ∃ g : G, MulAut.conj g i ≠ i ∧ Commute i (MulAut.conj g i) := by
  rcases hG with ⟨⟨n, hn, e⟩⟩ | ⟨⟨n, hn, e⟩⟩ |
      ⟨⟨n, hn, E, hEfield, hEfinite, J, hJ, hEcard, hfixedCard, e⟩⟩
  · apply geometry_of_equiv e.some _ i hi
    have hA := Converse.hypothesisA_PSL2_binary n hn
    exact hA.A1.isStronglyEmbedded.exists_distinct_commuting_conjugate_of_twoRank hA.A3
  · let : NeZero n := ⟨by omega⟩
    apply geometry_of_equiv e.some _ i hi
    have hA := Converse.hypothesisA_Sz n
    exact hA.A1.isStronglyEmbedded.exists_distinct_commuting_conjugate_of_twoRank hA.A3
  · let : Field E := hEfield
    let : Finite E := hEfinite
    apply geometry_of_equiv e.some _ i hi
    obtain ⟨_, rho, _, _, happly, _⟩ :=
      External.huppert_II_10_12 J (2 ^ n) hEcard hfixedCard hJ
    obtain ⟨H, D, Q, t, _, hA⟩ :=
      Converse.hypothesisA_psu3_general J hJ (2 ^ n) hEcard hfixedCard
        (by
          calc (2 : ℕ) < 2 ^ 2 := by norm_num
               _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn)
        ⟨n, rfl⟩ rho happly
    let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) (Converse.psuOmega J) :=
      MulAction.compHom _ rho
    exact hA.A1.isStronglyEmbedded.exists_distinct_commuting_conjugate_of_twoRank hA.A3
end BenderSuzuki
