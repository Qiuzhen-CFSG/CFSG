module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Automizer
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Carriers
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo.Symplectic.Placement
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.ExceptionalGraph
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.Sylow.NormalizerDerived
public import Theory.SpecificGroups.SymplecticFour.Sylow.OddSubgroups

/-!
# The surviving symplectic three-complement case

The permuting Sylow pair lies in a Borel by `Symplectic.Placement`. In the
actual full symplectic carrier, the flag characters then embed its odd
complement in Fˣ × Fˣ. This gives an elementary plane, the congruence
2^n = 1 modulo three, and even n. The derived subgroup of the Sylow
normalizer lies in the Sylow subgroup; its intersection with the odd
complement is trivial. Thus the full inner pair stabilizer centralizes R.

The exceptional graph automorphism squares to Frobenius. The proved
classification of diagram-preserving automorphisms therefore shows that its
outer class generates the whole outer group. Transport through the actual
matrix isomorphism and the inner-kernel calculation gives cyclicity of the
full pair automizer.

Only the earlier multiplier implication remains a named parameter:
`SymplecticCentralKernelTheorem` is the universal consequence of I.1.3 that
every finite perfect central extension of PSp₄(2^n), n ≥ 2, has trivial
kernel. Applying it to Q → Q/Z(Q) removes the center. `symplectic_case`
discharges placement and outer cyclicity and supplies the exact alternative
used by the rank-two sieve.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Proposition
1.3.4 and its proof, printed p.511 (PDF p.528 of `refs/quasithin.pdf`).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
open Theory.SpecificGroups.SymplecticFour
universe u

/-- The universal finite perfect-central-extension implication of the
vanishing symplectic multiplier, for the field degrees used here. -/
def SymplecticCentralKernelTheorem : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (n : ℕ), 2 ≤ n → Nat.card F = 2^n →
    ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E]
      (π : E →* ClassicalGroup.PSp 2 F),
      Function.Surjective π → π.ker ≤ center E → π.ker = ⊥

variable {Q : Type u} [Group Q] [Finite Q]
variable {S : Sylow 2 Q} {R : Subgroup Q}

omit [Finite Q] in
private theorem inner_centralizes_of_normalizer_commutator (S R : Subgroup Q)
    (hRS : R ≤ normalizer S) (hd : Disjoint S R)
    (hder : ⁅normalizer (S : Set Q), normalizer (S : Set Q)⁆ ≤ S) :
    normalizer S ⊓ normalizer R ≤ centralizer (R : Set Q) := by
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  rw [← hd.eq_bot]
  exact le_inf ((commutator_mono inf_le_left hRS).trans hder)
    (le_normalizer_iff_commutator_le_right.mp inf_le_right)

/-- The entire inner pair stabilizer acts trivially once R normalizes S. -/
theorem symplectic_inner_centralizes_of_normalizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R) (hnorm : R ≤ normalizer (S : Set Q)) :
    normalizer (S : Set Q) ⊓ normalizer (R : Set Q) ≤ centralizer (R : Set Q) := by
  have hd : Disjoint (S : Subgroup Q) R := (complement_disjoint_sylow h).symm
  have hder : ⁅normalizer (S : Set Q), normalizer (S : Set Q)⁆ ≤ (S : Subgroup Q) :=
    commutator_sylow_normalizer_le_of_equiv hF hn e S
  exact inner_centralizes_of_normalizer_commutator (S : Subgroup Q) R hnorm hd hder

/-- Embed the actual complement into the two Borel characters. -/
theorem symplectic_complement_embedding_of_normalizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R) (hnorm : R ≤ normalizer (S : Set Q)) :
    ∃ j : R →* Fˣ × Fˣ, Function.Injective j := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let U := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hN : R.map e.toMonoidHom ≤ normalizer (U : Set (Sp F)) :=
    (map_mono hnorm).trans (fun _ hx => (S : Subgroup Q).le_normalizer_map e.toMonoidHom hx)
  obtain ⟨j, hj⟩ := odd_sylow_normalizer_embedding hF hn U hN (by decide : Odd 3)
    (h.oddComplement.isPGroup.map e.toMonoidHom)
  exact ⟨j.comp (e.subgroupMap R).toMonoidHom, hj.comp (e.subgroupMap R).injective⟩

/-- The two character coordinates give abelianness and the torus order bound. -/
theorem symplectic_complement_abelian_card_of_normalizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R) (hnorm : R ≤ normalizer (S : Set Q)) :
    IsMulCommutative R ∧ Nat.card R ∣ (2^n - 1)^2 := by
  obtain ⟨j, hj⟩ := symplectic_complement_embedding_of_normalizes hF hn e h hnorm
  refine ⟨IsMulCommutative.of_comm (fun a b => hj (by
    simp only [map_mul, mul_comm])), ?_⟩
  simpa only [Nat.card_prod, Nat.card_units, hF, pow_two] using card_dvd_of_injective j hj

/-- Borel placement gives the plane and the split torus congruence. -/
theorem symplectic_plane_and_congruence_of_normalizes
    {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 ≤ n) (e : Q ≃* Sp F)
    (h : PairInput S R) (hnorm : R ≤ normalizer (S : Set Q)) :
    Nonempty (R ≃* Plane 3) ∧ Nat.ModEq 3 (2^n) 1 := by
  let _ : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hc, hd⟩ := symplectic_complement_abelian_card_of_normalizes hF hn e h hnorm
  have hthree : 3 ∣ Nat.card R := h.oddComplement.isPGroup.card_eq_or_dvd.resolve_left
    (by have := h.oddComplement.one_lt_card Nat.prime_three; omega)
  have hmod : Nat.ModEq 3 (2^n) 1 :=
    ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr
      (Nat.prime_three.dvd_of_dvd_pow (hthree.trans hd))).symm
  exact ⟨complement_plane_of_commutative h hc, hmod⟩

/-- Apply the earlier multiplier implication to the actual central quotient. -/
theorem symplectic_center_eq_bot_of_multiplier
    (hmult : SymplecticCentralKernelTheorem.{u}) {n : ℕ}
    (h : PairInput S R) (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n)) : center Q = ⊥ := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ := hmodel
  let _ := hfield
  let _ := hfinite
  let _ := h.quasisimple.toIsPerfect
  let π := e.toMonoidHom.comp (QuotientGroup.mk' (center Q))
  have hker : π.ker = center Q := by
    ext x
    change e (QuotientGroup.mk' (center Q) x) = 1 ↔ x ∈ center Q
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hh := hmult F n hn hF Q π
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le
  exact hker.symm.trans hh

/-- Conditional assembly of all surviving symplectic conclusions.
`symplectic_surviving_case` below discharges normalization and outer cyclicity. -/
theorem symplectic_case_of_normalizes_of_outer {n : ℕ}
    (h : PairInput S R) (hn : 2 ≤ n) (hcenter : center Q = ⊥)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n))
    (hnorm : R ≤ normalizer (S : Set Q)) (houter : IsCyclic (MulAut.Outer Q)) :
    Nonempty (R ≃* Plane 3) ∧ SymplecticModel 3 Q ∧
      IsCyclic (pairAutomizer (S : Subgroup Q) R) := by
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ :=
    full_symplectic_of_projective_quotient hcenter hmodel
  let _ := hfield
  let _ := hfinite
  obtain ⟨hplane, hmod⟩ := symplectic_plane_and_congruence_of_normalizes hF (by omega) e h hnorm
  refine ⟨hplane, symplectic_model_of_projective_quotient hcenter hmodel hmod, ?_⟩
  exact pairAutomizer_isCyclic_of_outer _ _ houter
    (symplectic_inner_centralizes_of_normalizes hF (by omega) e h hnorm)

/-- The symplectic source branch, with only the earlier universal multiplier
implication explicit. Placement follows from the permuting pair, while the
exceptional graph map and semilinear classification supply outer cyclicity. -/
theorem symplectic_surviving_case
    (hmult : SymplecticCentralKernelTheorem.{u}) {n : ℕ}
    (h : PairInput S R) (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n)) :
    Nonempty (R ≃* Plane 3) ∧ SymplecticModel 3 Q ∧
      IsCyclic (pairAutomizer (S : Subgroup Q) R) := by
  have hcenter := symplectic_center_eq_bot_of_multiplier hmult h hn hmodel
  obtain ⟨F, hfield, hfinite, hF, ⟨e⟩⟩ :=
    full_symplectic_of_projective_quotient hcenter hmodel
  let _ := hfield
  let _ := hfinite
  let _ : CharP F 2 := EvenProjective.charTwo_of_card hF
  have houter : IsCyclic (MulAut.Outer (Sp F)) :=
    DiagramAutomorphisms.ExceptionalGraph.outer_isCyclic_of_card hF (by omega)
      DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram
  exact symplectic_case_of_normalizes_of_outer h hn hcenter hmodel
    (symplectic_normalizes hF hn e h) ((MulAut.outerCongr e).isCyclic.mpr houter)

/-- The symplectic alternative for the characteristic-two rank-two sieve. -/
theorem symplectic_case
    (hmult : SymplecticCentralKernelTheorem.{u}) {n : ℕ}
    (h : PairInput S R) (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp (Q ⧸ center Q) 2 (2^n)) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ SymplecticModel 3 Q ∧
        IsCyclic (pairAutomizer (S : Subgroup Q) R)) :=
  Or.inr (symplectic_surviving_case hmult h hn hmodel)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
