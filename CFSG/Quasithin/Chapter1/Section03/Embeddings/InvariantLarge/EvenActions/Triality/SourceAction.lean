module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.Geometry
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Triality.SourceAlignment
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage

/-!
# The source triality Cartan action on the Frattini quotient

For the raw A.3.15(5) configuration on the genuine triality carrier, field and
inner-diagonal separation places the inner image of B in the relative Cartan.
Thus B normalizes S ∩ D. The concrete positive Sylow subgroup and Borel geometry
then give simultaneous Sylow and torus coordinates. The inner factor of each
normalizer automorphism centralizes B, and the cubic coefficient factor acts
by a uniform power. This identity descends to the actual action on B/Φ(B).

The conditional power formulas retain the precise binary automorphism-coverage
premise. In `frattini_power_of_raw`, the existing coverage theorem discharges it
using simplicity and perfectness transported from the nonabelian simple D.
`frattini_power_of_source` applies this result to the full ambient SQTK input.
Neither final theorem assumes geometry, alignment, or a power-action conclusion.
The raw theorem also includes B = 1, without a three-residual premise.

The full cubic coefficient group is used only in the automorphism decomposition;
it includes the order-three graph contribution and is distinct from the raw
source field subgroup F. All restrictions and quotients are those of the
original graph-field fixed group and its elementary central quotient.

Source: Aschbacher–Smith, `refs/quasithin.pdf`, Notation A.2.5, printed p.33,
Lemma A.3.15(5), pp.50–51, and the proof of Proposition 1.3.4, p.511;
GLS3 §§2.3–2.6, `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
noncomputable section
open Subgroup
open Triality.Standard Triality.Standard.Parabolics Triality.Standard.OuterOdd
open Triality.Standard.CartanAction
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality
open SourceAlignment

private theorem raw_alignment
    {J : Type*} [Group J] [Finite J] {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hB : IsPGroup p B) (P : Parameters) (n : ℕ) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom)) : HasCartanAlignment D B S P := by
  have hchar : P.prime = 2 := by
    rw [P.eq_binaryParameters_of_q_eq n (lt_trans Nat.zero_lt_one hraw.degree_gt_one) hraw.q_eq]
    rfl
  have hBN : B.subgroupOf D ≤ normalizer ((S : Subgroup J).subgroupOf D) := by
    have h := hraw.normalizes
      (sourceField_eq_one_of_mem_innerDiagonal P hchar)
    rw [← map_normalizer_eq_of_bijective _ e.bijective] at h
    exact (map_le_map_iff_of_injective e.injective).mp h
  obtain ⟨U, hU⟩ := exists_unipotentSylow P hchar
  exact hasCartanAlignment_of_normalizes D B S P (borelGeometry P hchar)
    U hU e hp hB hBN

/-- The raw Cartan configuration gives a uniform power formula for each element
of N_S(B), with only the binary automorphism decomposition left explicit. -/
theorem conjugation_power_of_raw_of_coverage
    {J : Type*} [Group J] [Finite J] {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hB : IsPGroup p B) (hBD : B ≤ D)
    (P : Parameters) (n : ℕ) (hn : 0 < n) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom))
    (hcover : ∀ a : MulAut (BinaryCarrier n hn), ∃ d : BinaryCarrier n hn,
      ∃ σ : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj d * coefficientAction (binaryParameters n hn) σ) :
    ∀ s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J), ∃ k : ℕ,
      ∀ b : B, (s : J) * (b : J) * (s : J)⁻¹ = (b : J) ^ (2 ^ k) := by
  have hchar : P.prime = 2 := by
    rw [P.eq_binaryParameters_of_q_eq n hn hraw.q_eq]
    rfl
  exact conjugation_power_of_alignment D B S hBD P n hn hraw.q_eq
    (borelGeometry P hchar) hcover (raw_alignment S (by omega) hB P n e hraw)

/-- The power formula descends through B's own Frattini subgroup for the literal
ambient normalizer action. Geometry and source alignment are discharged. -/
theorem frattini_power_of_raw_of_coverage
    {J : Type*} [Group J] [Finite J] {D B : Subgroup J} [D.Normal]
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hB : IsPGroup p B) (hBD : B ≤ D)
    (P : Parameters) (n : ℕ) (hn : 0 < n) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom))
    (hcover : ∀ a : MulAut (BinaryCarrier n hn), ∃ d : BinaryCarrier n hn,
      ∃ σ : CoefficientAut (binaryParameters n hn),
        a = MulAut.conj d * coefficientAction (binaryParameters n hn) σ) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  apply frattini_action_pow
  intro s
  obtain ⟨k, hk⟩ := conjugation_power_of_raw_of_coverage S hp hB hBD P n hn e hraw hcover s
  exact ⟨2 ^ k, hk⟩

/-- In the raw A.3.15(5) case, every N_S(B)-orbit of v in B/Φ(B) stays in
its cyclic subgroup. The nonabelian simple component supplies the instances
needed to discharge binary automorphism coverage. -/
theorem frattini_power_of_raw
    {J : Type*} [Group J] [Finite J] {D B : Subgroup J} [D.Normal] [IsSimpleGroup D]
    (hna : ¬ IsMulCommutative D)
    (S : Sylow 2 J) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hB : IsPGroup p B) (hBD : B ≤ D)
    (P : Parameters) (n : ℕ) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom)) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  have hn : 0 < n := by have := hraw.degree_gt_one; omega
  have hP := P.eq_binaryParameters_of_q_eq n hn hraw.q_eq
  subst P
  let : Group.IsPerfect D := ⟨
    (inferInstance : (commutator D).Normal).eq_bot_or_eq_top.resolve_left
      (fun h => hna ((commutator_eq_bot_iff D).mp h))⟩
  let : IsSimpleGroup (BinaryCarrier n hn) := e.symm.isSimpleGroup
  let : Group.IsPerfect (BinaryCarrier n hn) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact frattini_power_of_raw_of_coverage S hp hB hBD _ n hn e hraw
    (Coverage.binary_inner_coefficient n hn)

/-- The triality Cartan-action step in Proposition 1.3.4, applied to the full
finite SQTK ambient input and every clause of the raw A.3.15(5) configuration. -/
theorem frattini_power_of_source
    {J : Type*} [Group J] [Finite J] {κ : GroupClass}
    {D B : Subgroup J} {S : Sylow 2 J} {p : ℕ}
    (hA : AmbientInput κ D B S p)
    (P : Parameters) (n : ℕ) (e : D ≃* Carrier P)
    (hraw : RawConfiguration P n
      (((S : Subgroup J).subgroupOf D).map e.toMonoidHom)
      ((B.subgroupOf D).map e.toMonoidHom)) :
    ∀ (s : ((S : Subgroup J) ⊓ normalizer B : Subgroup J)) (v : B ⧸ frattini B),
      CFSG.Quasithin.Chapter1.frattiniConjugationAction
        ((S : Subgroup J) ⊓ normalizer B) B inf_le_right s v ∈ zpowers v := by
  let : D.Normal := hA.normal
  let : IsSimpleGroup D := hA.simple
  let : Fact p.Prime := ⟨hA.prime⟩
  exact frattini_power_of_raw hA.nonabelian S hA.large hA.p_group hA.inside P n e hraw

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Triality
