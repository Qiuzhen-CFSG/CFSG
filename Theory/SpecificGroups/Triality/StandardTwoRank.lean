module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.QuasithinBasic

/-!
# A derived elementary subgroup in binary triality

For the genuine graph-field carrier `³D₄(2^n)`, the three-arm Levi is a
perfect `PSL₂` over the cubic coefficient field.  Its upper root subgroup
therefore lies in the derived subgroup of the full carrier and is elementary
abelian of order `2^(3*n)`.  This supplies a source-independent lower bound
on the two-rank of both the carrier and its derived subgroup, including
`n = 1`, and transports it through the actual standard-model equivalences.

The sharp source calculation `m₂(³D₄(2^n)) = m₂(Aut(³D₄(2^n))) = 5n`
requires the full finite root-coordinate/Sylow computation and the sharp
semilinear automorphism calculation.  Those statements are deliberately not
inferred here from the root subgroup or a family label.

Sources: GLS3, Chapter 2, especially the folded arm Levi construction in
§§2.4--2.6; Aschbacher--Smith, the rank table used in G.9, printed p.356
(`refs/quasithin.pdf`).
-/

@[expose] public section
noncomputable section

open Matrix
open scoped MatrixGroups
namespace Triality.Standard.TwoRank
open Parabolics EvenInvolutionGeometry Theory.GroupTheory

variable (n : ℕ) (hn : 0 < n)
local notation "P" => binaryParameters n hn

/-- The folded three-arm Levi belongs to the carrier's derived subgroup. -/
theorem armsLevi_le_commutator :
    levi P .arms ≤ commutator (BinaryCarrier n hn) := by
  let := levi_arms_isPerfect_of_pinnedMaps P rfl
    (pinnedRankOneMaps P rfl) (armRootCommutation P rfl)
  rw [← Subgroup.commutator_eq_self (H := levi P .arms)]
  exact Subgroup.commutator_mono le_top le_top

/-- A folded short-root element lies in the three-arm Levi. -/
theorem shortRoot_mem_armsLevi (t : ExtensionField P) :
    shortRoot n hn t ∈ levi P .arms := by
  refine ⟨sl2ElementaryLift P rfl (shortRankOneFixed n hn)
    (SpecialLinearGroup.upperUnipotentHom _ (Multiplicative.ofAdd t)), ?_, rfl⟩
  exact ((pinnedRankOneMaps P rfl).range_armsFixedEmbedding
    (armRootCommutation P rfl)).le ⟨_, rfl⟩ |>.1

/-- A folded short-root element belongs to the carrier's derived subgroup. -/
theorem shortRoot_mem_commutator (t : ExtensionField P) :
    shortRoot n hn t ∈ commutator (BinaryCarrier n hn) :=
  armsLevi_le_commutator n hn (shortRoot_mem_armsLevi n hn t)

/-- The full cubic short-root group, regarded inside the derived subgroup. -/
def shortRootDerivedHom : Multiplicative (ExtensionField P) →*
    commutator (BinaryCarrier n hn) :=
  (shortRootHom n hn).codRestrict _ (fun t => shortRoot_mem_commutator n hn t.toAdd)

theorem shortRootDerivedHom_injective : Function.Injective (shortRootDerivedHom n hn) := by
  intro a b h
  exact shortRootHom_injective n hn (congrArg Subtype.val h)

/-- The derived subgroup contains the elementary cubic short-root group. -/
theorem derived_twoRank_ge_three_mul :
    3 * n ≤ primeRank 2 (commutator (BinaryCarrier n hn)) := by
  apply primeRank_ge_of_elementary_embedding (f := shortRootDerivedHom n hn)
  · intro a
    change 2 • a.toAdd = 0
    rw [two_nsmul]
    exact CharTwo.add_self_eq_zero a.toAdd
  · change Nat.card (ExtensionField P) = 2 ^ (3 * n)
    exact GaloisField.card 2 (3 * n) (by omega)
  · exact shortRootDerivedHom_injective n hn

/-- The carrier has two-rank at least the dimension of its cubic short-root group. -/
theorem twoRank_ge_three_mul : 3 * n ≤ primeRank 2 (BinaryCarrier n hn) :=
  (derived_twoRank_ge_three_mul n hn).trans
    (primeRank_le_of_injective 2 (commutator (BinaryCarrier n hn)).subtype
      Subtype.val_injective)

/-- An actual model equivalence transports to an equivalence of derived subgroups. -/
noncomputable def derivedEquivOfModel {G : Type*} [Group G]
    (e : G ≃* BinaryCarrier n hn) : commutator G ≃* commutator (BinaryCarrier n hn) :=
  (e.subgroupMap (commutator G)).trans (MulEquiv.subgroupCongr (by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.surjective]
    rfl))

include hn in
/-- The lower bound holds for every genuine standard parameter at field order `2^n`. -/
theorem derived_twoRank_ge_three_mul_of_parameters (Q : Parameters) (hq : Q.q = 2 ^ n) :
    3 * n ≤ primeRank 2 (commutator (Carrier Q)) := by
  rw [Q.eq_binaryParameters_of_q_eq n hn hq]
  exact derived_twoRank_ge_three_mul n hn

include hn in
/-- The lower bound transports through every genuine triality-family witness. -/
theorem derived_twoRank_ge_three_mul_of_model {G : Type*} [Group G]
    (hG : IsTrialityGroupAt (2 ^ n) G) : 3 * n ≤ primeRank 2 (commutator G) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff G n hn).mp hG
  let : Finite G := Finite.of_injective e e.injective
  rw [primeRank_equiv 2 (derivedEquivOfModel n hn e)]
  exact derived_twoRank_ge_three_mul n hn

end Triality.Standard.TwoRank
