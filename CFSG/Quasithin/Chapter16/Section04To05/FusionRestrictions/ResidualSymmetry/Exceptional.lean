module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Basic
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Intrinsic.Action
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.ThreeResidual
public import Theory.AtlasPort.ExceptionalIsomorphisms.Elementary
public import Theory.Representation.SU3.BinaryDegree.Perfectness
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Exceptional two-perfectness for Notation 16.5.5

For L ≅ PSL₃(2ⁿ), with n even and n > 2, the modification of Lᵤ is
O³(Lᵤ). In the inner row the literal projective highest-root centralizer
has a Heisenberg two-kernel and cubic torus weights. Its three-residual
is two-perfect by the commutator calculation in `ThreeResidual`.
For the field, graph and graph-field rows, the actual two-residual is
PSL₃(2ⁿᐟ²), PSL₂(2ⁿ), or PSU₃(2ⁿᐟ²); their proved perfectness invokes
`modifiedResidual_twoPerfect_of_perfect`.

The permitted earlier row inputs below are isomorphisms of the actual
fixed subgroup or its two-residual. They assert neither two-perfectness
of the modified residual nor a classification from group-family labels.
The exhaustive involutory-automorphism classification is a separate earlier
input. Unitary parameters use the fixed-field order, and the projective
inner model retains the cubic scalar kernel.

The ambient equivalence uses restriction of conjugation by the specified
actor. Transport to Lᵍ gives both actors' two-perfectness from a single
row table for L. The last theorem feeds these deductions into the existing
common-residual construction. Its earlier row, n > 2, cross-containment,
normalization and faithfulness inputs remain explicit; it does not claim
all the other clauses of source 16.5.6.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.1.4(1),(4)–(6), 16.4.8 and Notation 16.5.5,
printed pp.1171–1172, 1187–1188 and 1197.
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Exceptional
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter16.ComponentTransfer
open Matrix.PSL3.EvenInnerCentralizers.ThreeResidual

private noncomputable def residualEquiv {C D : Type*} [Group C] [Group D]
    (p : ℕ) (e : C ≃* D) : pResidual p C ≃* pResidual p D :=
  (e.subgroupMap _).trans (MulEquiv.subgroupCongr (map_pResidual p e))

/-- The needed portion of the earlier local table, applied to the actual fixed
subgroup C. The inner row identifies all of C; the outer rows identify O²(C).
Each model predicate contains a genuine multiplicative equivalence. -/
@[expose] def LocalCentralizerRow (C : Type*) [Group C] (n : ℕ) : Prop :=
  (∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
    Nonempty (C ≃* Matrix.PSL3.EvenInnerCentralizers.centralizer F)) ∨
  ClassicalGroup.IsPSL (pResidual 2 C) 3 (2 ^ (n / 2)) ∨
  ClassicalGroup.IsPSL (pResidual 2 C) 2 (2 ^ n) ∨
  ClassicalGroup.IsPSU (pResidual 2 C) 3 (2 ^ (n / 2))

/-- Earlier local rows for every actual involutory automorphism of A.
This is an explicit input to the local deduction, not a proved classification. -/
@[expose] def InvolutionRows (A : Type*) [Group A] (n : ℕ) : Prop :=
  ∀ a : MulAut A, orderOf a = 2 → LocalCentralizerRow a.fixedSubgroup n

/-- A fixed-subgroup isomorphism transports all rows and their intrinsic residuals. -/
theorem LocalCentralizerRow.of_equiv {C D : Type*} [Group C] [Group D]
    {n : ℕ} (h : LocalCentralizerRow C n) (e : C ≃* D) : LocalCentralizerRow D n := by
  rcases h with ⟨F, hF, hfin, hcard, ⟨d⟩⟩ | h | h | h
  · exact Or.inl ⟨F, hF, hfin, hcard, ⟨e.symm.trans d⟩⟩
  · exact Or.inr (Or.inl (h.of_mulEquiv (residualEquiv 2 e).symm))
  · exact Or.inr (Or.inr (Or.inl (h.of_mulEquiv (residualEquiv 2 e).symm)))
  · exact Or.inr (Or.inr (Or.inr (h.of_mulEquiv (residualEquiv 2 e).symm)))

/-- Transport the table by conjugating automorphisms through the specified group isomorphism. -/
theorem InvolutionRows.of_equiv {A B : Type*} [Group A] [Group B]
    {n : ℕ} (h : InvolutionRows A n) (e : A ≃* B) : InvolutionRows B n := by
  intro a ha
  exact (h (MulAut.congr e.symm a) (((MulAut.congr e.symm).orderOf_eq a).trans ha)).of_equiv
    (MulAut.fixedSubgroupCongr e.symm a).symm

private theorem perfect_of_outerRow {C : Type*} [Group C] {n : ℕ}
    (hn : 2 < n) (he : Even n)
    (h : ClassicalGroup.IsPSL (pResidual 2 C) 3 (2 ^ (n / 2)) ∨
      ClassicalGroup.IsPSL (pResidual 2 C) 2 (2 ^ n) ∨
      ClassicalGroup.IsPSU (pResidual 2 C) 3 (2 ^ (n / 2))) :
    Group.IsPerfect (pResidual 2 C) := by
  rcases h with h | h | h
  · obtain ⟨F, _, _, _, ⟨e⟩⟩ := h
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) :=
      Atlas.psl_perfect 3 (by decide)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
    have hq : 3 < Nat.card F := by
      rw [hcard]
      have := Nat.pow_le_pow_right (n := 2) (by decide : 1 ≤ 2) (show 2 ≤ n by omega)
      omega
    let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
      GorensteinWalter.psl2_isPerfect_of_card_gt_three F hq
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · obtain ⟨F, _, _, J, hcard, hconj, ⟨e⟩⟩ := h
    have hhalf : 2 ≤ n / 2 := by obtain ⟨k, hk⟩ := he; omega
    let : Group.IsPerfect (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Representation.SU3.BinaryDegree.isPerfect_projective J hhalf hcard hconj
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

variable {G : Type*} [Group G] [Finite G]

/-- Identify the embedded Lᵤ with the intrinsic fixed two-residual for conjugation by u.
There is no quotient of L by its center in this identification. -/
noncomputable def ambientTwoResidualEquivFixed {L : Subgroup G} {u : G}
    (hu : u ∈ normalizer (L : Set G)) :
    involutionTwoResidual L u ≃* pResidual 2 (Intrinsic.action hu).fixedSubgroup :=
  ((pResidual 2 (L ⊓ centralizer ({u} : Set G) : Subgroup G)).equivMapOfInjective
    (L ⊓ centralizer ({u} : Set G)).subtype Subtype.val_injective).symm.trans
      (residualEquiv 2 (Intrinsic.centralizerEquivFixed hu))

/-- The exceptional local deduction from the earlier row for the specified ambient action.
The bound n > 2 excludes the nonperfect graph-field endpoint and the trivial inner torus. -/
theorem modifiedResidual_twoPerfect_of_localRow {L : Subgroup G} {u : G} {n : ℕ}
    (hn : 2 < n) (he : Even n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hu : u ∈ normalizer (L : Set G))
    (hrow : LocalCentralizerRow (Intrinsic.action hu).fixedSubgroup n) :
    IsPPerfect 2 (modifiedCentralizerResidual L u) := by
  let e := ambientTwoResidualEquivFixed hu
  rcases hrow with hinner | houter
  · obtain ⟨F, _, _, hF, ⟨c⟩⟩ := hinner
    let d := e.trans (residualEquiv 2 c)
    let d3 := residualEquiv 3 d
    have hp : IsPPerfect 2 (pResidual 3 (involutionTwoResidual L u)) :=
      (twoThreeResidual_twoPerfect F hn he hF).of_surjective
        d3.symm.toMonoidHom d3.symm.surjective
    have hL : HasEvenLinearThreeType L := ⟨n, by omega, he, hmodel⟩
    classical
    rw [modifiedCentralizerResidual, if_pos hL]
    let j := (pResidual 3 (involutionTwoResidual L u)).equivMapOfInjective
      (involutionTwoResidual L u).subtype Subtype.val_injective
    exact hp.of_surjective j.toMonoidHom j.surjective
  · let := perfect_of_outerRow hn he houter
    let : Group.IsPerfect (involutionTwoResidual L u) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    exact modifiedResidual_twoPerfect_of_perfect u

/-- An involutory ambient action selects its actual fixed-subgroup row. -/
theorem modifiedResidual_twoPerfect_of_involutionRows {L : Subgroup G} {u : G} {n : ℕ}
    (hn : 2 < n) (he : Even n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hrows : InvolutionRows L n) (hu : u ∈ normalizer (L : Set G))
    (ha : orderOf (Intrinsic.action hu) = 2) :
    IsPPerfect 2 (modifiedCentralizerResidual L u) :=
  modifiedResidual_twoPerfect_of_localRow hn he hmodel hu (hrows _ ha)

omit [Finite G] in
private theorem faithful_action_order {L A : Subgroup G}
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) {u : G}
    (hu : u ∈ A) (hu2 : orderOf u = 2) :
    orderOf (Intrinsic.action (hA hu)) = 2 := by
  let a : normalizer (L : Set G) := ⟨u, hA hu⟩
  have hs : a ^ 2 = 1 := Subtype.ext (hu2 ▸ pow_orderOf_eq_one u)
  have hp : Intrinsic.action (hA hu) ^ 2 = 1 := by
    change L.normalizerMonoidHom a ^ 2 = 1
    rw [← map_pow, hs, map_one]
  apply orderOf_eq_prime hp
  intro he
  have hk : a ∈ L.normalizerMonoidHom.ker := he
  rw [normalizerMonoidHom_ker] at hk
  have hu1 : u = 1 := by
    have hm : u ∈ A ⊓ centralizer (L : Set G) := ⟨hu, hk⟩
    rwa [hfaith, mem_bot] at hm
  simp [hu1] at hu2

/-- Every involution of a faithful normalizing actor supplies the required two-perfect residual. -/
theorem actor_modifiedResidual_twoPerfect {L A : Subgroup G} {n : ℕ}
    (hn : 2 < n) (he : Even n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hrows : InvolutionRows L n)
    (hA : A ≤ normalizer (L : Set G))
    (hfaith : A ⊓ centralizer (L : Set G) = ⊥) :
    ∀ u ∈ A, orderOf u = 2 → IsPPerfect 2 (modifiedCentralizerResidual L u) := by
  intro u hu hu2
  exact modifiedResidual_twoPerfect_of_involutionRows hn he hmodel hrows (hA hu)
    (faithful_action_order hA hfaith hu hu2)

/-- The same table for L supplies both actors, including the one acting on the actual Lᵍ. -/
theorem conjugate_actors_twoPerfect {L A B : Subgroup G} {g : G} {n : ℕ}
    (hn : 2 < n) (he : Even n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hrows : InvolutionRows L n)
    (hA : A ≤ normalizer (L : Set G))
    (hfaithA : A ⊓ centralizer (L : Set G) = ⊥)
    (hB : B ≤ normalizer (L.conjBy g : Set G))
    (hfaithB : B ⊓ centralizer (L.conjBy g : Set G) = ⊥) :
    (∀ u ∈ A, orderOf u = 2 → IsPPerfect 2 (modifiedCentralizerResidual L u)) ∧
      (∀ i ∈ B, orderOf i = 2 →
        IsPPerfect 2 (modifiedCentralizerResidual (L.conjBy g) i)) := by
  let e : L ≃* L.conjBy g := (MulAut.conj g).subgroupMap L
  exact ⟨actor_modifiedResidual_twoPerfect hn he hmodel hrows hA hfaithA,
    actor_modifiedResidual_twoPerfect hn he (hmodel.of_mulEquiv e.symm)
      (hrows.of_equiv e) hB hfaithB⟩

/-- Preserve the marked residual subgroup and two-perfectness under ambient conjugation
or any other ambient automorphism; both L and the specified actor are transported. -/
theorem modifiedResidual_map_and_twoPerfect {L : Subgroup G} {u : G} {n : ℕ}
    (hn : 2 < n) (he : Even n) (hmodel : ClassicalGroup.IsPSL L 3 (2 ^ n))
    (hu : u ∈ normalizer (L : Set G))
    (hrow : LocalCentralizerRow (Intrinsic.action hu).fixedSubgroup n) (e : G ≃* G) :
    (modifiedCentralizerResidual L u).map e.toMonoidHom =
        modifiedCentralizerResidual (L.map e.toMonoidHom) (e u) ∧
      IsPPerfect 2 (modifiedCentralizerResidual (L.map e.toMonoidHom) (e u)) := by
  have hp := modifiedResidual_twoPerfect_of_localRow hn he hmodel hu hrow
  have hm := modifiedCentralizerResidual_map L u e
  refine ⟨hm, ?_⟩
  rw [← hm]
  let d := e.subgroupMap (modifiedCentralizerResidual L u)
  exact hp.of_surjective d.toMonoidHom d.surjective

/-- Feed the exceptional local calculation into the common-residual consumer.
Only the earlier local table and n > 2 exclusion are needed in the exceptional case;
there is no assumed two-perfectness of either modified residual. -/
theorem exists_common_residual_conjugate_of_rows
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (htransport : R = (commutingSylow T L).conjBy g)
    (hforward : ∀ u ∈ R, orderOf u = 2 →
      modifiedCentralizerResidual L u ≤ L.conjBy g)
    (hbackward : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i ≤ L)
    (hfaithR : R ⊓ centralizer (L : Set G) = ⊥)
    (hnormalC : commutingSylow T L ≤ normalizer (L.conjBy g : Set G))
    (hfaithC : commutingSylow T L ⊓ centralizer (L.conjBy g : Set G) = ⊥)
    (hrows : HasEvenLinearThreeType L → ∃ n : ℕ,
      2 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧ InvolutionRows L n) :
    ∃ X : Subgroup G, X ≤ L ⊓ L.conjBy g ∧
      R ⊔ commutingSylow T L ≤ centralizer (X : Set G) ∧
      (∀ u ∈ R, orderOf u = 2 → modifiedCentralizerResidual L u = X) ∧
      (∀ i ∈ commutingSylow T L, orderOf i = 2 →
        modifiedCentralizerResidual (L.conjBy g) i = X) := by
  have hboth (hL : HasEvenLinearThreeType L) :
      (∀ u ∈ R, orderOf u = 2 → IsPPerfect 2 (modifiedCentralizerResidual L u)) ∧
      (∀ i ∈ commutingSylow T L, orderOf i = 2 →
        IsPPerfect 2 (modifiedCentralizerResidual (L.conjBy g) i)) := by
    obtain ⟨n, hn, he, hm, hr⟩ := hrows hL
    exact conjugate_actors_twoPerfect hn he hm hr
      (h.le_sylow.trans h.sylow_normalizes) hfaithR hnormalC hfaithC
  apply exists_common_residual_conjugate h htransport hforward hbackward
  · exact fun hL => (hboth hL).1
  · intro hL
    exact (hboth ((hasEvenLinearThreeType_map_iff L (MulAut.conj g)).mp hL)).2

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Exceptional
