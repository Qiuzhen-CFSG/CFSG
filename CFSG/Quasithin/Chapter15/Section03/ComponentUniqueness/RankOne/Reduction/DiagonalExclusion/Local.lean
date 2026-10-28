module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.Reduction.Preliminary
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.Alternatives
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.SectionCentralizers

/-!
# Source inputs for the inner-action step of 15.3.43

The common input retains the actual component of I, the common Sylow subgroup,
the theta and normalizer identities, and the invariant characteristic-two
subgroup control of 15.3.33(1). The residual identity and index are the output
of `Reduction.Preliminary`. The plane data records (b)--(d), without assuming
component containment, component normality in I, or inner action.

In particular, the nontriviality of `O²(Y₊ ∩ L)` is NOT included: the earlier
15.3.12 proves it only under the rank-two hypothesis on Y₊. Nor does this
interface assert that failure of innerness implies the diagonal alternative.
Those are mathematical obligations in the present S₃ branch.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 15.3.11,
15.3.33--34, and 15.3.43(a)--(d), printed pp.1123--1125, 1134, and 1139.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion

variable {G : Type*} [Group G]

/-- Genuine earlier local inputs, with the two deductions of clause (a). -/
structure LocalSetup (Yplus S M I L : Subgroup G) : Prop where
  outside : I ∈ outsideFamily Yplus S M
  sylow : ∃ P : Sylow 2 I, (P : Subgroup I).map I.subtype = S
  sylow_le : S ≤ M
  component_le : L ≤ I
  component : IsComponent I (L.subgroupOf I)
  component_outside : ¬ L ≤ M
  odd_core : pPrimeCore 2 I = ⊥
  orbit_bound : (normalizer (L : Set G)).relIndex I ≤ 2
  theta_eq : theta (M ⊓ I) = Yplus
  normalizer_eq : I ⊓ normalizer (Yplus : Set G) = M ⊓ I
  local_fitting : generalizedFitting (M ⊓ I : Subgroup G) =
    pCore 2 (M ⊓ I : Subgroup G)
  rank_positive : 1 ≤ primeRank 3 L
  rank_overgroup : primeRank 3 I ≤ 2
  characteristic_two_containment : ∀ D : Subgroup G, D ≤ localSpan L S →
    Yplus ⊔ S ≤ normalizer (D : Set G) →
    generalizedFitting D = pCore 2 D → D ≤ M ⊓ I
  shadow : SymmetricThreeShadow Yplus S
  residual : Yplus = threeResidualIn (M ⊓ I)
  index : (pCore 2 Yplus).index = 3

/-- The actual plane information available before the inner-action step.
The source owner must construct these fields; this is not a conclusion record
for innerness or for the diagonal exclusion. -/
structure PlaneData (Yplus S M I V₁ V₂ : Subgroup G) : Prop where
  first_le : V₁ ≤ S
  second_le : V₂ ≤ S
  first_centralizes : ⁅V₁, Yplus⁆ = ⊥
  first_normalizer : normalizer (V₁ : Set G) ≤ M
  second_normalizer : normalizer (V₂ : Set G) ≤ M
  second_elementary : IsElementaryAbelian 2 V₂
  second_card : Nat.card V₂ = 4
  second_commutator : ⁅V₂, Yplus⁆ = V₂
  second_normalized : M ⊓ I ≤ normalizer (V₂ : Set G)
  not_alternating_four : ¬ Nonempty (Yplus ≃* alternatingGroup (Fin 4))

variable {Yplus S M I L : Subgroup G}

theorem LocalSetup.yplus_le (h : LocalSetup Yplus S M I L) : Yplus ≤ M ⊓ I := by
  rw [← h.theta_eq]
  exact theta_le _

theorem LocalSetup.sylow_le_overgroup (h : LocalSetup Yplus S M I L) : S ≤ I :=
  le_sup_right.trans h.outside.1.2

variable [Finite G]

omit [Finite G] in
/-- The quotient of Y₊ by its two-core is a genuine three-group. -/
theorem LocalSetup.quotient_three (h : LocalSetup Yplus S M I L) :
    IsPGroup 3 (Yplus ⧸ pCore 2 Yplus) :=
  IsPGroup.of_card (n := 1) (by simpa only [pow_one, ← Subgroup.index_eq_card] using h.index)

omit [Finite G] in
/-- Theta generation also supplies the full local normality of Y₊. -/
theorem LocalSetup.local_normalizes (h : LocalSetup Yplus S M I L) :
    M ⊓ I ≤ normalizer (Yplus : Set G) := by
  rw [← h.theta_eq]
  exact (M ⊓ I).le_normalizer.trans (normalizer_le_normalizer_theta _)

/-- The actual S₃ shadow makes the full join solvable, which is used in
constructing an invariant component Borel. -/
theorem LocalSetup.join_solvable (h : LocalSetup Yplus S M I L) :
    Group.IsSolvable (Yplus ⊔ S : Subgroup G) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
    apply Group.isSolvable_of_ker_le_range
      (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
    rw [range_subtype, ← alternatingGroup_eq_sign_ker]
  obtain ⟨e⟩ := h.shadow
  let : Group.IsSolvable ((Yplus ⊔ S : Subgroup G) ⧸ pCore 2 (Yplus ⊔ S : Subgroup G)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  let : Group.IsNilpotent (pCore 2 (Yplus ⊔ S : Subgroup G)) := pCore_isPGroup.isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient
    (pCore 2 (Yplus ⊔ S : Subgroup G))).mpr ⟨inferInstance, inferInstance⟩

/-- The orbit bound and order-three generation give normalization of the actual
component, without assuming that the whole overgroup I normalizes it. -/
theorem LocalSetup.yplus_normalizes (h : LocalSetup Yplus S M I L) :
    Yplus ≤ normalizer (L : Set G) :=
  ComponentIntersection.normalizes_of_index_le_two
    (le_sup_left.trans h.outside.1.2)
    (h.theta_eq ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)) h.orbit_bound

/-- In the single-component alternatives S also normalizes L. -/
theorem LocalSetup.join_normalizes (h : LocalSetup Yplus S M I L)
    (horbit : L = localSpan L S) : Yplus ⊔ S ≤ normalizer (L : Set G) := by
  refine sup_le h.yplus_normalizes ?_
  rw [horbit]
  exact le_normalizer_conjugateSpanBy L S

omit [Finite G] in
/-- Every proposed Borel together with its supplied diagonal actor is actually
in M ∩ I, once the invariant characteristic-two Borel has been constructed. -/
theorem LocalSetup.borel_join_actor_le (h : LocalSetup Yplus S M I L)
    {B : Subgroup G} (hBL : B ≤ localSpan L S)
    (hBnorm : Yplus ⊔ S ≤ normalizer (B : Set G))
    (hBfit : generalizedFitting B = pCore 2 B)
    {y : G} (hy : y ∈ Yplus) : B ⊔ zpowers y ≤ M ⊓ I := by
  exact sup_le (h.characteristic_two_containment B hBL hBnorm hBfit)
    (zpowers_le.mpr (h.yplus_le hy))

/-- The rank obstruction applies to the Borel AND the actor. It makes no
incorrect claim that a PSL₃(4) Borel alone has three-rank greater than one. -/
theorem LocalSetup.no_high_rank_borel_join_actor (h : LocalSetup Yplus S M I L)
    {B : Subgroup G} (hBL : B ≤ localSpan L S)
    (hBnorm : Yplus ⊔ S ≤ normalizer (B : Set G))
    (hBfit : generalizedFitting B = pCore 2 B)
    {y : G} (hy : y ∈ Yplus) : ¬ 1 < primeRank 3 (B ⊔ zpowers y : Subgroup G) :=
  no_high_three_rank_subgroup h.residual h.index
    (h.borel_join_actor_le hBL hBnorm hBfit hy)

end CFSG.Quasithin.Chapter15.Section03.RankOne.DiagonalExclusion
