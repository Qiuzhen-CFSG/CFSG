module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.CoreRemoval
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.LinearCore
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.Candidates.RankAlternatives.DiagonalProduct.UnitaryLocal
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.OddRank.Intersection
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Assembly of the rank-two diagonal product

The signed intermediate alternative already fixes L = ⟨L^S⟩ and supplies
an order-three actor with a compatible actual matrix action. For the
linear branch, the congruence 2ⁿ ≡ 1 (mod 3) forces n even. We retain the
same actor, field and equivalence, including the L/O₂(L) ≃ PSL₃(4) case.
Nontriviality of O²(Y₊ ∩ L) comes from the rank argument in 15.3.12(1).

The original conditional assembly is retained. The source assembly
`rankTwoDiagonal_of_signed_of_source` discharges its unitary exclusion
with `UnitaryLocal` and its cover and core-action bound with `LinearCore`.
The latter removes the source O₂(Y) supplement by two-perfectness, without
assuming its triviality or exponent three for Y₊. The original actor,
field parameter and compatible quotient action are retained.

The source assembly constructs the linear setup from the selected ordinary
component and the earlier local conclusions. It derives relative normality,
nontriviality of the component residual, the component-core bound and the
three-group quotients. Its remaining inputs are the signed alternative,
the uniform earlier facts in `SourceBorel.Earlier`, the plane-normalizer
clause of 15.3.11(3), the full alternatives and residual image of 15.3.7,
and the natural-module conclusions Ω₁(Z(S)) ≤ V and C_V(Y) = 1.
The parent source assembly discharges these earlier inputs and the signed
alternative; no local model, product or containment conclusion is assumed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final
paragraph of 15.3.37 on printed p.1135, with 15.3.12(1), pp.1124--1125.
No containment result from 15.3.38--40 is used.
-/

public section

open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.Candidates
variable {G : Type*} [Group G] [Finite G]

private theorem even_of_two_pow_mod_three {n : ℕ} (hmod : 2 ^ n % 3 = 1) : Even n := by
  have h : 2 ^ n % 3 = if Even n then 1 else 2 := by
    clear hmod
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Nat.mul_mod, ih]
      by_cases hn : Even n <;> simp [hn, Nat.even_add_one]
  rw [h] at hmod
  split at hmod <;> simp_all

/-- Arithmetic, residual and action-compatible assembly. The unitary
exclusion and the core cover/action premises are separate obligations;
this conditional theorem does not discharge the local model argument. -/
theorem rankTwoDiagonal_of_signed_of_core_cover {Y Yplus S M I L : Subgroup G}
    (hI : I ∈ outsideFamily Yplus S M)
    (hθ : theta (M ⊓ I) = Yplus) (hLI : L ≤ I)
    (hindex : (normalizer (L : Set G)).relIndex I ≤ 2)
    (hYrank : primeRank 3 Yplus = 2) (hLrank : primeRank 3 L = 2)
    (hIrank : primeRank 3 I ≤ 2)
    (hsigned : DiagonalAlternative15343 Yplus L (localSpan L S))
    (hunitary : ∀ y ∈ Yplus, orderOf y = 3 →
      ∀ n : ℕ, 0 < n → 2 ^ n % 3 = 2 → ClassicalGroup.IsPSU L 3 (2 ^ n) →
        UnitaryDiagonalOnTwoQuotient L y (2 ^ n) → False)
    (hcover : ∀ y ∈ Yplus, orderOf y = 3 →
      ((∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
          LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨
        LinearDiagonalOnTwoQuotient L y 4) → DiagonalCoreCover Y Yplus L y) :
    RankTwoDiagonal Yplus L (localSpan L S) := by
  obtain ⟨horbit, y, hy, hy3, hmodel⟩ := hsigned
  have hlinear :
      (∃ n : ℕ, 0 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
        LinearDiagonalOnTwoQuotient L y (2 ^ n)) ∨
      LinearDiagonalOnTwoQuotient L y 4 := by
    rcases hmodel with ⟨n, hn, hmod, hL, hact⟩ | ⟨n, hn, hmod, hL, hact⟩ | hact
    · exact Or.inl ⟨n, hn, even_of_two_pow_mod_three hmod, hL, hact⟩
    · exact (hunitary y hy hy3 n hn hmod hL hact).elim
    · exact Or.inr hact
  have hY : IsPPerfect 2 Yplus := hθ ▸ ComponentIntersection.theta_isPPerfect (M ⊓ I)
  have hn : Yplus ≤ normalizer (L : Set G) :=
    ComponentIntersection.normalizes_of_index_le_two (le_sup_left.trans hI.1.2) hY hindex
  have hne : componentPart Yplus L ≠ ⊥ :=
    ComponentIntersection.intersectionResidual_ne_bot_of_local_facts hI hθ hLI hindex
      hYrank (by omega) hIrank
  exact ⟨horbit, hne, y, hy, hy3, (hcover y hy hy3 hlinear).product hY hy hn, hlinear⟩

open DiagonalOuter.CoverReduction

/-- The signed intermediate alternative implies every clause of 15.3.37(3)
under the genuine earlier rank-two local conclusions. The selected component
is ordinary and normal only relative to I. Nontriviality of its residual and
the core bound are deduced from 15.3.12(1), and 15.3.25 supplies invariant
characteristic-two containment through 15.3.33(1).

`earlier` retains the actual Sylow and O_{2,Φ} quotient. The other explicit
inputs are 15.3.11(3), 15.3.7, 15.3.8 and the natural residual action.
Neither unitary exclusion nor a product or matrix-action bound remains an
input. The source-theorem parent supplies these earlier conclusions and the
signed alternative; the same chosen actor and linear field survive. -/
theorem rankTwoDiagonal_of_signed_of_source {d : CharacteristicTwo.LocalData G}
    {I L : Subgroup G} (hI : I ∈ d.Hplus)
    (hLI : L ≤ I) (hL : IsComponent I (L.subgroupOf I))
    (hLrank : primeRank 3 L = 2) (hYrank : primeRank 3 d.Yplus = 2)
    (earlier : LocalCover.SourceBorel.Earlier d)
    (hsigned : DiagonalAlternative15343 d.Yplus L (localSpan L d.S))
    (hchoice : Chapter4.UniqueMaximalOvergroup (d.Y ⊔ d.S) d.M →
      d.Yplus = Stellmacher.twoResidualAmbient (d.Y ⊓ centralizer (d.V₁ : Set G)) →
      normalizer (d.V₁ : Set G) ≤ d.M ∧ normalizer (d.V₂ : Set G) ≤ d.M)
    (h7 : ThreeAlternatives.ElementaryAlternative d.M d.Mc d.V ∨
      ThreeAlternatives.ExtraspecialAlternative d.M d.Mc d.V d.action)
    (himage7 : d.action.image d.Y =
      Stellmacher.twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hΩ : centralOmegaIn d.S ≤ d.V)
    (hVY : d.V ⊓ centralizer (d.Y : Set G) = ⊥) :
    RankTwoDiagonal d.Yplus L (localSpan L d.S) := by
  have hnormal := LocalCover.rank_two_component_normal_in hLI hL
    (earlier.odd I hI) (earlier.rank I hI) hLrank
  have hn : I ≤ normalizer (L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hLI).mp hnormal
  have hindex : (normalizer (L : Set G)).relIndex I ≤ 2 := by
    rw [relIndex_eq_one.mpr hn]
    decide
  have hθ := earlier.theta_eq I hI
  have hne : componentPart d.Yplus L ≠ ⊥ :=
    ComponentIntersection.intersectionResidual_ne_bot_of_local_facts hI hθ hLI hindex
      hYrank (by omega) (earlier.rank I hI)
  obtain ⟨P, hP⟩ := earlier.sylow I hI
  have hSM : d.S ≤ d.M := inf_le_left.trans d.sylow_le
  have hYI : d.Yplus ≤ I := le_sup_left.trans hI.1.2
  have hSY : d.S ≤ normalizer (d.Yplus : Set G) := by
    rw [← hθ]
    exact (le_inf hSM (le_sup_right.trans hI.1.2)).trans
      ((d.M ⊓ I).le_normalizer.trans (normalizer_le_normalizer_theta _))
  have hLM : ¬ L ≤ d.M := by
    intro h
    apply component_not_le_characteristicTwo hL
      (earlier.intersection_characteristic_two I hI)
    intro x hx
    exact h hx
  let eMI : d.M.subgroupOf I ≃* (d.M ⊓ I : Subgroup G) :=
    { toFun := fun x => ⟨x, x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x, x.property.2⟩, x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have hMI : generalizedFitting (d.M ⊓ I : Subgroup G) =
      pCore 2 (d.M ⊓ I : Subgroup G) := by
    have he := congrArg (Subgroup.map eMI.toMonoidHom)
      (earlier.intersection_characteristic_two I hI)
    simpa only [map_generalizedFitting_equiv, pCore_map_iso] using he
  have hY : IsPGroup 3 (d.Y ⧸ pCore 2 d.Y) := by
    rcases h7 with ⟨_, ⟨e⟩, _⟩ | ⟨⟨e⟩, _⟩
    · apply IsPGroup.of_card (n := 2)
      rw [Nat.card_congr e.toEquiv]
      simp [ThreeAlternatives.ElementaryNine, Nat.card_eq_fintype_card]
    · exact IsPGroup.of_card ((Nat.card_congr e.toEquiv).trans (HeisenbergPrime.card (p := 3)))
  have hYplus : IsPGroup 3 (d.Yplus ⧸ pCore 2 d.Yplus) :=
    IsPGroup.of_exponent_dvd_pow (n := 1) (by simpa only [pow_one] using earlier.quotient_exponent)
  have hsetup : LinearCore.MatrixImage.SourceSetup d I L :=
    { outside := hI
      sylow := ⟨P, hP⟩
      component_le := hLI
      component := hL
      odd_core := earlier.odd I hI
      component_outside := hLM
      orbit_eq := hsigned.1
      rank_component := hLrank
      rank_yplus := hYrank
      rank_overgroup := earlier.rank I hI
      theta_eq := hθ
      normalizer_eq := earlier.normalizer_eq I hI
      quotient_three := hY
      yplus_quotient_three := hYplus
      intersection_characteristic_two := hMI
      residual_ne := hne
      core_normalizes := (pCoreIn_le 2 _).trans (hI.1.2.trans hn)
      component_cores_le := ComponentIntersection.cores_le_localCore hLI hL.isCComponent
        P hP hYI hSY (hYI.trans hn)
      shadow := earlier.shadow
      characteristic_two_containment := by
        let := earlier.solvable
        intro D hD hDN hDF
        exact lemma_15_3_33_1 hI earlier.sylow earlier.exclusion earlier.odd
          (hD.trans hLI) hDN hDF }
  apply rankTwoDiagonal_of_signed_of_core_cover (Y := d.Y) hI hθ hLI hindex
    hYrank hLrank (earlier.rank I hI) hsigned
  · exact UnitaryLocal.unitary_exclusion hI hSM hθ hYplus hLI hL.1 hLM P hP
      hindex hYrank hLrank (earlier.rank I hI)
  · intro y hy hy3 hlinear
    exact LinearCore.cover_of_linear_source hsetup earlier hy hy3 hlinear
      hchoice h7 himage7 hΩ hVY

end CFSG.Quasithin.Chapter15.Section03.Candidates
