module

public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Contracts
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Geometry
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.Rank
public import CFSG.Quasithin.Chapter16.Section03.EnlargementSieve.IntrinsicRanks.Bounds
public import CFSG.Quasithin.Chapter16.Section01To02.ComponentTransfer.Swapped
public import CFSG.Quasithin.Chapter16.Section01To02.CounterexampleGeometry.OrbitPersistence.FamilySieve.CoveredModels
public import Theory.GroupTheory.PrimeRankCentralProduct
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.SpecificGroups.SL2.DefiningRank
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.FieldAction
public import Theory.SpecificGroups.SL2.SmallOddComparisons
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models


/-!
# The swapped-factor rank argument

Work with the actual enlargement K = ⟨L^{E(C_G(t))}⟩. Its swapped witness
is a component J of C_G(t), with K = J Jᶻ and J/O₂(J) ≃ L/O₂(L).
The full nonsimple-cover list of 16.1.2 intersects the source rank-one list
only in Sz(8). Involutory lifts and the elementary center then give
m₂(K) ≥ 2m₂(L/O₂(L)), including the nonsimple central products.

If Z(K) is nontrivial, centerlessness of the factor would make its commuting
conjugate product centerless. Thus the factor covers Sz(8), and the actual
quotient equivalence gives m₂(L/O₂(L)) = 3. No identification of K/Z(K)
with one Suzuki group is made.

The prime-field PSL₂ and Suzuki automorphism ranks are proved in the imported
model extensions. Final elimination is conditional on the independently owned
binary SL₂ automorphism bound, stated explicitly as BinaryAutomorphismRankBound.
The source-theorem assembly remains unfinished until that premise is proved.
The other inputs are the consumed clauses of earlier 16.1.2, 16.1.7(2), and
I.2.2(4), attached to the actual components and quotient equivalences.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.409, 1170, 1172–1173, and the swapped paragraph of 16.3.9 on p.1180.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
open ComponentTransfer CounterexampleGeometry.FamilySieve BenderSuzuki.MatrixGroups

private theorem prime_parameter_gt_three {Q : Type*} [Group Q] [Group.IsPerfect Q]
    [Nontrivial Q] {p : ℕ} (hp : p.Prime) (model : ClassicalGroup.IsPSL Q 2 p) :
    3 < p := by
  by_contra hn
  rcases model with ⟨F, hF, hfinite, hcard, ⟨e⟩⟩
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    e.injective.nontrivial
  have hsmall : p = 2 ∨ p = 3 := by have := hp.two_le; omega
  rcases hsmall with rfl | rfl
  · exact Group.IsPerfect.not_isSolvable _
      (Theory.PSL2.OuterSolvable.isSolvable_of_card_two hcard)
  · exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three hcard inferInstance

private theorem sourceOrbit_of_swapped {Q : Type*} [Group Q] [Group.IsPerfect Q]
    [Nontrivial Q] (h : SwappedQuotientModel Q) : SourceOrbitModel Q := by
  cases h with
  | linearEven n hn model => exact .linear_even n hn model
  | suzuki m hm model => exact .suzuki m hm model
  | linearPrime p hp model =>
      exact .linear_odd p hp (prime_parameter_gt_three hp model) model

private theorem aut_rank_le_central_quotient {X : Type*} [Group X] [Finite X]
    [Group.IsPerfect X] : primeRank 2 (MulAut X) ≤ primeRank 2 (MulAut (X ⧸ center X)) := by
  let f : PerfectCentralCovering.Cover X (X ⧸ center X) := {
    toMonoidHom := QuotientGroup.mk' (center X)
    surjective := QuotientGroup.mk'_surjective _
    isPerfect := inferInstance
    ker_le_center := (QuotientGroup.ker_mk' _).le }
  have hk : f.toMonoidHom.ker = center X := QuotientGroup.ker_mk' _
  exact primeRank_le_of_injective 2 (f.autMap hk) (f.autMap_injective hk)

/-- The remaining independent binary PSL₂ automorphism calculation. The G.9
owner proves this on SL₂; the actual characteristic-two quotient equivalence
transports it below. This predicate is not a source theorem or a proved fact. -/
def BinaryAutomorphismRankBound : Prop :=
  ∀ (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ), 2 ≤ n → Nat.card F = 2 ^ n →
    primeRank 2 (MulAut (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ n

/-- The center-size clause of 16.1.2(2) specialized to a Suzuki quotient,
and the involution-lifting clause of I.2.2(4). No rank is prescribed. -/
def SuzukiCoverClauses (X : Type*) [Group X] : Prop :=
  (Nat.card (center X) ≤ 2 ∨
    Nonempty (center X ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)))) ∧
  ∀ x : X ⧸ center X, x ^ 2 = 1 →
    ∃ y : X, QuotientGroup.mk' (center X) y = x ∧ y ^ 2 = 1

private theorem elementary_center_of_cover {X : Type*} [Group X] [Finite X]
    (hc : SuzukiCoverClauses X) : IsElementaryAbelian 2 (center X) := by
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  rcases hc.1 with hcard | he
  · have hp : 0 < Nat.card (center X) := Nat.card_pos
    have hdiv : Nat.card (center X) ∣ 2 := by
      have he : Nat.card (center X) = 1 ∨ Nat.card (center X) = 2 := by omega
      rcases he with he | he <;> simp [he]
    exact orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard x).trans hdiv)
  · obtain ⟨e⟩ := he
    apply e.injective
    rw [map_pow, map_one]
    apply Prod.ext
    · change (e x).1 ^ 2 = 1
      rw [pow_two]
      change Multiplicative.ofAdd ((e x).1.toAdd + (e x).1.toAdd) = Multiplicative.ofAdd 0
      rw [CharTwo.add_self_eq_zero]
    · change (e x).2 ^ 2 = 1
      rw [pow_two]
      change Multiplicative.ofAdd ((e x).2.toAdd + (e x).2.toAdd) = Multiplicative.ofAdd 0
      rw [CharTwo.add_self_eq_zero]

private theorem cover_clauses_of_center_bot {X : Type*} [Group X]
    (hc : center X = ⊥) : SuzukiCoverClauses X := by
  refine ⟨Or.inl (by rw [hc]; simp), ?_⟩
  intro x hx
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center X) x
  refine ⟨y, rfl, ?_⟩
  have hi : Function.Injective (QuotientGroup.mk' (center X)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (by rw [QuotientGroup.ker_mk', hc])
  apply hi
  simpa only [map_pow, map_one] using hx

universe u
variable {G : Type u} [Group G] [Finite G] {𝒦 : GroupClass.{u}}
  {T : Sylow 2 G} {z t : G} {L J : Subgroup G}

/-- The source cover list forces a noncenterless rank-one factor to cover Sz(8). -/
theorem swapped_factor_suzuki_of_center_ne (hg : Hypothesis1611 𝒦 G)
    (s1612 : Source1612One 𝒦 G) (ht : orderOf t = 2)
    (hJ : IsCentralizerComponent t J)
    (hmodel : SwappedQuotientModel (J ⧸ pCore 2 J)) (hZ : center J ≠ ⊥) :
    Nonempty ((J ⧸ center J) ≃* SuzukiMatrixGroup 1) := by
  let := hJ.quasisimple
  have hcenter := hg.evenType.component_center_eq_twoCore ht hJ
  let e := QuotientGroup.quotientMulEquivOfEq hcenter
  let : IsSimpleGroup (J ⧸ center J) := IsQuasisimple.simple
  let : Group.IsPerfect (J ⧸ center J) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hn : ¬ IsSimpleGroup J := by
    intro hs
    let := hs
    rcases (inferInstance : (center J).Normal).eq_bot_or_eq_top with hb | ht
    · exact hZ hb
    · exact Group.IsPerfect.not_isMulCommutative J (center_eq_top_iff.mp ht)
  exact covered_model_intersection (sourceOrbit_of_swapped (hmodel.of_mulEquiv e))
    (s1612 hg t J ht hJ hn).2

/-- Nontrivial center of the actual swapped enlargement is detected in a factor,
whose quotient is Sz(8); its equivalence with L/O₂(L) gives m=3. -/
theorem swapped_rank_three_of_center_ne (hg : Hypothesis1611 𝒦 G)
    (s1612 : Source1612One 𝒦 G) (h : TerminalCounterexample T z L t)
    (hswap : SwappedComponents (involutionCentralizer t) z L (enlargement t L))
    (hmodel : SwappedQuotientModel (L ⧸ pCore 2 L))
    (hZ : center (enlargement t L) ≠ ⊥) :
    Nonempty ((L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1) ∧
      primeRank 2 (L ⧸ pCore 2 L) = 3 := by
  obtain ⟨J, hJ, hne, hK, hc, ⟨eJ⟩⟩ := hswap.commute (setup h).t_mem
  have hJZ : center J ≠ ⊥ := by
    intro hJZ
    apply hZ
    rw [hK]
    exact J.center_conjugate_join_eq_bot z (commutator_eq_bot_iff_le_centralizer.mp hc) hJZ
  obtain ⟨e⟩ := swapped_factor_suzuki_of_center_ne hg s1612 h.involution hJ
    (hmodel.of_mulEquiv eJ) hJZ
  have hcenter := hg.evenType.component_center_eq_twoCore h.involution hJ
  let eL : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup 1 :=
    eJ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hcenter.symm).trans e)
  exact ⟨⟨eL⟩, (primeRank_equiv 2 eL).trans (suzuki_two_rank 1 (by decide))⟩


/-- Doubling for the actual enlargement, including the allowed nonsimple factors.
Only the genuine earlier cover and source-model statements are inputs. -/
theorem swapped_doubled_rank (hg : Hypothesis1611 𝒦 G)
    (s1612 : Source1612One 𝒦 G) (h : TerminalCounterexample T z L t)
    (hswap : SwappedComponents (involutionCentralizer t) z L (enlargement t L))
    (hmodel : SwappedQuotientModel (L ⧸ pCore 2 L))
    (hcover : ∀ M : Subgroup G, IsCentralizerComponent t M → center M ≠ ⊥ →
      Nonempty ((M ⧸ center M) ≃* SuzukiMatrixGroup 1) → SuzukiCoverClauses M) :
    2 * primeRank 2 (L ⧸ pCore 2 L) ≤ primeRank 2 (enlargement t L) := by
  obtain ⟨J, hJ, hne, hK, hcomm, ⟨eJ⟩⟩ := hswap.commute (setup h).t_mem
  have hcenter := hg.evenType.component_center_eq_twoCore h.involution hJ
  have hc : SuzukiCoverClauses J := by
    by_cases hZ : center J = ⊥
    · exact cover_clauses_of_center_bot hZ
    · exact hcover J hJ hZ (swapped_factor_suzuki_of_center_ne hg s1612 h.involution hJ
        (hmodel.of_mulEquiv eJ) hZ)
  let := elementary_center_of_cover hc
  have hr := J.two_rank_conjugate_join_ge z
    (commutator_eq_bot_iff_le_centralizer.mp hcomm) hc.2
  rw [← hK] at hr
  have he := primeRank_equiv 2 ((QuotientGroup.quotientMulEquivOfEq hcenter).trans eJ)
  rwa [he] at hr

/-- All three factor families satisfy the numerical inequalities, conditional
only on the independent binary automorphism theorem. The odd prime-field and
Suzuki estimates are proved on their actual carriers. -/
theorem swapped_factor_ranks_of_binary_bound (hbinary : BinaryAutomorphismRankBound)
    (hg : Hypothesis1611 𝒦 G) (h : TerminalCounterexample T z L t)
    (hmodel : SwappedQuotientModel (L ⧸ pCore 2 L)) :
    2 ≤ primeRank 2 (L ⧸ pCore 2 L) ∧
      primeRank 2 (MulAut L) ≤ primeRank 2 (L ⧸ pCore 2 L) := by
  let := h.localSetup.component.quasisimple
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  have hc := hg.evenType.component_center_eq_twoCore h.localSetup.involution h.localSetup.component
  let ec := QuotientGroup.quotientMulEquivOfEq hc
  have hec := primeRank_equiv 2 ec
  rw [← hec]
  have ha := aut_rank_le_central_quotient (X := L)
  cases hmodel.of_mulEquiv ec with
  | linearEven n hn model =>
      obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := model
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hcard)
      have hl : n ≤ primeRank 2 (L ⧸ center L) :=
        Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective
          hcard e.symm.toMonoidHom e.symm.injective
      have hau : primeRank 2 (MulAut (L ⧸ center L)) ≤ n := by
        rw [primeRank_equiv 2 (MulAut.congr (e.trans (BenderSuzuki.ZD.Linear.sl2QuotientEquiv F).symm))]
        exact hbinary F n hn hcard
      exact ⟨hn.trans hl, ha.trans (hau.trans hl)⟩
  | suzuki m hm model =>
      obtain ⟨e⟩ := model
      have hr : primeRank 2 (L ⧸ center L) = 2*m+1 :=
        (primeRank_equiv 2 e).trans (suzuki_two_rank m hm)
      rw [hr]
      exact ⟨by omega, suzuki_cover_automorphism_two_rank hm e⟩
  | linearPrime p hp model =>
      have hlarge := prime_parameter_gt_three hp model
      let : Fact p.Prime := ⟨hp⟩
      obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := model
      let : Fintype F := Fintype.ofFinite F
      let ef : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp
        (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
      let eQ := e.trans (Atlas.fieldEquivPSL 2 ef)
      have hr : primeRank 2 (L ⧸ center L) = 2 :=
        (primeRank_equiv 2 eQ).trans (Theory.PSL2.primeField_two_rank hlarge)
      rw [hr]
      refine ⟨le_rfl, ha.trans ?_⟩
      rw [primeRank_equiv 2 (MulAut.congr eQ)]
      exact Theory.PSL2.primeField_automorphism_two_rank hlarge

/-- Exclude the actual swapped enlargement. The binary automorphism premise
is the sole remaining intrinsic numerical obligation; this conditional
assembly is not the completed swapped branch until that premise is supplied. -/
theorem exclude_swapped_of_binary_bound (hbinary : BinaryAutomorphismRankBound)
    (hg : Hypothesis1611 𝒦 G) (s1612 : Source1612One 𝒦 G)
    (h : TerminalCounterexample T z L t) (hs : NonterminalCentralizerShape T z L t)
    (hswap : SwappedComponents (involutionCentralizer t) z L (enlargement t L))
    (hmodel : SwappedQuotientModel (L ⧸ pCore 2 L))
    (hcover : ∀ M : Subgroup G, IsCentralizerComponent t M → center M ≠ ⊥ →
      Nonempty ((M ⧸ center M) ≃* SuzukiMatrixGroup 1) → SuzukiCoverClauses M) : False := by
  obtain ⟨hm, hAut⟩ := swapped_factor_ranks_of_binary_bound hbinary hg h hmodel
  have hK := swapped_doubled_rank hg s1612 h hswap hmodel hcover
  have ht := not_outside_of_doubled_rank h hs hm hK hAut
  have hthree := (swapped_rank_three_of_center_ne hg s1612 h hswap hmodel (center_ne_bot h ht)).2
  rw [hthree] at hK hAut
  exact exclude_rank_six h hs hK hAut

/-- The Suzuki family is excluded without the outstanding binary rank premise. -/
theorem exclude_swapped_suzuki (hg : Hypothesis1611 𝒦 G)
    (s1612 : Source1612One 𝒦 G) (h : TerminalCounterexample T z L t)
    (hs : NonterminalCentralizerShape T z L t)
    (hswap : SwappedComponents (involutionCentralizer t) z L (enlargement t L))
    {m : ℕ} (hm : 1 ≤ m) (e : (L ⧸ pCore 2 L) ≃* SuzukiMatrixGroup m)
    (hcover : ∀ M : Subgroup G, IsCentralizerComponent t M → center M ≠ ⊥ →
      Nonempty ((M ⧸ center M) ≃* SuzukiMatrixGroup 1) → SuzukiCoverClauses M) : False := by
  let := h.localSetup.component.quasisimple
  have hc := hg.evenType.component_center_eq_twoCore h.localSetup.involution h.localSetup.component
  have hmodel : SwappedQuotientModel (L ⧸ pCore 2 L) := .suzuki m hm ⟨e⟩
  have hr : primeRank 2 (L ⧸ pCore 2 L) = 2*m+1 :=
    (primeRank_equiv 2 e).trans (suzuki_two_rank m hm)
  have hAut : primeRank 2 (MulAut L) ≤ primeRank 2 (L ⧸ pCore 2 L) := by
    rw [hr]
    exact suzuki_cover_automorphism_two_rank hm
      ((QuotientGroup.quotientMulEquivOfEq hc).trans e)
  have hK := swapped_doubled_rank hg s1612 h hswap hmodel hcover
  have hlower : 2 ≤ primeRank 2 (L ⧸ pCore 2 L) := by omega
  have ht := not_outside_of_doubled_rank h hs hlower hK hAut
  have hthree := (swapped_rank_three_of_center_ne hg s1612 h hswap hmodel (center_ne_bot h ht)).2
  rw [hthree] at hK hAut
  exact exclude_rank_six h hs hK hAut

end CFSG.Quasithin.Chapter16.EnlargementSieve.IntrinsicRanks
