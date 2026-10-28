module
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.EvenRankTwo
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicRemaining.Covers
public import Theory.SpecificGroups.PSL3.BinaryOddCenterCover
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.Even
public import Theory.SpecificGroups.G2.MultiplierTwoGroup
public import Theory.Representation.Triality.InnerDisplacement.PrimeToTwoCovers

/-!
# Original characteristic-two rank-two intrinsic embedding alternatives

The proved central-cover calculations discharge the G₂, triality and
symplectic cover inputs in the existing Sylow-pair sieve. The binary linear
case needs only an SL₃ scalar lift: trivial two-core gives odd center, so
the exceptional field-four odd-center lift suffices without an exact
universal multiplier decomposition. Existing placement and pair-action
calculations then cover all eight RankTwoTheoremC constructors. The actual
intrinsic consumer transports the plane and cyclic automizer back through
the literal quotient L/O₂(L).

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.511, and I.1.3,
printed p.407. The original genuine Sylow hypothesis is retained.
-/

public section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
universe u

/-- Every perfect cover of the actual binary symplectic model is injective. -/
theorem source_symplecticKernel : SymplecticCentralKernelTheorem.{u} := by
  intro F _ _ n hn hF E _ _ _ π hπ hk
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let e := Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)
  let c : Cover E (Theory.SpecificGroups.SymplecticFour.Sp F) :=
    ⟨e.symm.toMonoidHom.comp π, e.symm.surjective.comp hπ, inferInstance, by
      intro x hx
      apply hk
      apply e.symm.injective
      change e.symm (π x) = 1 at hx
      simpa only [map_one] using hx⟩
  have hl : 3 < Nat.card F := by
    have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hn
    omega
  have hi := Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.cover_injective hl c
  exact π.ker_eq_bot_iff.mpr (fun _ _ he => hi (congrArg e.symm he))

/-- The actual odd-primary calculation gives two-group center for binary G₂ covers. -/
theorem source_g2TwoCenter : ExceptionalActions.G2TwoCenter.{u} := by
  intro K _ _ hK f hf hm
  let : IsQuasisimple K := hK
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  have hlarge : 2 < Nat.card F := by
    have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) hf
    omega
  let : Fact (2 < Nat.card F) := ⟨hlarge⟩
  have hh := Atlas.G2.FiniteCover.universalKernel_isPGroup_of_card_pow hF (by omega)
  have hz := (centralQuotientCover e).ker_isPGroup_of_universal
    (universalCover (Atlas.G2.Model F)) (universalCover_isUniversal (G := Atlas.G2.Model F)) hh
  change IsPGroup 2 (centralQuotientCover e).toMonoidHom.ker at hz
  rwa [centralQuotientCover_ker] at hz

/-- The triality cover calculation includes the smallest binary parameter. -/
theorem source_trialityTwoCenter : ExceptionalActions.TrialityTwoCenter.{u} := by
  intro K _ _ hK f hf hm
  let : IsQuasisimple K := hK
  exact Triality.InnerDisplacement.PrimeToTwoCovers.center_isTwoGroup f (by omega) hm

/-- The binary linear pair exclusion needs no universal multiplier premise. -/
theorem linear_reducible_of_source
    {Q : Type u} [Group Q] [Finite Q] {S : Sylow 2 Q} {R : Subgroup Q}
    (h : PairInput S R) {f : ℕ} (hf : 1 ≤ f)
    (hm : ClassicalGroup.IsPSL (Q ⧸ center Q) 3 (2 ^ f)) :
    PairReducible (S : Subgroup Q) R := by
  by_cases hf1 : f = 1
  · exact Linear.pairReducible_binary h (by simpa only [hf1, pow_one] using hm)
  have hf2 : 2 ≤ f := by omega
  let : IsQuasisimple Q := h.quasisimple
  have hodd : Odd (Nat.card (center Q)) := Nat.not_even_iff_odd.mp (by
    simpa only [even_iff_two_dvd] using SporadicRemaining.two_not_dvd_center_card h.twoCore)
  have hc : R ≤ normalizer (S : Set Q) ∧ IsMulCommutative R := by
    apply Linear.Placement.placement_of_model_inputs h hf2 hm
    · intro F _ _ hF B hB
      exact Linear.Placement.projective_le_borel hf2 hF hB
    · intro F _ _ hF e
      have hlarge : 4 ≤ Nat.card F := by
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hf2
        omega
      by_cases h4 : Nat.card F = 4
      · simpa only [Linear.Placement.modelProjection, centralQuotientCover] using
          Matrix.PSL3.BinaryOddCenterCover.exists_scalar_lift_four h4 e hodd
      · simpa only [Linear.Placement.modelProjection, centralQuotientCover] using
          Matrix.PSL3.OrdinaryCenterRecognition.exists_scalar_lift (by omega) h4 e
  apply Linear.pairReducible_of_commutative_and_disjoint_action h hc.2
  intro hd D hD htwo
  exact Linear.Actions.pair_power_involution h hf2 hm hc.1 hc.2 hd D hD htwo

/-- All eight original rank-two model branches, with every cover premise discharged. -/
theorem rankTwo_of_source {Q : Type u} [Group Q] [Finite Q]
    {S : Sylow 2 Q} {R : Subgroup Q} (h : PairInput S R)
    (hm : Section02.LocalModels.RankTwoTheoremC (Q ⧸ center Q)) :
    PairReducible (S : Subgroup Q) R ∨
      (Nonempty (R ≃* Plane 3) ∧ SymplecticModel 3 Q ∧
        IsCyclic (pairAutomizer (S : Subgroup Q) R)) := by
  cases hm with
  | linear f hf hm => exact Or.inl (linear_reducible_of_source h hf hm)
  | symplectic f hf hm => exact symplectic_case source_symplecticKernel h hf hm
  | g2 f hf hm => exact Or.inl (ExceptionalActions.g2_pairReducible source_g2TwoCenter h hf hm)
  | triality f hf hm =>
      exact Or.inl (ExceptionalActions.triality_pairReducible source_trialityTwoCenter h hf hm)
  | ree m hm he => exact Or.inl (Ree.pairReducible_of_equiv hm h he)
  | symplectic_derived he =>
      obtain ⟨e⟩ := symplectic_derived_is_alternating_six he
      exact Or.inl (AlternatingBinary.alternating_six h e)
  | g2_derived he => exact Or.inl (SmallDerived.g2_pairReducible_of_equiv h he.some)
  | tits he => exact Or.inl (SmallDerived.tits_pairReducible_of_equiv h he.some)

/-- The original intrinsic input gives the literal plane and symplectic alternative. -/
theorem alternatives_of_local_input {G : Type u} [Group G] [Finite G]
    {κ : GroupClass.{u}} {T X P H L : Subgroup G}
    (h : LocalInput 3 T X P H) (hH : IsSQTK κ H)
    (hT : IsSylowIn 2 T H) (hLH : L ≤ H) (hLn : (L.subgroupOf H).Normal)
    (hq : IsQuasisimple (XiQuotient L)) (hPL : P ≤ L) (hcomm : ⁅L, P⁆ = L)
    (hm : Section02.LocalModels.RankTwoTheoremC
      (XiQuotient L ⧸ center (XiQuotient L))) : Alternatives 3 T P L := by
  have hTL : T ≤ normalizer L := (le_sup_right.trans h.overgroup).trans
    ((normal_subgroupOf_iff_le_normalizer hLH).mp hLn)
  obtain ⟨S, hS, hi⟩ := pairInput_of_sylow h hH hT hLH hLn hq hPL hcomm
  rcases rankTwo_of_source hi hm with hr | ⟨he, hm, hc⟩
  · exact (not_pairReducible h hPL hTL (by simpa only [hS] using hr)).elim
  · rw [hS] at hc
    have hcy := automizer_cyclic_of_pairAutomizer h hPL hTL hc
    exact ⟨plane_of_quotient_plane h hPL he, Or.inr ⟨hTL, Or.inr (Or.inl ⟨hm, hcy⟩)⟩⟩
end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.EvenRankTwo
