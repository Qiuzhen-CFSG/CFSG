module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.CoreGrowth
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual
public import BenderSuzuki.SE.Section9Focal
public import BenderSuzuki.ZD.Recognition
public import Mathlib.GroupTheory.Nilpotent

/-!
# Applying core growth to the splitting and residual endpoints

The numerical theorem now discharges both core-order premises of the
existing Proposition 17.6 complement theorem. Section 16's local hypothesis
supplies the normal two-complement in the literal two-point stabilizer, and
its marked involution supplies even order. The quotient argument then makes
the two-residual of `M` proper.

The final theorem combines the focal-transfer endpoint of residual embedding
with the existing full finite-group ZD induction. It retains the source producers
for simple reduction, action, generation, local cyclic Sylows and counting;
it introduces no global involution-class or torus-freeness assumption.
Those earlier producers remain the responsibility of the source assembly.

Source: GLS, Volume 4, Chapter 2, Proposition 17.6 and the final paragraph
of Section 17, followed by the finite-group reduction of Sections 3–4.
-/

noncomputable section
namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
universe u
variable {G : Type u} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- The two-core growth conclusions discharge the actual complement's
numerical premises, retaining the original two-point stabilizer. -/
public theorem TwoCoreCountingData.isComplement_of_local_cyclicSylow
    (d : TwoCoreCountingData Z M) (h : MinimalCounterexample Z M)
    (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    (residualPairIn M d.t).IsComplement' (pCore 2 M) := by
  obtain ⟨hlarge, hpower⟩ := d.core_growth_of_local_cyclicSylow h r ha hn hg hlocal
  exact d.isComplement_of_core_growth h.disconnected hlocal hlarge hpower

/-- The splitting supplies the source quotient `D/O_{2'}(D)`, and hence a
proper two-residual. Even order comes from the original marked `d.u`. -/
public theorem TwoCoreCountingData.twoResidual_ne_top_of_local_cyclicSylow
    (d : TwoCoreCountingData Z M) (h : MinimalCounterexample Z M)
    (r : SimpleReduction Z M) (ha : ResidualAction Z M)
    (hn : ¬ IsStronglyEmbedded M) (hg : ResidualGeneration Z M)
    (hlocal : ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
      HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) :
    External.hallPResidual 2 M ≠ ⊤ := by
  have hcomp : HasNormalPComplement 2 (residualPairIn M d.t) := by
    apply hasNormalPComplement_of_equiv 2 (residualPairInEquiv M d.t).symm
    exact (hlocal _ (residualPairStabilizer_localClosure_eq_bot
      h.disconnected d.t_not_mem)).1
  have heven : 2 ∣ Nat.card (residualPairIn M d.t) :=
    d.u_order ▸ orderOf_dvd_natCard d.u
  exact twoResidual_ne_top_of_split_pair
    (d.isComplement_of_local_cyclicSylow h r ha hn hg hlocal) hcomp heven

-- Use the narrow focal-transfer interface here: the legacy residual-action
-- import also brings a second declaration of `residualPairStabilizer_even`,
-- with a different signature from the local-selection branch.
private theorem false_of_proper_twoResidual
    (h : IsProductDisconnected Z M) (r : SimpleReduction Z M)
    (hres : External.hallPResidual 2 M ≠ ⊤) : False := by
  let R := External.hallPResidual 2 M
  let : R.Normal := External.hallPResidual_normal 2 M
  let Q := M ⧸ R
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hres
  have hQ : IsPGroup 2 Q := External.hallPResidual_quotient_isPGroup 2
  let : Group.IsNilpotent Q := hQ.isNilpotent
  let : Nontrivial (Abelianization Q) := QuotientGroup.nontrivial_iff.mpr
    (Group.IsSolvable.commutator_lt_top_of_nontrivial Q).ne
  have hAQ : IsPGroup 2 (Abelianization Q) := hQ.to_quotient (commutator Q)
  obtain ⟨n, hn, hcard⟩ := hAQ.nontrivial_iff_card.mp inferInstance
  have htwo : 2 ∣ Nat.card (Abelianization Q) :=
    hcard ▸ dvd_pow_self 2 (by omega)
  let f : M →* Q := QuotientGroup.mk' R
  have hf : Function.Surjective (Abelianization.map f) := by
    intro x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (commutator Q) x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective R q
    exact ⟨Abelianization.of y, rfl⟩
  have hdiv : 2 ∣ Nat.card (M ⧸ derivedSubgroup M) := by
    simpa only [Abelianization, derivedSubgroup, derivedSeries_one] using
      htwo.trans (Subgroup.card_dvd_of_surjective (Abelianization.map f) hf)
  obtain ⟨S, hSM, hfusion⟩ := r.fusion
  obtain ⟨hlt, hsup⟩ :=
    hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
      M S hSM hfusion hdiv
  rcases r.simple.eq_bot_or_eq_top_of_normal (External.hallPResidual 2 G)
      (External.hallPResidual_normal 2 G) with hbot | htop
  · exact h.proper (by simpa [hbot] using hsup)
  · exact hlt.ne htop

/-- Full finite-group ZD assembly with the numerical and splitting steps
proved. Only the existing earlier-source producers remain explicit; in
particular this is not an assertion that counting or Section 16 is proved. -/
public theorem conclusion_of_local_cyclicSylow_and_counting
    (reduce : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M)
    (action : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M)
    (generation : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M →
      ¬ IsStronglyEmbedded M → ResidualGeneration Z M)
    (local_steps : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M →
      ¬ IsStronglyEmbedded M → ResidualGeneration Z M →
      ∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
        HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S)
    (counting : ∀ {G : Type u} [Group G] [Finite G]
      (Z : Set G) (M : Subgroup G),
      MinimalCounterexample Z M → SimpleReduction Z M → ResidualAction Z M →
      ¬ IsStronglyEmbedded M → ResidualGeneration Z M →
      (∀ Y : Subgroup G, Subgroup.closure (Y.subtype ⁻¹' Z) = ⊥ →
        HasNormalPComplement 2 Y ∧ ∀ S : Sylow 2 Y, IsCyclic S) →
      Nonempty (TwoCoreCountingData Z M))
    (Z : Set G) (M : Subgroup G) (h : IsProductDisconnected Z M) :
    Conclusion Z M := by
  apply conclusion_of_simple_and_embedding_reductions reduce ?_ Z M h
  intro H _ _ W N hmin r
  by_contra hn
  have ha := action W N hmin r
  have hg := generation W N hmin r ha hn
  have hlocal := local_steps W N hmin r ha hn hg
  obtain ⟨d⟩ := counting W N hmin r ha hn hg hlocal
  exact false_of_proper_twoResidual hmin.disconnected r
    (d.twoResidual_ne_top_of_local_cyclicSylow hmin r ha hn hg hlocal)

end BenderSuzuki.ZD
