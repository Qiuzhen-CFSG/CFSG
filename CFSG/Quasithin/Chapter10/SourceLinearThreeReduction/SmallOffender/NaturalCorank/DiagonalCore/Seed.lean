module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.DiagonalCore.Setup
public import Theory.GroupTheory.PResidual.ThreeFree
public import CFSG.Quasithin.Chapter10.SourceA5NormalizerControl
public import CFSG.Quasithin.Chapter10.SourceA5MovedNormalizer.OppositeComponent
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.GroupTheory.PResidual.TwoThreeComparison
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.LinearThree.Overgroups
public import Theory.GroupTheory.WreathTwoCoreQuotient
public import Theory.SpecificGroups.PSL3Two.Parabolics.NaturalPoint
public import Theory.GroupTheory.MinimalParabolicResidual
public import Theory.Representation.BinaryNaturalResidual

/-!
# The original diagonal seed before weak closure

The actual natural action identifies the diagonal parabolic quotient with
S3 wr C2. Its two-core preserves each factor, and a T-normal subgroup outside
the factor stabilizer generates the seed by commutators. Prime support gives
the required cubic-residual identity. The two point-centralizer residuals
then generate the original full module under the literal seed action.

Together these prove every seed-analysis field used by the core argument.
The proofs adapt the indicated modules under
`SourceLinearThreeReplacement/Geometry/CoreReduced/Seed`, removing the unused
later numerical premises while retaining the same residuals and inclusions.
Source: Aschbacher--Smith 10.1.3 and 10.2.11, printed pp.742,753--754.
-/

public noncomputable section
-- Adapted from Geometry/CoreReduced/Seed/Inputs.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- Calculations on the literal original local centralizer and its two-residual. -/
structure LocalCalculation (_c : Configuration s a b) : Prop where
  prime_spectrum : IsPiGroup twoThreePrimes
    (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G)
  not_two : ¬ IsPGroup 2 (centralizerSeed T L (a*b))
  commutator : ∀ R : Subgroup G, R ≤ (T : Subgroup G) →
    (T : Subgroup G) ≤ normalizer (R : Set G) →
    ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) →
      ⁅centralizerSeed T L (a*b), R⁆ = centralizerSeed T L (a*b)

/-- The local odd-residual computation, independent of the representation supplement. -/
@[expose] def LocalCalculationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D) (a b : G) (c : Configuration s a b),
      LocalCalculation c

/-- The natural-action supplement on the original full module and original seed. -/
@[expose] def ModuleGenerationAt (T : Sylow 2 G) : Prop :=
  ∀ (L : Subgroup G) (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (s : SourceLinearThreePair T D) (a b : G), Configuration s a b →
      D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔ (zpowers a ⊔ zpowers b)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Core.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G} {c : Configuration s a b}

/-- The first SeedAnalysis field follows from the local commutator calculation. -/
theorem core_bound (h : LocalCalculation c) :
    (centralizerSeed T L (a*b) ⊔ (T : Subgroup G)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let X := centralizerSeed T L (a*b)
  let J := X ⊔ (T : Subgroup G)
  let Q := J.pCoreIn 2
  have hQT : Q ≤ (T : Subgroup G) := by
    have he := pCoreIn_le_sylow J (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
    change Q ≤ ((T : Subgroup G).subgroupOf J).map J.subtype at he
    rwa [map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ J from le_sup_right)] at he
  have hJQ : J ≤ normalizer (Q : Set G) := by
    simpa only [Q, pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using (pCore 2 J).le_normalizer_map J.subtype
  by_contra hout
  have he : ⁅X,Q⁆ = X := h.commutator Q hQT (le_sup_right.trans hJQ) hout
  have hXQ : X ≤ Q := by
    rw [← he]
    exact le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hJQ)
  exact h.not_two ((isPGroup_pCoreIn 2 J).to_le hXQ)

/-- Actual application to the central-core conclusion of 10.2.11(1). -/
theorem span_central_core (h : LocalCalculation c) :
    centralizerModule a b ≤ centerIn ((centralizer ({a*b} : Set G)).pCoreIn 2) :=
  c.span_central_core_of_seedJoin_core (core_bound h)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Fixed.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The original orbit preserves the first moved factor. -/
theorem orbit_normalizes_moved (s : SourceLinearThreePair T D) :
    localOrbit T L ≤ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule ((localOrbit T L).le_normalizer hg)),
    mem_normalizer_iff_map_conj_eq.mp
      (source_nonnormal_orbit_le_normalizer D (pair_nonnormal s) hg)]

/-- Conjugating the orbit invariance gives invariance of the partner. -/
theorem orbit_normalizes_partner (s : SourceLinearThreePair T D) :
    localOrbit T L ≤ normalizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) : Set G) := by
  have he : (localOrbit T L).map (MulAut.conj s.exchange).toMonoidHom = localOrbit T L :=
    mem_normalizer_iff_map_conj_eq.mp (le_normalizer_componentOrbit L T s.exchange_mem)
  rw [← he]
  exact (map_mono (orbit_normalizes_moved s)).trans
    ((⁅D.fullModule,L⁆ : Subgroup G).le_normalizer_map (MulAut.conj s.exchange).toMonoidHom)

/-- Fixing the product in the two disjoint original factors fixes each coordinate. -/
theorem centralizer_fixes (c : Configuration s a b) :
    localOrbit T L ⊓ centralizer ({a*b} : Set G) ≤
      centralizer ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) := by
  let A := ⁅D.fullModule,L⁆
  let B := A.map (MulAut.conj s.exchange).toMonoidHom
  have hd : Disjoint A B := pair_pair_disjoint s c.fixed
  intro g hg
  have ha : (MulAut.conj g) a ∈ A :=
    (mem_normalizer_iff.mp (orbit_normalizes_moved s hg.1) a).mp c.first_mem
  have hb : (MulAut.conj g) b ∈ B :=
    (mem_normalizer_iff.mp (orbit_normalizes_partner s hg.1) b).mp c.second_mem
  have he : (MulAut.conj g) a * (MulAut.conj g) b = a*b := by
    rw [← map_mul]
    change g*(a*b)*g⁻¹ = a*b
    rw [mem_centralizer_singleton_iff.mp hg.2, mul_inv_cancel_right]
  have hp : ((⟨(MulAut.conj g) a,ha⟩ : A), (⟨(MulAut.conj g) b,hb⟩ : B)) =
      (⟨a,c.first_mem⟩,⟨b,c.second_mem⟩) := mul_injective_of_disjoint hd he
  have hga : g*a*g⁻¹ = a := congrArg (fun p : A × B => (p.1 : G)) hp
  have hgb : g*b*g⁻¹ = b := congrArg (fun p : A × B => (p.2 : G)) hp
  have hE : zpowers a ⊔ zpowers b ≤ centralizer ({g} : Set G) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hga).symm
    · exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hgb).symm
  intro x hx
  exact (mem_centralizer_singleton_iff.mp (hE hx))

/-- The fourth SeedAnalysis field, with no additional local-model premise. -/
theorem fixes (c : Configuration s a b) :
    centralizerSeed T L (a*b) ≤
      centralizer ((zpowers a ⊔ zpowers b : Subgroup G) : Set G) :=
  (map_subtype_le _).trans (centralizer_fixes c)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Natural.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The literal natural section has zero kernel in the diagonal configuration. -/
theorem natural_kernel_eq_bot (c : Configuration s a b) :
    ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) = ⊥ := by
  have hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map (MulAut.conj s.exchange).toMonoidHom : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D s.exchange_mem s.exchange_moves s.crossed)
  have hpair : localOrbit T L = L ⊔ L.map (MulAut.conj s.exchange).toMonoidHom :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
        (pair_nonnormal s)) inf_le_right s.exchange_mem s.exchange_moves
  have hC : ⁅D.fullModule,L⁆ ⊓ centralizer (L : Set G) ≤
      centralizer (localOrbit T L : Set G) := by
    apply le_centralizer_iff.mpr
    rw [hpair]
    exact sup_le (le_centralizer_iff.mp inf_le_right)
      (le_centralizer_iff.mp (inf_le_left.trans hcross))
  exact bot_unique ((le_inf (inf_le_left.trans (pair_moved_le s)) hC).trans_eq c.fixed)

/-- The supplied coordinates identify the entire original moved factor. -/
theorem natural_coordinates_bijective (c : Configuration s a b) :
    Function.Bijective s.natural.coordinates := by
  refine ⟨(MonoidHom.ker_eq_bot_iff _).mp ?_, s.natural.onto⟩
  rw [s.natural.kernel_eq, natural_kernel_eq_bot c, bot_subgroupOf]

/-- The given nonidentity first vector is nonzero in the literal natural action. -/
theorem first_coordinates_ne_one (c : Configuration s a b) :
    s.natural.coordinates ⟨a,c.first_mem⟩ ≠ 1 := by
  intro he
  have ha := (s.natural.coordinates_eq_one_iff ⟨a,c.first_mem⟩).mp he
  rw [natural_kernel_eq_bot c] at ha
  exact c.first_ne (mem_bot.mp ha)

/-- The original first moved factor has order eight, without a quotient-kernel premise. -/
theorem moved_card (c : Configuration s a b) : Nat.card (⁅D.fullModule,L⁆ : Subgroup G) = 8 := by
  have he := s.natural.card_section
  rw [natural_kernel_eq_bot c, card_bot] at he
  norm_num [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at he ⊢
  exact he

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Residual.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The actual linear-three quotient supplies the cubic divisibility in 10.1.3. -/
theorem orbit_eq_cubic_residual (s : SourceLinearThreePair T D) :
    (primeToResidual 3 D.maximalLocal).map D.maximalLocal.subtype = localOrbit T L := by
  apply source_nonnormal_cubic_residual D (pair_nonnormal s)
  rw [Nat.card_congr s.quotient.toEquiv, Matrix.PSL3Two.card_SL]
  decide

/-- Literal residual comparison; only the local prime-spectrum calculation remains. -/
theorem seed_eq_cubic_residual (s : SourceLinearThreePair T D)
    (h23 : IsPiGroup twoThreePrimes
      (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G)) :
    (primeToResidual 3 (centralizer ({a*b} : Set G) ⊓ D.maximalLocal : Subgroup G)).map
      (centralizer ({a*b} : Set G) ⊓ D.maximalLocal).subtype =
        centralizerSeed T L (a*b) := by
  have he := embedded_primeToResidual_intersection 3 D.maximalLocal
    (centralizer ({a*b} : Set G))
  rw [orbit_eq_cubic_residual s, inf_comm D.maximalLocal] at he
  rw [centralizerSeed, twoResidual_eq_primeToResidual_three h23]
  exact he.symm

/-- The third SeedAnalysis field follows from the actual prime-to-three calculation. -/
theorem normal_in_kernel_of_twoThree (s : SourceLinearThreePair T D)
    (h23 : IsPiGroup twoThreePrimes
      (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G))
    (C : Subgroup G)
    (hC : C ≤ centralizer ({a*b} : Set G) ⊓ D.maximalLocal)
    (hHC : centralizer ({a*b} : Set G) ≤ normalizer (C : Set G))
    (hXC : centralizerSeed T L (a*b) ≤ C) :
    centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G) := by
  let K := centralizer ({a*b} : Set G) ⊓ D.maximalLocal
  let X := centralizerSeed T L (a*b)
  have hK : (primeToResidual 3 K).map K.subtype = X := seed_eq_cubic_residual s h23
  have hX : (primeToResidual 3 X).map X.subtype = X := by
    have he := congrArg (fun A : Subgroup K => A.map K.subtype)
      (embedded_primeToResidual_eq_of_normal 3 (primeToResidual 3 K) le_rfl)
    rw [map_embedded_primeToResidual_of_hom, hK] at he
    exact he
  have he : (primeToResidual 3 C).map C.subtype = X := by
    apply le_antisymm ((embedded_primeToResidual_mono 3 hC).trans_eq hK)
    rw [← hX]
    exact embedded_primeToResidual_mono 3 hXC
  change centralizer ({a*b} : Set G) ≤ normalizer (X : Set G)
  rw [← he]
  exact hHC.trans (normalizer_le_normalizer_characteristic_image C (primeToResidual 3 C))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- All five fields on the same original configuration, from the two remaining calculations. -/
theorem analysis_of_calculations (c : Configuration s a b) (h : LocalCalculation c)
    (hgen : D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔
      (zpowers a ⊔ zpowers b)) : SeedAnalysis c where
  core_bound := core_bound h
  commutator := h.commutator
  normal_in_kernel := normal_in_kernel_of_twoThree s h.prime_spectrum
  fixes := fixes c
  generates := hgen

/-- Conditional assembly; the local and natural-action obligations are not discharged here. -/
theorem seedAnalysisAt_of_calculations
    (hlocal : LocalCalculationAt T) (hmodule : ModuleGenerationAt T) : SeedAnalysisAt T := by
  intro L D s a b c
  exact analysis_of_calculations c (hlocal L D s a b c) (hmodule L D s a b c)

/-- Application to the original centralizer two-core and full-action reducedness contract.
The independent full-action representation argument is retained with its assembly owner. -/
theorem coreReduced_of_calculations
    (hlocal : LocalCalculationAt T) (hmodule : ModuleGenerationAt T)
    (haction : FullActionCentralizationAt T) : CoreReducedAt T :=
  coreReduced_of_source_inputs (seedAnalysisAt_of_calculations hlocal hmodule) haction

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed

-- Adapted from Geometry/CoreReduced/Seed/Local/Primes.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The prime-spectrum field on the original centralizer. -/
theorem prime_spectrum (c : Configuration s a b) :
    IsPiGroup twoThreePrimes
    (localOrbit T L ⊓ centralizer ({a*b} : Set G) : Subgroup G) := by
  let K : Subgroup G := localOrbit T L ⊓ centralizer ({a*b} : Set G)
  let P : Subgroup G := localJoin T L ⊓ centralizer ({a*b} : Set G)
  have hKP : K ≤ P := inf_le_inf_right _ le_sup_left
  have hTP : (T : Subgroup G) ≤ P := le_inf le_sup_right c.sylow_le
  have hlt : P < localJoin T L := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hz : a*b ∈ D.fullModule := D.fullModule.mul_mem
      (pair_moved_le s c.first_mem) (pair_partner_le s c.second_mem)
    have hJC : localJoin T L ≤ centralizer ({a*b} : Set G) := he ▸ inf_le_right
    have hfixed : a*b ∈ centralizer (localOrbit T L : Set G) := by
      intro x hx
      exact mem_centralizer_singleton_iff.mp (hJC (mem_sup_left hx))
    have hzero : a*b = 1 := mem_bot.mp (c.fixed ▸ (show
      a*b ∈ D.fullModule ⊓ centralizer (localOrbit T L : Set G) from ⟨hz,hfixed⟩))
    have ho := c.order
    rw [hzero, orderOf_one] at ho
    omega
  have h6 : IsPGroup 6 K :=
    (CentralHall.LinearThree.source_proper_overgroup_six D s.quotient
      (pair_nonnormal s) P hTP hlt).to_le hKP
  rw [IsPiGroup_iff twoThreePrimes]
  intro p hp
  obtain ⟨n, hn⟩ := h6.exists_card_dvd_pow
  have hpd : p.val ∣ 6 := by
    apply p.property.dvd_of_dvd_pow
    exact hp.trans hn
  have hpd' : p.val = 2 ∨ p.val = 3 := by
    have := p.property.dvd_mul.mp (show p.val ∣ 2*3 from hpd)
    rcases this with h | h
    · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp h |>.resolve_left p.property.ne_one)
    · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp h |>.resolve_left p.property.ne_one)
  exact hpd'
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local

-- Adapted from Geometry/CoreReduced/Seed/Local/Action.lean.
open Subgroup Theory.GroupTheory
open scoped Matrix
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic.Natural.OriginalAction
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic.Natural
open Matrix.PSL3Two
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

private def originalAction (c : Configuration s a b) : Natural.ActionData s c.fixed where
  hom := (Natural.OriginalAction.originalLift s c.fixed).hom
  onto := (Natural.OriginalAction.originalLift s c.fixed).surjective
  kernel_two := (Natural.OriginalAction.originalLift s c.fixed).kernel_two
  equivariant := (Natural.OriginalAction.originalLift s c.fixed).equivariant

private def diagonalVector (c : Configuration s a b) : D.fullModule :=
  ⟨a*b,D.fullModule.mul_mem (pair_moved_le s c.first_mem)
    (pair_partner_le s c.second_mem)⟩

private def pointMap (c : Configuration s a b) :
    diagonalParabolic T L (a*b) →*
      Natural.pointStabilizer (Natural.fullCoordinates s c.fixed (diagonalVector c)) := by
  let f := originalAction c
  exact (f.hom.comp (inclusion (diagonalParabolic_le_join (a*b)))).codRestrict _ (by
    intro x
    have hh : (⟨x,diagonalParabolic_le_join (a*b) x.property⟩ : localJoin T L) ∈
        (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) := x.property
    have hp := f.stabilizer_preimage (diagonalVector c)
    change (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) = _ at hp
    rw [hp] at hh
    exact hh)

private theorem pointMap_surjective (c : Configuration s a b) : Function.Surjective (pointMap c) := by
  let f := originalAction c
  intro y
  obtain ⟨g,hg⟩ := f.onto y.val
  have hm : g ∈ (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) := by
    have hp := f.stabilizer_preimage (diagonalVector c)
    change (diagonalParabolic T L (a*b)).subgroupOf (localJoin T L) = _ at hp
    rw [hp]
    change f.hom g ∈ Natural.pointStabilizer
      (Natural.fullCoordinates s c.fixed (diagonalVector c))
    rw [hg]
    exact y.property
  exact ⟨⟨g.val,hm⟩,Subtype.ext hg⟩

/-- The original point-centralizer quotient, obtained from its natural action. -/
def parabolicQuotient (c : Configuration s a b) :
    (diagonalParabolic T L (a*b) ⧸ pCore 2 (diagonalParabolic T L (a*b))) ≃*
      WreathTwoResidual.Actor := by
  let f := originalAction c
  let z : D.fullModule := ⟨a*b,D.fullModule.mul_mem
    (pair_moved_le s c.first_mem) (pair_partner_le s c.second_mem)⟩
  let v := Natural.fullCoordinates s c.fixed z
  have hv : ∀ i, v i ≠ 1 := Natural.diagonal_coordinates_ne_one s c.fixed
    c.first_mem c.second_mem c.first_ne c.second_ne
  let e := f.parabolicQuotientEquiv z
    (Natural.PointModel.pointStabilizerEquivSymmetricWreath v hv)
  let eSL := Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three
  exact e.trans (RegularWreathProduct.congr eSL.symm (MulEquiv.refl _))

/-- The original seed modulo its own two-core is elementary of order nine. -/
theorem quotient_nine (c : Configuration s a b) :
    Nonempty ((centralizerSeed T L (a*b) ⧸ pCore 2 (centralizerSeed T L (a*b))) ≃*
      Multiplicative (Fin 2 → ZMod 3)) := by
  let P := diagonalParabolic T L (a*b)
  obtain ⟨e⟩ := WreathTwoResidual.residual_core_quotient_equiv_elementaryNine (parabolicQuotient c)
  let f : pResidual 2 P ≃* centralizerSeed T L (a*b) :=
    ((pResidual 2 P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (diagonalParabolic_residual (a*b)))
  exact ⟨(QuotientGroup.congr _ _ f.symm (pCore_map_iso 2 f.symm)).trans e⟩

/-- The seed retains a nontrivial odd quotient. -/
theorem not_two (c : Configuration s a b) : ¬ IsPGroup 2 (centralizerSeed T L (a*b)) := by
  intro hp
  obtain ⟨e⟩ := quotient_nine c
  have hq := hp.of_surjective (QuotientGroup.mk' (pCore 2 (centralizerSeed T L (a*b))))
    (QuotientGroup.mk'_surjective _)
  have h9 : IsPGroup 2 (Multiplicative (Fin 2 → ZMod 3)) := hq.of_equiv e
  obtain ⟨n,hn⟩ := h9.exists_card_eq
  have hc : Nat.card (Multiplicative (Fin 2 → ZMod 3)) = 9 := by
    change Nat.card (Fin 2 → ZMod 3) = 9
    simp
  have hd : 3 ∣ 2 ^ n := by rw [← hn,hc]; decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem point_not_two (v : Eight) (hv : v ≠ 1) :
    ¬ IsPGroup 2 (MulAction.stabilizer SL v.toAdd) := by
  obtain ⟨g,hg⟩ := Matrix.SpecialLinearGroup.exists_mulVec_eq_three
    flagPoint.val v.toAdd flagPoint.property hv
  change g • flagPoint.val = v.toAdd at hg
  have he : MulAction.stabilizer SL v.toAdd =
      pointParabolicSL.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
    congr 1
    ext x
    rw [← Fano.stabilizer_flagPoint_SL]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  intro h
  have hp := (he ▸ h).of_equiv ((MulAut.conj g).subgroupMap pointParabolicSL).symm
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hd : 3 ∣ 2^n := by rw [← hn,card_pointParabolicSL]; decide
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)

private theorem core_right (v : Space) (hv : v 1 ≠ 1)
    (x : pointStabilizer v) (hx : x ∈ pCore 2 (pointStabilizer v)) :
    x.val.right = 1 := by
  classical
  by_contra hright
  have hr : x.val.right = other := (bit_cases x.val.right).resolve_left hright
  let S := pointStabilizer v
  let N := pCore 2 S
  let B : Subgroup S := (RegularWreathProduct.rightHom : Actor →* Bit).ker.comap S.subtype
  let NB := N ⊓ B
  let A : Subgroup SL := MulAction.stabilizer SL (v 1).toAdd
  have fix (y : NB) : y.val.val.left 1 ∈ A := by
    have hh := congrFun y.val.property 1
    have hr : y.val.val.right = 1 := y.property.2
    change action y.val.val v 1 = v 1 at hh
    rw [action_apply,hr] at hh
    change (y.val.val.left 1).val *ᵥ (v 1).toAdd = (v 1).toAdd
    simpa only [inv_one,one_mul,toAdd_ofAdd] using congrArg Multiplicative.toAdd hh
  let f : NB →* A := {
    toFun y := ⟨y.val.val.left 1,fix y⟩
    map_one' := rfl
    map_mul' y z := by
      apply Subtype.ext
      change y.val.val.left 1 * z.val.val.left (y.val.val.right⁻¹ * 1) = _
      rw [show y.val.val.right = 1 from y.property.2]
      simp }
  have onto : Function.Surjective f := by
    intro a
    have ha : firstBase a.val ∈ S := by
      change action (firstBase a.val) v = v
      funext i
      rw [firstBase_action]
      by_cases hi : i = 1
      · subst i
        simp only [ite_true]
        exact congrArg Multiplicative.ofAdd a.property
      · simp only [hi,if_false]
    let aS : S := ⟨firstBase a.val,ha⟩
    let y : S := aS * x * aS⁻¹ * x⁻¹
    have hyn : y ∈ N := N.mul_mem
      ((inferInstance : N.Normal).conj_mem x hx aS) (N.inv_mem hx)
    have hyb : y ∈ B := by
      change (firstBase a.val * x.val * (firstBase a.val)⁻¹ * x.val⁻¹).right = 1
      simp [firstBase]
    refine ⟨⟨y,hyn,hyb⟩,?_⟩
    apply Subtype.ext
    change (firstBase a.val * x.val * (firstBase a.val)⁻¹ * x.val⁻¹).left 1 = a.val
    simp [RegularWreathProduct.mul_left,RegularWreathProduct.inv_left,firstBase,hr]
  exact point_not_two (v 1) hv (((pCore_isPGroup (p := 2) (G := S)).to_le inf_le_left).of_surjective f onto)

private theorem normalizes_of_right (c : Configuration s a b) (g : localJoin T L)
    (hg : ((originalLift s c.fixed).hom g).right = 1) :
    (g : G) ∈ normalizer (L : Set G) := by
  by_contra hout
  have hgm : (g : G) ∈ D.maximalLocal :=
    (sup_le (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)) g.property
  have hLg : L.map (MulAut.conj (g : G)).toMonoidHom =
      L.map (MulAut.conj s.exchange).toMonoidHom := by
    exact (source_nonnormal_maximal_pair D (pair_nonnormal s)
      s.exchange_mem s.exchange_moves g hgm).resolve_left
        (fun h => hout (mem_normalizer_iff_map_conj_eq.mpr h))
  have hVg : (⁅D.fullModule,L⁆).map (MulAut.conj (g : G)).toMonoidHom =
      (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := by
    have hV (m : G) (hm : m ∈ D.maximalLocal) :
        D.fullModule.map (MulAut.conj m).toMonoidHom = D.fullModule :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule hm)
    rw [map_commutator,map_commutator,hV g hgm,
      hV s.exchange (le_normalizer_componentOrbit L T s.exchange_mem),hLg]
  let av : (⁅D.fullModule,L⁆ : Subgroup G) := ⟨a,c.first_mem⟩
  let bv : ((⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom) :=
    ⟨(g : G)*a*(g : G)⁻¹, hVg ▸ mem_map_of_mem (MulAut.conj (g : G)).toMonoidHom c.first_mem⟩
  have he : joinAction D g (factorProduct s c.fixed (av,1)) =
      factorProduct s c.fixed (1,bv) := by
    apply Subtype.ext
    rw [joinAction_apply,factorProduct_apply,factorProduct_apply]
    simp only [OneMemClass.coe_one,mul_one,one_mul]
    rfl
  have hh := congrFun ((originalLift s c.fixed).equivariant g
    (factorProduct s c.fixed (av,1))) 1
  rw [he,coordinates_factorProduct,action_apply,hg] at hh
  simp only [ite_true,map_one,inv_one,one_mul] at hh
  rw [coordinates_factorProduct] at hh
  simp only [ite_true] at hh
  have hz : Matrix.SpecialLinearGroup.toLin' (((originalLift s c.fixed).hom g).left 1)
      (s.natural.coordinates av).toAdd = 0 := (congrArg Multiplicative.toAdd hh).symm
  exact first_coordinates_ne_one c
    ((Matrix.SpecialLinearGroup.toLin' _).map_eq_zero_iff.mp hz)

/-- The literal diagonal-parabolic core preserves the original component. -/
theorem parabolic_core_le_stabilizer (c : Configuration s a b) :
    (diagonalParabolic T L (a*b)).pCoreIn 2 ≤
      (T : Subgroup G) ⊓ normalizer (L : Set G) := by
  let P := diagonalParabolic T L (a*b)
  have hQT : P.pCoreIn 2 ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow P (T.subtype (sylow_le_diagonalParabolic c.central))
    change P.pCoreIn 2 ≤ ((T : Subgroup G).subgroupOf P).map P.subtype at hh
    rwa [map_subgroupOf_eq_of_le (sylow_le_diagonalParabolic c.central)] at hh
  refine le_inf hQT ?_
  rintro g ⟨x,hx,rfl⟩
  have hmap : (pCore 2 P).map (pointMap c) ≤
      pCore 2 (Natural.pointStabilizer (Natural.fullCoordinates s c.fixed (diagonalVector c))) :=
    le_sSup ⟨(inferInstance : (pCore 2 P).Normal).map _ (pointMap_surjective c),
      pCore_isPGroup.map (pointMap c)⟩
  have hr := core_right _ (Natural.diagonal_coordinates_ne_one s c.fixed
    c.first_mem c.second_mem c.first_ne c.second_ne 1) (pointMap c x)
      (hmap (mem_map_of_mem (pointMap c) hx))
  exact normalizes_of_right c (inclusion (diagonalParabolic_le_join (a*b)) x) hr
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local

-- Adapted from Geometry/CoreReduced/Seed/Local/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Overgroups.Closure.Parabolic
open CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Overgroups.Closure.Parabolic
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- Every original T-normal subgroup outside T₁ generates X by commutators. -/
theorem commutator (c : Configuration s a b) (R : Subgroup G)
    (hRT : R ≤ (T : Subgroup G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hout : ¬ R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)) :
    ⁅centralizerSeed T L (a*b),R⁆ = centralizerSeed T L (a*b) := by
  let P := diagonalParabolic T L (a*b)
  have hTP : (T : Subgroup G) ≤ P := sylow_le_diagonalParabolic c.central
  have hRP : R ≤ P := hRT.trans hTP
  let S := T.subtype hTP
  have hmax := WreathTwoResidual.sylow_isCoatom_of_core_quotient S (parabolicQuotient c)
  have hu : Order.HasUniqueMaximalOver (S : Subgroup P) ⊤ := by
    refine ⟨lt_top_iff_ne_top.mpr hmax.ne_top,(S : Subgroup P),⟨le_rfl,hmax.covBy_top⟩,?_⟩
    intro M hM
    rcases eq_or_lt_of_le hM.1 with h | h
    · exact h.symm
    · exact (hM.2.ne (hmax.2 _ h)).elim
  have hnot : ¬ R.subgroupOf P ≤ pCore 2 P := by
    intro h
    apply hout
    intro r hr
    exact parabolic_core_le_stabilizer c ⟨⟨r,hRP hr⟩,h hr,rfl⟩
  have hn : (S : Subgroup P) ≤ normalizer (R.subgroupOf P : Set P) := by
    rw [← subgroupOf_normalizer_eq hRP]
    exact fun x hx => hTR hx
  have he := commutator_twoResidual_eq_of_normal_sylow_subgroup S hu
    (R.subgroupOf P) (fun _ hx => hRT hx) hn hnot
  have hh := congrArg (map P.subtype) he
  rw [map_commutator,diagonalParabolic_residual,map_subgroupOf_eq_of_le hRP] at hh
  exact hh

/-- All three calculations for the same original source configuration. -/
theorem localCalculation (c : Configuration s a b) : LocalCalculation c where
  prime_spectrum := prime_spectrum c
  not_two := not_two c
  commutator := commutator c

/-- The complete local calculation, without a core, action, or recognition premise. -/
theorem localCalculationAt (T : Sylow 2 G) : LocalCalculationAt T := by
  intro L D s a b c
  exact localCalculation c

/-- The actual seed consumer now retains only the independent module calculation. -/
theorem seedAnalysisAt_of_moduleGeneration (hmodule : ModuleGenerationAt T) : SeedAnalysisAt T :=
  seedAnalysisAt_of_calculations (localCalculationAt T) hmodule

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Local

-- Adapted from Geometry/CoreReduced/Seed/Generation/Factors.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Generation
open Chapter3.Section02
open Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- The residual of an original nonidentity point centralizer generates its factor. -/
theorem moved_le_point_commutator (c : Configuration s a b)
    {v : G} (hv : v ∈ ⁅D.fullModule,L⁆) (hne : v ≠ 1) :
    ⁅D.fullModule,L⁆ ≤
      ⁅⁅D.fullModule,L⁆, (pResidual 2 (L ⊓ centralizer ({v} : Set G) : Subgroup G)).map
        (L ⊓ centralizer ({v} : Set G)).subtype⁆ := by
  let f := s.quotient.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let e : (⁅D.fullModule,L⁆ : Subgroup G) ≃* Model :=
    MulEquiv.ofBijective s.natural.coordinates (natural_coordinates_bijective c)
  refine Representation.BinaryNaturalResidual.natural_factor_le_commutator
    L ⁅D.fullModule,L⁆ s.natural.normalized f
      (s.quotient.surjective.comp (QuotientGroup.mk'_surjective _)) e ?_ ⟨v,hv⟩ ?_
  · intro l x
    apply Multiplicative.toAdd.injective
    rw [slAut_apply]
    exact s.natural.equivariant l x
  · exact fun h => hne (congrArg Subtype.val h)

/-- The first factor is generated by commutators with the literal diagonal seed. -/
theorem first_le_seed_commutator (c : Configuration s a b) :
    ⁅D.fullModule,L⁆ ≤ ⁅D.fullModule, centralizerSeed T L (a*b)⁆ := by
  have hP : L ⊓ centralizer ({a} : Set G) ≤
      localOrbit T L ⊓ centralizer ({a*b} : Set G) := by
    refine le_inf (inf_le_left.trans (le_componentOrbit L T)) ?_
    intro g hg
    apply mem_centralizer_singleton_iff.mpr
    have ha := mem_centralizer_singleton_iff.mp hg.2
    have hb := s.crossed c.second_mem g hg.1
    calc
      g*(a*b) = (g*a)*b := (mul_assoc _ _ _).symm
      _ = (a*g)*b := by rw [ha]
      _ = a*(g*b) := mul_assoc _ _ _
      _ = a*(b*g) := by rw [hb]
      _ = (a*b)*g := (mul_assoc _ _ _).symm
  exact (moved_le_point_commutator c c.first_mem c.first_ne).trans
    (commutator_mono (pair_moved_le s) (embedded_pResidual_mono 2 hP))

/-- The specified exchanged factor is generated by the same seed. -/
theorem partner_le_seed_commutator (c : Configuration s a b) :
    (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom ≤
      ⁅D.fullModule, centralizerSeed T L (a*b)⁆ := by
  obtain ⟨v,hv,hvb⟩ := mem_map.mp c.second_mem
  have hne : v ≠ 1 := by
    intro h
    apply c.second_ne
    rw [← hvb, h, map_one]
  let f := (MulAut.conj s.exchange).toMonoidHom
  have hcross : ⁅D.fullModule,L⁆ ≤
      centralizer (L.map f : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (source_a5_moved_normalizer_opposite_cross D
        s.exchange_mem s.exchange_moves s.crossed)
  have hpair : localOrbit T L = L ⊔ L.map f :=
    componentOrbit_eq_sup_of_index_two L T (normalizer (L : Set G))
      (source_nonnormal_sylow_stabilizer_index D.simpleQTKE D.maximal.1
        (pair_nonnormal s)) inf_le_right s.exchange_mem s.exchange_moves
  have hP : (L ⊓ centralizer ({v} : Set G)).map f ≤
      localOrbit T L ⊓ centralizer ({a*b} : Set G) := by
    rintro g ⟨l,hl,rfl⟩
    have hl' : f l ∈ L.map f := mem_map_of_mem f hl.1
    refine ⟨(le_sup_right.trans_eq hpair.symm) hl', ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    have ha := hcross c.first_mem (f l) hl'
    have hb : f l * b = b * f l := by
      rw [← hvb]
      simpa only [map_mul] using congrArg f (mem_centralizer_singleton_iff.mp hl.2)
    calc
      f l*(a*b) = (f l*a)*b := (mul_assoc _ _ _).symm
      _ = (a*f l)*b := by rw [ha]
      _ = a*(f l*b) := mul_assoc _ _ _
      _ = a*(b*f l) := by rw [hb]
      _ = (a*b)*f l := (mul_assoc _ _ _).symm
  have hm := map_mono (f := f) (moved_le_point_commutator c hv hne)
  rw [map_commutator ⁅D.fullModule,L⁆ _ f, map_embedded_pResidual] at hm
  exact hm.trans (commutator_mono (pair_partner_le s)
    (embedded_pResidual_mono 2 hP))

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Generation

-- Adapted from Geometry/CoreReduced/Seed/Generation/Source.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Generation
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreePair T D} {a b : G}

/-- Both original natural factors lie in the seed commutator subgroup. -/
theorem full_eq_seed_commutator (c : Configuration s a b) :
    D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ := by
  apply le_antisymm
  · calc
      D.fullModule = ⁅D.fullModule,L⁆ ⊔
          (⁅D.fullModule,L⁆).map (MulAut.conj s.exchange).toMonoidHom := s.generated
      _ ≤ ⁅D.fullModule, centralizerSeed T L (a*b)⁆ :=
        sup_le (first_le_seed_commutator c) (partner_le_seed_commutator c)
  · apply le_normalizer_iff_commutator_le_left.mp
    exact ((map_subtype_le _).trans inf_le_left).trans
      ((localOrbit T L).le_normalizer.trans D.maximalLocal_normalizes_fullModule)

/-- The exact natural-action supplement, with the original two vectors. -/
theorem module_generation (c : Configuration s a b) :
    D.fullModule = ⁅D.fullModule, centralizerSeed T L (a*b)⁆ ⊔
      (zpowers a ⊔ zpowers b) := by
  apply le_antisymm ((full_eq_seed_commutator c).le.trans le_sup_left)
  exact sup_le (full_eq_seed_commutator c).ge
    (sup_le (zpowers_le.mpr (pair_moved_le s c.first_mem))
      (zpowers_le.mpr (pair_partner_le s c.second_mem)))

/-- The representation obligation in the original SeedAnalysis assembly is discharged. -/
theorem moduleGenerationAt (T : Sylow 2 G) : ModuleGenerationAt T := by
  intro L D s a b c
  exact module_generation c

/-- Apply the proved generation identity to the original five-field seed contract.
The independent local calculation remains with its source producer. -/
theorem seedAnalysisAt_of_localCalculation (hlocal : LocalCalculationAt T) :
    SeedAnalysisAt T :=
  seedAnalysisAt_of_calculations hlocal (moduleGenerationAt T)

/-- The literal centralizer-core consumer needs no further module-generation premise.
The local and full-action source branches retain their separate assembly owners. -/
theorem coreReduced_of_localCalculation (hlocal : LocalCalculationAt T)
    (haction : FullActionCentralizationAt T) : CoreReducedAt T :=
  coreReduced_of_calculations hlocal (moduleGenerationAt T) haction

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed.Generation

-- Adapted from Geometry/CoreReduced/Seed/Assembly.lean.
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
variable {G : Type*} [Group G] [Finite G]

/-- The complete original seed analysis, including the literal residual action. -/
theorem seedAnalysisAt (T : Sylow 2 G) : SeedAnalysisAt T :=
  seedAnalysisAt_of_calculations (Local.localCalculationAt T) (Generation.moduleGenerationAt T)

end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Earlier.Geometry.CoreReduced.Seed
