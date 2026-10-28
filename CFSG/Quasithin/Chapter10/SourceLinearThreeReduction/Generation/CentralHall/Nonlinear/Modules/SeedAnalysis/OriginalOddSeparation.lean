module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.SeedCubic
public import CFSG.Quasithin.ChapterD.Section03.OddTensor
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.Modules.SeedAnalysis.OriginalJanko

/-!
# Odd-prime separation on the unchanged central Hall seed

Failure of separation makes the original seed a faithful irreducible
PSL₂(p) square. Its proved cubic bound contradicts the full-normalizer tensor
exclusion for p at least eleven, including both preserving and exchanging
actors. This proves separation and crossed movement in both original
orientations, without assuming the Sylow exchanger lies in a small actor.

The original non-A₅ and non-SL₃(2) hypotheses remove the small primes.
Together with the checked Suzuki and J₁ exclusions, the genuine catalogue
leaves only even-linear quotients in the nonseparated case.

The literal Hall consumer retains only moved minimality. Even-linear
separation and constituent minimality remain with the final assembly owner
qt-d-10-nona5-central-hall-orders; SeedAnalysisAt and
SourceNonnormalCentralHallAt are not asserted here.
Source: Aschbacher--Smith D.3.7, 3.2.6 and10.1.1, printed pp.197--199,581,741.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
local instance : IsElementaryAbelian 2 D.seed := D.seed_elementary

/-- The original cubic bound excludes odd-prime tensor support. -/
theorem original_seed_separated_of_odd_prime
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  let := D.quasisimple
  let : IsSimpleGroup (L ⧸ pCore 2 L) := component_simple D c.nonnormal
  let : IsSimpleGroup PSL(2,ZMod p) := e.symm.isSimpleGroup
  let : IsQuasisimple PSL(2,ZMod p) := IsQuasisimple.of_mulEquiv e
  by_contra hsep
  have hsmall := original_seed_normalizer_cubic_of_not_separated D c ht htn hsep
  let : FiniteDimensional (ZMod 2) (Additive D.seed) := Module.Finite.of_finite
  obtain ⟨q,hq,_,hl,hr,σ,hi,hσ⟩ := original_seed_product_action D c e ht htn
  have hf := original_seed_product_faithful_of_not_separated D e ht hsep q hl hr σ hσ
  have himage : actionImage (originalSeedAction D) = actionImage σ := by
    rw [←hσ]
    ext x
    constructor
    · rintro ⟨l,rfl⟩
      exact ⟨q l,Units.ext rfl⟩
    · rintro ⟨g,rfl⟩
      obtain ⟨l,rfl⟩ := hq g
      exact ⟨l,Units.ext rfl⟩
  have hsmallσ : cubicRatio (normalizerRepresentation σ) ≤ 2 := by
    unfold normalizerRepresentation linearNormalizer at hsmall ⊢
    rwa [himage] at hsmall
  exact (not_le_of_gt (ChapterD.odd_prime_square_normalizer_cubicRatio_gt hp
    (IsSQTK.knownSimple_of_equiv e (original_component_quotient_sqtk D)) σ hi hf)) hsmallσ


/-- The actual odd-prime moved factor centralizes its opposite, in both seed orientations. -/
theorem original_odd_prime_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    {p : ℕ} [Fact p.Prime] (hp : 11 ≤ p)
    (e : (L ⧸ pCore 2 L) ≃* PSL(2,ZMod p))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  full_moved_centralizes_opposite_of_seed_separated D ht htn
    (original_seed_separated_of_odd_prime D c hp e ht htn)

/-- The original non-A₅, non-SL₃(2) hypotheses remove every small prime.
The marking remains on the literal component quotient. -/
theorem original_odd_prime_parameter_large
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p) : 11 ≤ p := by
  have hp3 : p ≠ 3 := by
    intro hp3
    obtain ⟨F,_,_,hc,⟨e⟩⟩ := hm
    let := D.quasisimple
    let : Group.IsPerfect (L ⧸ pCore 2 L) := inferInstance
    let : Group.IsPerfect PSL(2,F) := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three
      (hc.trans hp3) inferInstance
  have hp5 : p ≠ 5 := by
    intro hp5
    exact c.not_a5 (ChapterK.OddCharacteristic.altFive_of_psl2_five (hp5 ▸ hm))
  have hp7 : p ≠ 7 := by
    intro hp7
    obtain ⟨e⟩ := ChapterK.OddCharacteristic.psl3Two_of_psl2_seven (hp7 ▸ hm)
    exact hnot ⟨e.trans (Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm.trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two)⟩
  by_contra! hsmall
  interval_cases p <;> norm_num at *

/-- Every odd-prime row in the original component catalogue is separated;
no lower bound on its prime or extra actor premise is required. -/
theorem original_seed_separated_of_odd_model
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G) := by
  have hlarge := original_odd_prime_parameter_large D c hnot hp ho hm
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := (ZMod.ringEquivOfPrime F hp (by
    simpa only [Nat.card_eq_fintype_card] using hF)).symm
  exact original_seed_separated_of_odd_prime D c hlarge
    (e.trans (Atlas.fieldEquivPSL 2 eF)) ht htn

/-- Crossed movement in every odd-prime source row, on the original module. -/
theorem original_odd_model_crossed
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G)) :
    ⁅D.fullModule,L⁆ ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) :=
  full_moved_centralizes_opposite_of_seed_separated D ht htn
    (original_seed_separated_of_odd_model D c hnot hp ho hm ht htn)

/-- After separation, moved minimality excludes every odd-prime source row. -/
theorem not_odd_model_of_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)
    (hmin : MovedMinimal D) : False := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp c.nonnormal
  have hs := separatedSeed_of_separated_and_movedMinimal D hmin ht htn
    (original_seed_separated_of_odd_model D c hnot hp ho hm ht htn)
  have hg := (geometry_and_minimality_of_separatedSeed D ht htn hs).1
  exact not_odd_prime_model D c hg hmin (cubic_bounds D c).1 hnot hp ho hm

/-- The complete odd-prime exclusion reaches the literal Hall consumer.
Moved minimality remains with the final source assembly owner. -/
theorem hall_exponent_of_odd_model_and_moved_minimal
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 p)
    (hmin : MovedMinimal D) :
    ∃ n : ℕ, 1 < n ∧ Monoid.exponent B ∣ 2 ^ n + 1 :=
  (not_odd_model_of_moved_minimal D c hnot hp ho hm hmin).elim
/-- The genuine four-model catalogue leaves only an even-linear quotient
when the unchanged seed is not separated. -/
theorem original_nonseparated_model_even
    {H : Subgroup G} {B : Subgroup H} (c : Context D H B)
    (hnot : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* SL(3,ZMod 2)))
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hsep : ¬ (D.seed ≤ centralizer (L.map (MulAut.conj t).toMonoidHom : Set G) ∨
      D.seed ≤ centralizer (L : Set G))) :
    ∃ n : ℕ, 2 ≤ n ∧ ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) := by
  cases component_model D c.nonnormal with
  | linear_even n hn hm => exact ⟨n,hn,hm⟩
  | suzuki m hm he =>
    exact (hsep (original_seed_separated_of_suzuki D c m (by omega) he.some ht htn)).elim
  | linear_prime p hp ho hm =>
    exact (hsep (original_seed_separated_of_odd_model D c hnot hp ho hm ht htn)).elim
  | janko he =>
    exact (hsep (original_seed_separated_of_janko D c he.some ht htn)).elim

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.Modules
