module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.QuotientInputs
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.SmallExclusions
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.FixedCentralizers.Nonquasisimple.ModelSieve.StarResidualContract
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Lifting.Transport
public import Theory.SpecificGroups.PSL2.AutomorphismModel
public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer

/-!
# Block and Borel comparisons for the fixed component

The marked K-image's A₅ two-residual makes the stabilizer nonsolvable,
forces a factor of five, and excludes a second factor of three. The actual
core-to-star map transfers the binary rank-one model to the star image,
whose Borel is solvable. Transposition centralizers in degrees five through
eight have orders 6, 24, 120, and 720, leaving degree seven. Neither A₆
partition stabilizer has an element of order five: such an element fixes
every part and then every point. Finally the actual derived G₂(2) carrier
has order 6048, so its core model cannot contain the marked residual.

The fixed-centralizer applications retain the literal C.2.7 constructor
hypotheses. `HasA5TwoResidual` remains an explicit input, produced by
qt-14-07-fixed-star-local-residual and discharged by the parent model sieve;
these conditional comparisons do not assert the full 14.7.68 theorem.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
C.2.7 pp.145--147, A.3.14 pp.49--50, and 14.7.68(2) pp.1071--1072.
-/

@[expose] public section
noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped Pointwise
open Equiv Equiv.Perm
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Chapter1.RadicalExclusions.ModelReduction
open Nonquasisimple

namespace Nonquasisimple

/-- A two-group extension of a perfect subgroup with A₅ residual is
nonsolvable.  The proof passes through the actual residual quotient. -/
theorem HasA5TwoResidual.not_isSolvable {M : Type*} [Group M]
    (h : HasA5TwoResidual M) [Group.IsSolvable M] : False := by
  obtain ⟨B, hB, hperf, ⟨e⟩, _⟩ := h
  let := hB
  let : Group.IsSolvable B :=
    Group.isSolvable_of_isSolvable_injective (f := B.subtype) B.subtype_injective
  let : Group.IsSolvable (B ⧸ pCore 2 B) :=
    Group.isSolvable_of_surjective (QuotientGroup.mk'_surjective (pCore 2 B))
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

/-- The A₅ quotient forces five to divide the order of the stabilizer. -/
theorem HasA5TwoResidual.five_dvd_card {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) : 5 ∣ Nat.card M := by
  obtain ⟨B, hB, _, ⟨e⟩, _⟩ := h
  let := hB
  have hq : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcore := (pCore 2 B).card_mul_index
  change Nat.card (pCore 2 B) * Nat.card (B ⧸ pCore 2 B) = Nat.card B at hcore
  rw [hq] at hcore
  have h60 : 60 ∣ Nat.card B := by
    refine ⟨Nat.card (pCore 2 B), ?_⟩
    simpa [Nat.mul_comm] using hcore.symm
  have h5B : 5 ∣ Nat.card B := (by decide : 5 ∣ 60).trans h60
  have hcard := B.card_mul_index
  exact h5B.trans ⟨B.index, hcard.symm⟩

/-- The A₅ quotient has only one factor of three; the two-core and the
two-group extension cannot supply a second factor. -/
theorem HasA5TwoResidual.not_nine_dvd_card {M : Type*} [Group M] [Finite M]
    (h : HasA5TwoResidual M) : ¬ 9 ∣ Nat.card M := by
  intro h9
  obtain ⟨B, hB, _, ⟨e⟩, hQ⟩ := h
  let := hB
  have hqpow := hQ.exists_card_dvd_pow
  obtain ⟨m, hm⟩ := hqpow
  have hcardB := B.card_mul_index
  have h9prod : 9 ∣ Nat.card B * Nat.card (M ⧸ B) := by
    exact hcardB ▸ h9
  have hcopQ : Nat.Coprime 9 (Nat.card (M ⧸ B)) := by
    exact (by decide : Nat.Coprime 9 2).pow_right m |>.of_dvd_right hm
  have h9B : 9 ∣ Nat.card B := hcopQ.dvd_of_dvd_mul_right h9prod
  have hq : Nat.card (B ⧸ pCore 2 B) = 60 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcore := (pCore 2 B).card_mul_index
  change Nat.card (pCore 2 B) * Nat.card (B ⧸ pCore 2 B) = Nat.card B at hcore
  rw [hq] at hcore
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := B)).exists_card_dvd_pow
  have h9mul0 : 9 ∣ Nat.card (pCore 2 B) * 60 := hcore ▸ h9B
  have h9mul : 9 ∣ 2 ^ k * 60 :=
    h9mul0.trans (Nat.mul_dvd_mul_right hk 60)
  have hcop : Nat.Coprime 9 (2 ^ k) := (by decide : Nat.Coprime 9 2).pow_right k
  have hbad : 9 ∣ 60 := hcop.dvd_of_dvd_mul_left h9mul
  norm_num at hbad

end Nonquasisimple

namespace Data

/-- The even part of a symmetric centralizer has half the order of the
full centralizer whenever the marked permutation is odd. -/
private theorem alternatingCentralizer_card_mul_two {n : ℕ}
    (q : Equiv.Perm (Fin n)) (hq : Equiv.Perm.sign q = -1) :
    Nat.card (alternatingGroup (Fin n) ⊓
      centralizer ({q} : Set (Equiv.Perm (Fin n))) : Subgroup (Equiv.Perm (Fin n))) * 2 =
      Nat.card (centralizer ({q} : Set (Equiv.Perm (Fin n)))) := by
  let C : Subgroup (Equiv.Perm (Fin n)) := centralizer ({q} : Set (Equiv.Perm (Fin n)))
  let f : C →* ℤˣ := Equiv.Perm.sign.comp C.subtype
  have hf : Function.Surjective f := by
    intro u
    rcases Int.units_eq_one_or u with rfl | rfl
    · exact ⟨1, f.map_one⟩
    · exact ⟨⟨q, mem_centralizer_singleton_iff.mpr rfl⟩, hq⟩
  have hk : f.ker = (alternatingGroup (Fin n) ⊓ C).subgroupOf C := by
    ext x
    change Equiv.Perm.sign x.val = 1 ↔
      x.val ∈ alternatingGroup (Fin n) ∧ x.val ∈ C
    simp only [Equiv.Perm.mem_alternatingGroup, x.property, and_true]
  have hc : Nat.card f.ker =
      Nat.card (alternatingGroup (Fin n) ⊓ C : Subgroup (Equiv.Perm (Fin n))) :=
    Nat.card_congr ((MulEquiv.subgroupCongr hk).trans
      (Subgroup.subgroupOfEquivOfLe inf_le_right)).toEquiv
  have hi : f.ker.index = 2 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf]
    simpa only [Nat.card_eq_fintype_card, Fintype.card_units_int] using
      Nat.card_congr (Subgroup.topEquiv (G := ℤˣ)).toEquiv
  rw [← hc, ← hi]
  exact f.ker.card_mul_index

/-- The cardinality of the alternating centralizer of a transposition in the
four degrees that occur in C.2.7(b). -/
theorem alternatingTranspositionCentralizer_card {n : ℕ}
    (hn : 5 ≤ n) (hn' : n ≤ 8) (q : Equiv.Perm (Fin n)) (hq : q.IsSwap) :
    Nat.card (alternatingGroup (Fin n) ⊓
      centralizer ({q} : Set (Equiv.Perm (Fin n))) : Subgroup (Equiv.Perm (Fin n))) =
      if n = 5 then 6 else if n = 6 then 24 else if n = 7 then 120 else 720 := by
  have hs : Equiv.Perm.sign q = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, isSwap_iff_cycleType.mp hq]
    decide
  have hc := alternatingCentralizer_card_mul_two q hs
  rw [Equiv.Perm.nat_card_centralizer, isSwap_iff_cycleType.mp hq] at hc
  interval_cases n
  · norm_num at ⊢
    apply Nat.eq_of_mul_eq_mul_right (m := 2) (k := 6) (by decide)
    norm_num [Nat.factorial] at hc ⊢
    exact hc
  · norm_num at ⊢
    apply Nat.eq_of_mul_eq_mul_right (m := 2) (k := 24) (by decide)
    norm_num [Nat.factorial] at hc ⊢
    exact hc
  · norm_num at ⊢
    apply Nat.eq_of_mul_eq_mul_right (m := 2) (k := 120) (by decide)
    norm_num [Nat.factorial] at hc ⊢
    exact hc
  · norm_num at ⊢
    apply Nat.eq_of_mul_eq_mul_right (m := 2) (k := 720) (by decide)
    norm_num [Nat.factorial] at hc ⊢
    exact hc

private theorem alternating_starM_map_eq
    {G : Type*} [Group G] {K R MH : Subgroup G} {n : ℕ}
    (hM : starM K R MH = starImage K R K ⊓
      Subgroup.centralizer (starImage K R R : Set (StarQuotient K R)))
    (e : AlternatingComponentModel K R n)
    (r : StarQuotient K R) (t : Equiv.Perm (Fin n))
    (hrad : starImage K R R = closure {r})
    (hact : ∀ k k' : starImage K R K,
      (k' : StarQuotient K R) = r * (k : StarQuotient K R) * r⁻¹ ↔
        (e.groupIso k' : Equiv.Perm (Fin n)) =
          t * (e.groupIso k : Equiv.Perm (Fin n)) * t⁻¹) :
    let φ : starImage K R K →* Equiv.Perm (Fin n) :=
      (alternatingGroup (Fin n)).subtype.comp e.groupIso.toMonoidHom
    ((starM K R MH).subgroupOf (starImage K R K)).map φ =
      alternatingGroup (Fin n) ⊓ centralizer ({t} : Set (Equiv.Perm (Fin n))) := by
  let φ : starImage K R K →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp e.groupIso.toMonoidHom
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(e.groupIso y).property, ?_⟩
    apply mem_centralizer_singleton_iff.mpr
    apply (eq_mul_inv_iff_mul_eq).mp
    apply (hact y y).mp
    apply (eq_mul_inv_iff_mul_eq).mpr
    have hyM : (y : StarQuotient K R) ∈ starM K R MH := mem_subgroupOf.mp hy
    rw [hM, hrad, Subgroup.centralizer_closure] at hyM
    exact mem_centralizer_singleton_iff.mp hyM.2
  · intro hx
    obtain ⟨y, hy⟩ := e.groupIso.surjective ⟨x, hx.1⟩
    refine ⟨y, ?_, ?_⟩
    rw [hM]
    refine ⟨?_, ?_⟩
    · exact y.property
    · rw [hrad, Subgroup.centralizer_closure]
      apply mem_centralizer_singleton_iff.mpr
      apply (eq_mul_inv_iff_mul_eq).mp
      have heq : (e.groupIso y : Equiv.Perm (Fin n)) = x := congrArg Subtype.val hy
      apply (hact y y).mpr
      rw [heq]
      exact (eq_mul_inv_iff_mul_eq).mpr (mem_centralizer_singleton_iff.mp hx.2)
    · exact congrArg Subtype.val hy

/-- The literal transposition action and centralizer clause of C.2.7(b)
force degree seven for a stabilizer with this A₅ residual. -/
theorem alternating_force_seven
    {G : Type*} [Group G] [Finite G] {K R MH : Subgroup G} {n : ℕ}
    (hA : HasA5TwoResidual (starM K R MH))
    (lower : 5 ≤ n) (upper : n ≤ 8)
    (action : TranspositionAction K R n)
    (centralizerEq : starM K R MH =
      starImage K R K ⊓ centralizer (starImage K R R : Set (StarQuotient K R))) :
    n = 7 := by
  obtain ⟨e, r, t, hr, hrad, ht, hact⟩ := action
  let φ : starImage K R K →* Equiv.Perm (Fin n) :=
    (alternatingGroup (Fin n)).subtype.comp e.groupIso.toMonoidHom
  have hφ : Function.Injective φ :=
    (alternatingGroup (Fin n)).subtype_injective.comp e.groupIso.injective
  have hmap := alternating_starM_map_eq centralizerEq e r t hrad hact
  have hsubcard : Nat.card ↥((starM K R MH).subgroupOf (starImage K R K)) =
      Nat.card ↥(starM K R MH) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (starM_le K R MH)).toEquiv
  have hmapcard := Subgroup.card_map_of_injective (K :=
    (starM K R MH).subgroupOf (starImage K R K)) hφ
  rw [hmap] at hmapcard
  have hcard : Nat.card (starM K R MH) =
      Nat.card (alternatingGroup (Fin n) ⊓
        centralizer ({t} : Set (Equiv.Perm (Fin n))) :
          Subgroup (Equiv.Perm (Fin n))) :=
    hsubcard.symm.trans hmapcard.symm
  have hcard' := hcard.trans (alternatingTranspositionCentralizer_card lower upper t ht)
  have h5 : 5 ∣ Nat.card (starM K R MH) := hA.five_dvd_card
  interval_cases n
  · norm_num at hcard'
    rw [hcard'] at h5
    norm_num at h5
  · norm_num at hcard'
    rw [hcard'] at h5
    norm_num at h5
  · rfl
  · norm_num at hcard'
    exact (hA.not_nine_dvd_card (hcard' ▸ (by decide : 9 ∣ 720))).elim


/-- The rank-one model crosses the literal core-to-star map; its kernel
is killed by the source central-kernel bound and the centerless SL₂ model. -/
theorem binary_borel_impossible
    {G : Type*} [Group G] [Finite G] {K R MH : Subgroup G} {n : ℕ}
    (hRK : R ≤ normalizer K) (hb : FullSieve.StarKernelBound K R)
    (hA : HasA5TwoResidual (starM K R MH))
    (hblock : ChapterC.IsL2EvenBlock K n)
    (hborel : IsRankOneBorel (starImage K R K) (starM K R MH)) : False := by
  obtain ⟨hn, _, F, _, _, hF, hPSL, hlinear⟩ := hblock
  obtain ⟨eSL⟩ := hlinear.quotient_iso
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hz : center (K ⧸ pCore 2 K) = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro b hb
    have hc := (centerCongr eSL ⟨b, hb⟩).property
    change eSL b ∈ center (Matrix.SpecialLinearGroup (Fin 2) F) at hc
    rw [Theory.PSL2.sl2_center_eq_bot] at hc
    exact eSL.injective ((mem_bot.mp hc).trans eSL.map_one.symm)
  let e : (K ⧸ pCore 2 K) ≃* starImage K R K :=
    MulEquiv.ofBijective (coreToStar hRK)
      ⟨(MonoidHom.ker_eq_bot_iff _).mp (bot_unique
        (hz ▸ FullSieve.coreToStar_ker_le_center_of_bound hRK hb)),
        coreToStar_surjective hRK⟩
  obtain ⟨E, _, _, hE, ⟨ePSL⟩⟩ := hPSL.of_mulEquiv e.symm
  obtain ⟨S, hS⟩ := hborel
  have hnS : ChapterF.Source.RankOneSylowFacts S :=
    ChapterF.Source.rankOneSylowFacts_of_equiv S ePSL
      (ChapterF.Source.rankOneSylowFacts_psl2 E n (by omega) hE _)
  let : Group.IsSolvable (normalizer (S : Set (starImage K R K))) := hnS.solvable
  have hsolv : Group.IsSolvable (starM K R MH) := by
    rw [hS]
    exact Group.isSolvable_of_surjective
      ((starImage K R K).subtype.subgroupMap_surjective _)
  let := hsolv
  exact hA.not_isSolvable

/-- The actual derived G₂(2) carrier has no factor of five. Its core model
therefore cannot admit the displayed residual in the star stabilizer. -/
theorem binaryG2_impossible
    {G : Type*} [Group G] [Finite G] {K R MH : Subgroup G}
    (hRK : R ≤ normalizer K)
    (hA : HasA5TwoResidual (starM K R MH))
    (hmodel : IsG2TwoBlock K) : False := by
  have h5star : 5 ∣ Nat.card (starImage K R K) :=
    hA.five_dvd_card.trans (Subgroup.card_dvd_of_le (starM_le K R MH))
  have h5core : 5 ∣ Nat.card (K ⧸ pCore 2 K) :=
    h5star.trans (card_dvd_of_surjective (coreToStar hRK) (coreToStar_surjective hRK))
  obtain ⟨e⟩ := hmodel.quotient_model
  rw [Nat.card_congr e.toEquiv,
    Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at h5core
  norm_num at h5core
private theorem perm_eq_one_of_pow_five {α : Type*} [Finite α]
    (hc : Nat.card α ≤ 4) (q : Equiv.Perm α) (hq : q ^ 5 = 1) : q = 1 := by
  apply orderOf_eq_one_iff.mp
  apply Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 5 24)
    (orderOf_dvd_of_pow_eq_one hq)
  apply (orderOf_dvd_natCard q).trans
  rw [Nat.card_perm]
  exact Nat.factorial_dvd_factorial hc

/-- A partition with fewer than five parts, each of size less than five,
has no stabilizer element of order five. -/
private theorem partition_not_five_dvd_card {n k : ℕ} {sizes : Fin k → ℕ}
    (p : Partition n k sizes) (hk : k ≤ 4) (hs : ∀ i, sizes i ≤ 4) :
    ¬ 5 ∣ Nat.card p.stabilizer := by
  classical
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro hd
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 5 hd
  have hqpow : q ^ 5 = 1 := hq ▸ pow_orderOf_eq_one q
  let : MulAction p.stabilizer (Set.range p.part) :=
    inferInstanceAs (MulAction (MulAction.stabilizer (Equiv.Perm (Fin n))
      (Set.range p.part)) (Set.range p.part))
  let ρ := MulAction.toPermHom p.stabilizer (Set.range p.part)
  have hρ : ρ q = 1 := perm_eq_one_of_pow_five
    ((Finite.card_range_le p.part).trans (by simpa using hk)) _ (by
      rw [← map_pow, hqpow, map_one])
  have hparts : ∀ i, (q : Equiv.Perm (Fin n)) • p.part i = p.part i := by
    intro i
    exact congrArg Subtype.val (Equiv.congr_fun hρ ⟨p.part i, ⟨i, rfl⟩⟩)
  have hpoint : ∀ i (x : Fin n), x ∈ p.part i → (q : Equiv.Perm (Fin n)) x = x := by
    intro i x hx
    have hinv : ∀ x, (q : Equiv.Perm (Fin n)) x ∈ p.part i ↔ x ∈ p.part i := by
      intro x
      conv_lhs => rw [← hparts i]
      exact Finset.smul_mem_smul_finset_iff (q : Equiv.Perm (Fin n))
    let σ : Equiv.Perm (p.part i) := (q : Equiv.Perm (Fin n)).subtypePerm hinv
    have hσpow : σ ^ 5 = 1 := by
      apply Equiv.ext
      intro a
      apply Subtype.ext
      change (((q : Equiv.Perm (Fin n)).subtypePerm hinv ^ 5) a : Fin n) = a
      rw [subtypePerm_apply_pow_of_mem]
      have hh : (q : Equiv.Perm (Fin n)) ^ 5 = 1 := congrArg Subtype.val hqpow
      rw [hh]
      rfl
    have hσ : σ = 1 := perm_eq_one_of_pow_five (by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe, p.card]
      exact hs i) _ hσpow
    exact congrArg Subtype.val (Equiv.congr_fun hσ ⟨x, hx⟩)
  have hone : q = 1 := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    obtain ⟨i, hi⟩ := p.cover x
    exact hpoint i x hi
  rw [hone, orderOf_one] at hq
  norm_num at hq

/-- Neither of the literal A₆ partition parabolics has order divisible by five. -/
private theorem a6Parabolic_not_five_dvd {A : Type*} [Group A] [Finite A]
    {P : Subgroup A} (hP : IsA6MaximalParabolic P) : ¬ 5 ∣ Nat.card P := by
  obtain ⟨e, hP⟩ := hP
  have hc : Nat.card ((P.map e.toMonoidHom).map (alternatingGroup (Fin 6)).subtype) =
      Nat.card P := by
    rw [Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
      Subgroup.card_map_of_injective e.injective]
  intro h5
  rcases hP with ⟨d, hd⟩ | ⟨d, hd⟩
  · rw [hd] at hc
    have h5d : 5 ∣ Nat.card d.stabilizer :=
      (hc.symm ▸ h5).trans (Subgroup.card_dvd_of_le (show
        alternatingGroup (Fin 6) ⊓ d.stabilizer ≤ d.stabilizer from inf_le_right))
    exact partition_not_five_dvd_card d (by decide)
      (by intro i; fin_cases i <;> norm_num) h5d
  · rw [hd] at hc
    have h5d : 5 ∣ Nat.card d.stabilizer :=
      (hc.symm ▸ h5).trans (Subgroup.card_dvd_of_le (show
        alternatingGroup (Fin 6) ⊓ d.stabilizer ≤ d.stabilizer from inf_le_right))
    exact partition_not_five_dvd_card d (by decide)
      (by intro i; fin_cases i <;> norm_num) h5d

private theorem a6_parabolic_impossible
    {G : Type*} [Group G] [Finite G] {K R MH : Subgroup G}
    (hA : HasA5TwoResidual (starM K R MH))
    (hP : IsA6MaximalParabolic ((starM K R MH).subgroupOf (starImage K R K))) :
    False := by
  apply a6Parabolic_not_five_dvd hP
  rw [Nat.card_congr (subgroupOfEquivOfLe (starM_le K R MH)).toEquiv]
  exact hA.five_dvd_card

universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
variable (d : Data T L V F W)

/-- Applying the literal four chi constructors at the fixed centralizer
leaves only the two A₇ block rows. The binary row uses the C.2.7 kernel bound
on the actual core-to-star map; the A₅ row uses strictness of the marked K-image. -/
theorem fixedComponent_chi_alternatingSeven (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (c27 : Conclusion KnownSimple.IsKnownSimple
      (d.fixedCentralizer u) Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u))
    (hA : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (_block : ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)))
    (_chi : ChapterC.IsChiBlock Lu)
    (cases : ChiAlternative Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)) :
    ChapterC.IsAlternatingBlock Lu 7 := by
  cases cases with
  | binary n block sylow borel =>
    exact (binary_borel_impossible (d.fixedCore_normalizes_component u h)
      c27.kernel.upper hA block borel).elim
  | five block sylow extension borel =>
    exact (d.fixedComponent_not_alternatingFiveBlock u h block).elim
  | sevenDihedral block radical extension => exact block
  | sevenElementary block radical extension => exact block

/-- In the literal alternating constructor of C.2.7(b), the star residual
and transposition centralizer force degree seven. -/
theorem fixedComponent_alternating_degree_seven (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (hA : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 8)
    (_block : ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)))
    (_model : ChapterC.IsAlternatingBlock Lu n)
    (action : TranspositionAction Lu (d.fixedCore u) n)
    (centralizer : starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) =
      starImage Lu (d.fixedCore u) Lu ⊓
        Subgroup.centralizer (starImage Lu (d.fixedCore u) (d.fixedCore u) :
          Set (StarQuotient Lu (d.fixedCore u)))) : n = 7 :=
  alternating_force_seven hA lower upper action centralizer

/-- In C.2.7(e), neither defined A₆ partition stabilizer can contain this
residual. The Sp₄(4) branch, with its original parabolic clause, survives. -/
theorem fixedComponent_rankTwo_symplecticFour (u : F.U) {Lu : Subgroup G}
    (_h : Nonquasisimple.Case d u Lu)
    (hA : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (_block : ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)))
    (cases : (ChapterC.IsAlternatingBlock Lu 6 ∧
      IsA6MaximalParabolic
        ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu))) ∨
      (ChapterC.IsSp4FourBlock Lu ∧
      IsSp4FourMaximalParabolic
        ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu)))) :
    ChapterC.IsSp4FourBlock Lu ∧
      IsSp4FourMaximalParabolic
        ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)).subgroupOf
          (starImage Lu (d.fixedCore u) Lu)) := by
  rcases cases with ⟨_, hP⟩ | hP
  · exact (a6_parabolic_impossible hA hP).elim
  · exact hP

/-- The literal binary G₂ constructor is impossible, using its derived
core carrier of order 6048. Its extension and parabolic clauses are retained. -/
theorem fixedComponent_not_binaryG2 (u : F.U) {Lu : Subgroup G}
    (h : Nonquasisimple.Case d u Lu)
    (hA : HasA5TwoResidual (starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u)))
    (_block : ChapterC.IsBlock (Lu.subgroupOf (d.fixedCentralizer u)))
    (model : IsG2TwoBlock Lu)
    (_extension : ∃ e : StarQuotient Lu (d.fixedCore u) ≃* Atlas.G2.Model (ZMod 2),
      IsG2MaximalParabolic
        ((starM Lu (d.fixedCore u) (F.H ⊓ d.fixedCentralizer u) ⊔
          starImage Lu (d.fixedCore u) (d.fixedCore u)).map e.toMonoidHom)) : False :=
  binaryG2_impossible (d.fixedCore_normalizes_component u h) hA model

end Data
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
