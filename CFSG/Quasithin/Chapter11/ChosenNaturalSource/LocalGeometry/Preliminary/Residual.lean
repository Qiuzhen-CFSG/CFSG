module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.QuadraticActors
public import Theory.SpecificGroups.PSL3.SplitPrimeActors
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.SymplecticCubicResidual
public import CFSG.Quasithin.ChapterA.Section03.OddPrime.SourceModels.G2CubicResidual

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Module
public import CFSG.Quasithin.Chapter12.Section02.Preliminaries.NormalizerSource
public import Theory.GroupTheory.PResidual.PrimeToPerfect
public import Theory.GroupTheory.PResidual.NormalizedImageContainment

/-!
# Exact prime residuals of the chosen normalizer

Work first in the literal quotient of M = N_G(L) by O₂(M), where the
image of the C-component is an ordinary component. The concrete natural
marking identifies that image with the full model. The rank-two field-actor
argument proves the residual equality for every prime dividing q²−1 in
Sp₄ and G₂, and every prime p > 3 dividing q−1 in SL₃.

The equality lifts across O₂(M), since both the perfect relative component
and the prime-to-p residual are two-perfect. This does not require O₂(L)
to be central or any central extension to split. In the SL₃ row the scalar
center is retained: its order divides three and is therefore prime to p.
The last exports place the original p-elements of M in L.

Source: Aschbacher--Smith 11.0.4(1--2), printed p.760, using A.3.18.
The additional order-three clause for SL₃ with even degree is separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

theorem normalizer_sqtk : IsSQTK KnownSimple.IsKnownSimple (normalizer (L : Set G)) :=
  S.source.simpleQTKE.twoLocal_sqtk (normalizer_maximal D S).1

theorem component_in_normalizer :
    (L.subgroupOf (normalizer (L : Set G))).IsCComponent :=
  S.source.toHypothesis1221.sylow_normalized_component D.sylow_normalizes_component
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))

omit D S in
/-- The intrinsic quotient of the relative component, with its original inclusion. -/
@[expose] def relativeComponentQuotientEquiv :
    ((L.subgroupOf (normalizer (L : Set G))) ⧸
      pCore 2 (L.subgroupOf (normalizer (L : Set G)))) ≃* (L ⧸ pCore 2 L) :=
  QuotientGroup.congr _ _ (subgroupOfEquivOfLe L.le_normalizer)
    (pCore_map_iso 2 (subgroupOfEquivOfLe L.le_normalizer))

omit D S in
private theorem perfect_twoPerfect {A : Type*} [Group A] [Finite A]
    [Group.IsPerfect A] : IsPPerfect 2 A := by
  intro N hN hQ
  let := hN
  apply eq_top_iff.mpr
  intro a _
  apply (QuotientGroup.eq_one_iff a).mp
  have hs : Subsingleton (A ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (A ⧸ N) hQ.isNilpotent
  exact Subsingleton.elim _ _

/-- Lift the odd residual through the literal ambient two-core quotient. -/
theorem relative_residual_of_twoCore_image {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (he : (L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G)))) =
      primeToResidual p ((normalizer (L : Set G)) ⧸
        pCore 2 (normalizer (L : Set G)))) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let M := normalizer (L : Set G)
  let K := L.subgroupOf M
  let q := QuotientGroup.mk' (pCore 2 M)
  let : K.Normal := normal_subgroupOf_of_le_normalizer le_rfl
  let : Group.IsPerfect K := (component_in_normalizer D S).perfect
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  have hm : (primeToResidual p M).map q = K.map q := by
    rw [map_primeToResidual_of_surjective p q (QuotientGroup.mk'_surjective _)]
    exact he.symm
  have hK : K = primeToResidual p M := le_antisymm
    (isPPerfect_le_of_map_le_of_kernel_normalizes q K _ perfect_twoPerfect hk
      le_normalizer_of_normal hm.symm.le)
    (isPPerfect_le_of_map_le_of_kernel_normalizes q _ K
      (isPPerfect_primeToResidual p 2 hp) hk le_normalizer_of_normal hm.le)
  have hh := congrArg (fun A : Subgroup M => A.map M.subtype) hK
  rw [map_subgroupOf_eq_of_le L.le_normalizer] at hh
  exact hh

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
open ChapterA.Section03.OddPrime.SourceModels
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

private theorem normalizer_quotient_sqtk :
    IsSQTK KnownSimple.IsKnownSimple
      ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G))) := by
  have h := normalizer_sqtk D S
  refine ⟨?_, h.isKGroup.quotient _⟩
  intro p hp ho
  let : Fact p.Prime := ⟨hp⟩
  exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
    (h.stronglyQuasithin p hp ho)

private theorem field_card_gt_two : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) S.nonbinary

private def imageEquiv {A : Type*} [Group A] (e : (L ⧸ pCore 2 L) ≃* A) :
    ((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) ≃* A :=
  (cComponentTwoCoreQuotientEquiv (component_in_normalizer D S)).symm.trans
    ((relativeComponentQuotientEquiv (L := L)).trans e)

private theorem image_component : IsComponent
    ((normalizer (L : Set G)) ⧸ pCore 2 (normalizer (L : Set G)))
    ((L.subgroupOf (normalizer (L : Set G))).map
      (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))) := by
  let := pCore_isNilpotent (p := 2) (G := normalizer (L : Set G))
  let := S.source.quasisimple
  let e := imageEquiv D S (MulEquiv.refl (L ⧸ pCore 2 L))
  let := IsQuasisimple.of_mulEquiv e.symm
  exact ⟨((component_in_normalizer D S).map_quotient _).subnormal, inferInstance⟩

omit D S in
private theorem center_eq_bot_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (hz : center B = ⊥) : center A = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hh : e x ∈ center B := (centerCongr e ⟨x,hx⟩).property
  rw [hz, mem_bot] at hh
  exact e.map_eq_one_iff.mp hh

/-- The Sp₄ cubic clause uses the actual C-component, allowing a noncentral two-core. -/
theorem sp4_cubic_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) :
    L = (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  have hz := center_eq_bot_of_equiv e
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
      (F := S.field.Carrier))
  let d := (QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot.trans e)
  apply relative_residual_of_twoCore_image D S (by decide : 3 ≠ 2)
  exact (SymplecticCubicResidual.component_eq_primeClosure_and_residual
    (normalizer_quotient_sqtk D S) (image_component D S)
    (hz.symm ▸ IsPGroup.of_bot) (field_card_gt_two D S) d).2

/-- The G₂ cubic clause includes both split and nonsplit cubic tori. -/
theorem g2_cubic_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    L = (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  have hz := center_eq_bot_of_equiv e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (field_card_gt_two D S))
  let d := (QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot.trans e)
  apply relative_residual_of_twoCore_image D S (by decide : 3 ≠ 2)
  exact (G2CubicResidual.component_eq_primeClosure_and_residual
    (normalizer_quotient_sqtk D S) (image_component D S)
    (hz.symm ▸ IsPGroup.of_bot) (field_card_gt_two D S) d).2

/-- The split-prime Sp₄ clause of 11.0.4(1), on the original normalizer. -/
theorem sp4_split_prime_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ 2 ^ S.field.degree - 1) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have ho : Odd p := by
    apply hp.odd_of_ne_two
    intro he
    subst p
    have hn := S.field.degree_pos
    have heven : Even (2 ^ S.field.degree) := even_two.pow_of_ne_zero (by omega)
    have hodd : Odd (2 ^ S.field.degree - 1) := Nat.odd_iff.mpr (by
      have hmod := Nat.even_iff.mp heven
      have hpos : 0 < 2 ^ S.field.degree := pow_pos (by decide) _
      omega)
    have hm := Nat.odd_iff.mp hodd
    have hm' := Nat.dvd_iff_mod_eq_zero.mp hd
    omega
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  have hz := center_eq_bot_of_equiv e
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
      (F := S.field.Carrier))
  let d := (QuotientGroup.quotientMulEquivOfEq hz).trans
    (QuotientGroup.quotientBot.trans e)
  apply relative_residual_of_twoCore_image D S (by intro hh; subst p; norm_num at ho)
  exact (SymplecticResidual.component_eq_primeClosure_and_residual
    (normalizer_quotient_sqtk D S) (image_component D S)
    (hz.symm ▸ IsPGroup.of_bot) S.nonbinary hp ho S.field.card_eq hd d).2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
open Theory.GroupAction.ComponentRankAction
open scoped MatrixGroups
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
include D S

private theorem prime_ne_two_of_square_dvd {p : ℕ}
    (hd : p ∣ (2 ^ S.field.degree) ^ 2 - 1) : p ≠ 2 := by
  intro he
  subst p
  have hn := S.field.degree_pos
  have hev : Even ((2 ^ S.field.degree) ^ 2) :=
    (even_two.pow_of_ne_zero (by omega : S.field.degree ≠ 0)).pow_of_ne_zero (by decide)
  have hm := Nat.even_iff.mp hev
  have hh := Nat.dvd_iff_mod_eq_zero.mp hd
  have hpos : 0 < (2 ^ S.field.degree) ^ 2 := pow_pos (pow_pos (by decide) _) _
  omega

/-- Every prime dividing q²−1 gives the exact Sp₄ residual in M = N_G(L). -/
theorem sp4_prime_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ (2 ^ S.field.degree) ^ 2 - 1) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 := prime_ne_two_of_square_dvd D S hd
  have ho := hp.odd_of_ne_two hp2
  have hdF : p ∣ Nat.card S.field.Carrier ^ 2 - 1 := S.field.card_eq ▸ hd
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  have hez := center_eq_bot_of_equiv e
    (Theory.SpecificGroups.SymplecticFour.EvenProjective.center_eq_bot
      (F := S.field.Carrier))
  let d := (QuotientGroup.quotientMulEquivOfEq hez).trans
    (QuotientGroup.quotientBot.trans e)
  have hz : Nat.Coprime p (Nat.card (center K)) := by
    rw [hez, card_bot]
    exact Nat.coprime_one_right p
  have hr : 2 ≤ primeRank p K := by
    rw [primeRank_congr p e]
    exact QuadraticActors.Sp4.rank_two hdF
  let := (image_component D S).2
  have hb := (normalizer_quotient_sqtk D S).stronglyQuasithin p hp ho
  apply relative_residual_of_twoCore_image D S hp2
  apply (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    (image_component D S) hz hr hb d ?_).2
  intro a ha k hk
  exact QuadraticActors.Sp4.primePower_actor_inner (field_card_gt_two D S) ho hdF
    (action _ d).range (inner_le_range _ d) (range_rank_le_two _ d hz hr hb) a ha ⟨k,hk⟩

/-- Every prime dividing q²−1 gives the exact G₂ residual in M = N_G(L). -/
theorem g2_prime_residual
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    {p : ℕ} (hp : p.Prime) (hd : p ∣ (2 ^ S.field.degree) ^ 2 - 1) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have hp2 := prime_ne_two_of_square_dvd D S hd
  have ho := hp.odd_of_ne_two hp2
  have hdF : p ∣ Nat.card S.field.Carrier ^ 2 - 1 := S.field.card_eq ▸ hd
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  have hez := center_eq_bot_of_equiv e
    (Atlas.G2.LieAutomorphismExtensions.model_center_eq_bot (field_card_gt_two D S))
  let d := (QuotientGroup.quotientMulEquivOfEq hez).trans
    (QuotientGroup.quotientBot.trans e)
  have hz : Nat.Coprime p (Nat.card (center K)) := by
    rw [hez, card_bot]
    exact Nat.coprime_one_right p
  have hr : 2 ≤ primeRank p K := by
    rw [primeRank_congr p e]
    exact QuadraticActors.G2.rank_two hdF
  let := (image_component D S).2
  have hb := (normalizer_quotient_sqtk D S).stronglyQuasithin p hp ho
  apply relative_residual_of_twoCore_image D S hp2
  apply (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    (image_component D S) hz hr hb d ?_).2
  intro a ha k hk
  exact QuadraticActors.G2.primePower_actor_inner (field_card_gt_two D S) hdF
    (action _ d).range (inner_le_range _ d) (range_rank_le_two _ d hz hr hb) a ha ⟨k,hk⟩

omit D S in
private def centerQuotientEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (A ⧸ center A) ≃* (B ⧸ center B) :=
  QuotientGroup.congr _ _ e (by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact (centerCongr e ⟨x,hx⟩).property
    · intro hy
      exact ⟨e.symm y,(centerCongr e.symm ⟨y,hy⟩).property,e.apply_symm_apply y⟩)

/-- The SL₃ prime-residual clause retains its full, possibly cubic, scalar center. -/
theorem sl3_prime_residual (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hd : p ∣ 2 ^ S.field.degree - 1) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  let : Fact p.Prime := ⟨hp⟩
  have ho := hp.odd_of_ne_two (by omega)
  have hdF : p ∣ Nat.card S.field.Carrier - 1 := S.field.card_eq ▸ hd
  let K := (L.subgroupOf (normalizer (L : Set G))).map
    (QuotientGroup.mk' (pCore 2 (normalizer (L : Set G))))
  let e := imageEquiv D S m.groupEquiv
  let d := centerQuotientEquiv e
  have hz : Nat.Coprime p (Nat.card (center K)) := by
    rw [Nat.card_congr (centerCongr e).toEquiv]
    apply Nat.Coprime.of_dvd_right (Matrix.SL3.card_center_dvd_three S.field.Carrier)
    exact hp.coprime_iff_not_dvd.mpr (fun h =>
      (by omega : p ≠ 3) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h))
  have hr := Matrix.PSL3.SplitPrimeRank.component_rank S.field.Carrier _ hz d (by omega) hdF
  let := (image_component D S).2
  have hb := (normalizer_quotient_sqtk D S).stronglyQuasithin p hp ho
  apply relative_residual_of_twoCore_image D S (by omega : p ≠ 2)
  apply (Theory.GroupAction.ComponentRankAction.component_eq_primeClosure_and_residual
    (image_component D S) hz hr hb d ?_).2
  intro a ha k hk
  exact Matrix.PSL3.SplitPrimeActors.inner_of_primePower S.field.degree_pos S.field.card_eq
    hp3 hdF (action _ d).range (inner_le_range _ d)
    (range_rank_le_two _ d hz hr hb) a ha ⟨k,hk⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Exactly the two prime ranges in source 11.0.4, with actual natural markings. -/
@[expose] def SourcePrime (p : ℕ) : Prop :=
  ((Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2))) ∨
    Nonempty (ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))) ∧
    p ∣ (2 ^ S.field.degree) ^ 2 - 1) ∨
  (Nonempty (ActionEquiv D.centralQuotientAction (linearNatural S.field 3)) ∧
    3 < p ∧ p ∣ 2 ^ S.field.degree - 1)

/-- Source 11.0.4(1--2), for the literal prime-to-p residual of N_G(L). -/
theorem prime_residual {p : ℕ} (hp : p.Prime) (hc : SourcePrime D S p) :
    L = (primeToResidual p (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype := by
  rcases hc with ⟨hm,hd⟩ | ⟨⟨m⟩,hp3,hd⟩
  · rcases hm with hm | hm
    · obtain ⟨m⟩ := hm
      exact sp4_prime_residual D S m hp hd
    · obtain ⟨m⟩ := hm
      exact g2_prime_residual D S m hp hd
  · exact sl3_prime_residual D S m hp hp3 hd

/-- The residual equality places the original p-elements of M in L. -/
theorem primePower_mem_component {p k : ℕ} (hp : p.Prime) (hc : SourcePrime D S p)
    {x : G} (hx : x ∈ normalizer (L : Set G)) (hpow : x ^ (p ^ k) = 1) : x ∈ L := by
  rw [prime_residual D S hp hc]
  exact ⟨⟨x,hx⟩, mem_primeToResidual_of_pow (Subtype.ext hpow), rfl⟩

/-- In particular, all order-p elements in the source prime ranges belong to L. -/
theorem orderPrime_mem_component {p : ℕ} (hp : p.Prime) (hc : SourcePrime D S p)
    {x : G} (hx : x ∈ normalizer (L : Set G)) (horder : orderOf x = p) : x ∈ L := by
  apply primePower_mem_component D S hp hc hx (k := 1)
  simpa only [pow_one, ← horder] using pow_orderOf_eq_one x

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary
