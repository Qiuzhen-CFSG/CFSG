module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Coordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Geometry
public import Theory.GroupAction.SubgroupQuotientFullAction
public import Theory.Representation.ElementaryAbelianAction

/-!
# The actual binary core quotient and its descended action

The subgroup U_alpha is central in the core. The radius-derived and square
bounds make core/U elementary abelian; its finiteness is inherited from the
finite vertex stabilizer. Conjugation descends through the specified local
projection because [core,Q_alpha] lies in U_alpha. Residual commutator
idempotence gives the full subspace commutator, and simplicity of SL3(2),
together with noncommutativity of the core, gives faithfulness.

`MidpointFacts` isolates the remaining geometric calculation: the actual
midpoint image is elementary of order four, and its commutator preimage
modulo U_alpha has index at most four in the core. These group facts imply
an offender for the constructed action. This module does not construct the
midpoint facts from the small-intersection hypothesis; the final constructor
remains conditional on that witness.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), printed p.842,
and (4.6.9)--(4.6.11), printed pp.908--909.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
open Representation Representation.BinaryOffender
universe u
variable {M : Type u} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

/-- The finite binary core quotient with its literal descended conjugation action. -/
structure QuotientAction (source : LocalSource L R) where
  Space : Type u
  [addCommGroup : AddCommGroup Space]
  [module : Module (ZMod 2) Space]
  [finite : Finite Space]
  representation : Representation (ZMod 2) SL Space
  projection : core R (alpha R) →* Multiplicative Space
  onto : Function.Surjective projection
  kernel : projection.ker = (U R (alpha R)).subgroupOf (core R (alpha R))
  action : ∀ (m : M) (x y : core R (alpha R)),
    (y : FreeAmalgam R) = embedM R m * (x : FreeAmalgam R) * (embedM R m)⁻¹ →
    (projection y).toAdd = representation (source.projection m) (projection x).toAdd
attribute [instance] QuotientAction.addCommGroup QuotientAction.module QuotientAction.finite

include source common radius in
/-- Construct the elementary quotient and descend conjugation to the actual SL3(2). -/
theorem exists_quotientAction : Nonempty (QuotientAction source) := by
  let C := core R (alpha R)
  let N := (U R (alpha R)).subgroupOf C
  have hNC : N ≤ center C := by
    intro x hx
    obtain ⟨y, hy, he⟩ := U_le_center_core source geometry common hx
    exact (Subtype.ext he : y = x) ▸ hy
  let : N.Normal := ⟨by
    intro x hx g
    simpa only [(mem_center_iff.mp (hNC hx) g), mul_inv_cancel_right] using hx⟩
  let D := C ⧸ N
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (Subgroup.inclusion hC) (Subgroup.inclusion_injective hC)
  have hderived : _root_.commutator C ≤ N := by
    intro x hx
    have hh := mem_map_of_mem C.subtype hx
    rw [map_subtype_commutator] at hh
    exact core_derived_le_U geometry radius (alpha R) rfl hh
  let : IsMulCommutative D := Normal.quotient_commutative_iff_commutator_le.mpr hderived
  let : IsElementaryAbelian 2 D := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact core_square_mem_U geometry radius (alpha R) rfl y }
  let P := Mbar R
  have hPC : P ≤ normalizer C := core_normalized
  have hPN : P ≤ normalizer (U R (alpha R)) := common.natural.normalized
  obtain ⟨a, ha⟩ := exists_quotient_conjugation_action P C (U R (alpha R)) hPC hPN inferInstance
  let i : M →* P := (embedM R).rangeRestrict
  let aM : M →* MulAut D := a.comp i
  have hkill : source.projection.ker ≤ aM.ker := by
    intro m hm
    have hmQ : embedM R m ∈ Q R (alpha R) := by
      rw [Q_alpha R source.two_group source.core_le]
      exact mem_map_of_mem _ (source.projection_kernel ▸ hm)
    have hk := quotient_conjugation_action_kills_commutator_layer P C (U R (alpha R))
      (Q R (alpha R)) inferInstance hPC
      (core_commutator_Q_le_U source geometry common radius (alpha R) (beta R) rfl
        (base_adjacent R)) a ha
    exact hk hmQ
  let aSL : SL →* MulAut D := source.projection.liftOfSurjective
    source.projection_surjective ⟨aM, hkill⟩
  have haSL (m : M) : aSL (source.projection m) = aM m := by
    exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let : MulDistribMulAction SL D := MulDistribMulAction.compHom D aSL
  let ρ : Representation (ZMod 2) SL (Additive D) := ofElementaryAbelianAction
  let q : C →* Multiplicative (Additive D) :=
    (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom.comp (QuotientGroup.mk' N)
  refine ⟨{
    Space := Additive D
    representation := ρ
    projection := q
    onto := (MulEquiv.multiplicativeAdditive (H := D)).symm.surjective.comp (QuotientGroup.mk'_surjective N)
    kernel := ?_
    action := ?_ }⟩
  · exact (MonoidHom.ker_comp_of_injective (QuotientGroup.mk' N)
      (MulEquiv.multiplicativeAdditive (H := D)).symm.toMonoidHom
      (MulEquiv.multiplicativeAdditive (H := D)).symm.injective).trans
        (QuotientGroup.ker_mk' N)
  · intro m x y hy
    change QuotientGroup.mk' N y = aSL (source.projection m) (QuotientGroup.mk' N x)
    rw [haSL, show aM m = a (i m) from rfl, ha]
    congr 1
    exact Subtype.ext hy

variable {source geometry} (d : QuotientAction source)

/-- Idempotence of the actual group commutator descends to linear fullness. -/
theorem QuotientAction.full : subspaceCommutator d.representation ⊤ ⊤ = ⊤ := by
  let C := core R (alpha R)
  let W := subspaceCommutator d.representation ⊤ ⊤
  let H : Subgroup C := W.toAddSubgroup.toSubgroup.comap d.projection
  have hCH : C ≤ H.map C.subtype := by
    change core R (alpha R) ≤ H.map C.subtype
    rw [← Flags.core_idempotent source (alpha R) rfl, commutator_comm]
    apply commutator_le.mpr
    intro l hl x hx
    have hlM : l ∈ Mbar R := by
      rw [← stabilizer_m_base R]
      exact map_subtype_le _ hl
    obtain ⟨m, rfl⟩ := hlM
    let z : C := coreAction (R := R) m ⟨x, hx⟩ * (⟨x, hx⟩ : C)⁻¹
    refine ⟨z, ?_, rfl⟩
    change (d.projection z).toAdd ∈ W
    have he : (d.projection z).toAdd =
        d.representation (source.projection m) (d.projection ⟨x, hx⟩).toAdd -
          (d.projection ⟨x, hx⟩).toAdd := by
      change (d.projection (coreAction (R := R) m ⟨x, hx⟩ * (⟨x, hx⟩ : C)⁻¹)).toAdd = _
      rw [map_mul, map_inv]
      simp only [toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
      rw [d.action m ⟨x, hx⟩ _ rfl]
    rw [he]
    exact Submodule.subset_span ⟨source.projection m, mem_top _,
      (d.projection ⟨x, hx⟩).toAdd, Submodule.mem_top, rfl⟩
  apply top_unique
  intro v _
  obtain ⟨x, hx⟩ := d.onto (Multiplicative.ofAdd v)
  obtain ⟨y, hy, he⟩ := hCH x.property
  have he' : y = x := Subtype.ext he
  subst y
  change (d.projection x).toAdd ∈ W at hy
  rw [hx] at hy
  exact hy

include common radius in
/-- Simplicity makes the nontrivial fully moving action faithful. -/
theorem QuotientAction.faithful : Function.Injective d.representation := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  apply d.representation.ker_eq_bot_iff.mp
  rcases (inferInstance : d.representation.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  exfalso
  have hfixed : (⊤ : Submodule (ZMod 2) d.Space) ≤ fixedSpace d.representation ⊤ := by
    intro v _ g
    have hg : d.representation g.val = 1 := by
      change g.val ∈ d.representation.ker
      rw [hk]
      exact mem_top _
    change d.representation g.val v = v
    rw [hg]
    rfl
  have hzero := (subspaceCommutator_eq_bot_iff d.representation ⊤ ⊤).mpr hfixed
  rw [d.full] at hzero
  have hCU : core R (alpha R) ≤ U R (alpha R) := by
    intro x hx
    have hq : d.projection ⟨x, hx⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      exact hzero.le Submodule.mem_top
    have hmem : (⟨x, hx⟩ : core R (alpha R)) ∈ d.projection.ker := hq
    rwa [d.kernel] at hmem
  apply core_not_commutative source geometry common radius
  apply le_centralizer_iff_isMulCommutative.mp
  intro x hx y hy
  obtain ⟨z, hz, he⟩ := U_le_center_core source geometry common (hCU hx)
  have h := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)
  change (z : FreeAmalgam R) = x at he
  simpa only [coe_mul, he] using h

/-- The image of the actual midpoint radius subgroup in the specified quotient. -/
noncomputable def midpointActor (s : CriticalSegment geometry) : Subgroup SL :=
  ((V R s.middle).comap (embedM R)).map source.projection

/-- Group-theoretic data still required from the small-intersection geometry.
The index is computed on core/U, not on the larger quotient V/Z. -/
structure MidpointFacts (s : CriticalSegment geometry) : Prop where
  locality : V R s.middle ≤ Mbar R
  elementary : IsElementaryAbelian 2 (midpointActor (source := source) s)
  card : Nat.card (midpointActor (source := source) s) = 4
  fixed_index : (commutatorPreimage (core R (alpha R)) (V R s.middle)
    (U R (alpha R))).relIndex (core R (alpha R)) ≤ 4

include common in
/-- A geometric fixed-preimage bound gives an offender on the actual action. -/
theorem QuotientAction.offending_of_midpoint (s : CriticalSegment geometry)
    (h : MidpointFacts (source := source) s) : IsFFModule d.representation := by
  let C := core R (alpha R)
  let A := midpointActor (source := source) s
  let K := commutatorPreimage C (V R s.middle) (U R (alpha R))
  let W := fixedSpace d.representation A
  let H : Subgroup (Multiplicative d.Space) := W.toAddSubgroup.toSubgroup
  let F : Subgroup C := H.comap d.projection
  have hC : C ≤ stabilizer R (alpha R) := (core_le_Q source).trans (fun _ hx => hx.1)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite C := Finite.of_injective (Subgroup.inclusion hC) (Subgroup.inclusion_injective hC)
  have hKU : ⁅K, V R s.middle⁆ ≤ U R (alpha R) :=
    commutator_commutatorPreimage_le _ _ _
      (hC.trans (by rw [alpha, stabilizer_m_base]; exact common.natural.normalized))
  have hKF : K.subgroupOf C ≤ F := by
    intro x hx
    change ∀ g : A, d.representation g.val (d.projection x).toAdd = (d.projection x).toAdd
    intro g
    obtain ⟨m, hm, hmg⟩ := g.property
    change embedM R m ∈ V R s.middle at hm
    rw [← hmg]
    let y := coreAction (R := R) m x
    have hz : y * x⁻¹ ∈ d.projection.ker := by
      rw [d.kernel]
      change ⁅embedM R m, (x : FreeAmalgam R)⁆ ∈ U R (alpha R)
      rw [commutator_comm] at hKU
      exact hKU (commutator_mem_commutator hm hx)
    have hq : d.projection y = d.projection x := by
      change d.projection (y * x⁻¹) = 1 at hz
      rwa [map_mul, map_inv, mul_inv_eq_one] at hz
    rw [← d.action m x y rfl, hq]
  have hind : F.index ≤ 4 :=
    (Subgroup.index_antitone hKF).trans
      h.fixed_index
  have hpow : 2 ^ fixedCodim d.representation A ≤ 4 := by
    rw [Subgroup.index_comap_of_surjective _ d.onto, AddSubgroup.index_toSubgroup] at hind
    change Nat.card (d.Space ⧸ W) ≤ 4 at hind
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hind
    exact hind
  refine ⟨A, ⟨?_, h.elementary⟩, ?_⟩
  · intro he
    have hc := h.card
    change Nat.card A = 4 at hc
    rw [he, Subgroup.card_bot] at hc
    omega
  · have hdim : fixedCodim d.representation A ≤ 2 :=
      (pow_le_pow_iff_right₀ (by decide : 1 < (2 : ℕ))).mp hpow
    simpa only [rank, show Nat.card A = 4 from h.card, show Nat.log 2 4 = 2 by decide]
      using hdim

include common radius in
/-- Assembly is conditional precisely on the unconstructed midpoint facts. -/
theorem exists_coreModule_of_midpoint (s : CriticalSegment geometry)
    (h : MidpointFacts (source := source) s) : Nonempty (CoreModule source) := by
  obtain ⟨d⟩ := exists_quotientAction source geometry common radius
  exact ⟨{
    Space := d.Space
    representation := d.representation
    projection := d.projection
    onto := d.onto
    kernel := d.kernel
    action := d.action
    faithful := d.faithful common radius
    full := d.full
    offending := d.offending_of_midpoint common s h }⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
