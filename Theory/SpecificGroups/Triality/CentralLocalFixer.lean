module
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.LocalKernel
public import Theory.SpecificGroups.Triality.BinaryCentralResidual
import all Theory.SpecificGroups.Triality.BinaryCentralResidual
public import Theory.GroupAction.PerfectCentralQuotient

/-!
# Restriction to the central triality local subgroup

The central-node local residual has trivial center. Its center maps trivially
into the centerless rank-one quotient, hence lies in the radical and in the
unipotent center. The central Levi cubic moves every nonidentity highest-root
element. The proved local-action kernel theorem then makes an involutory
pointwise fixer conjugation by a local central element, so it is trivial.

Faithful descent to a perfect central quotient transfers the result to the
actual marked subgroup of every perfect cover. This is the central-node row
used in Aschbacher–Smith 10.2.9, pp.750–751, and F.1.12.

The private import intentionally shares the internal cubic root calculation
with BinaryCentralResidual; no private name occurs in the public interface.
-/

open Subgroup
open Triality.Standard Triality.Standard.Parabolics
open Triality.Standard.RadicalCoordinates Triality.Standard.RadicalCoordinates.Centers
open Triality.Standard.ParabolicOuterTwo
open Triality.Standard.Parabolics.BinaryCentralResidual

namespace Triality.Standard.Parabolics

private theorem central_local_quotient_center (P : Parameters) (hp : P.prime = 2) :
    center (localFactor P .central ⧸ pCore 2 (localFactor P .central)) = ⊥ := by
  let : CharP (GaloisField P.prime P.exponent) 2 := hp ▸ inferInstance
  let e := (localFactorCentralQuotientEquivPSL2 P hp).trans
    (Theory.PSL2.sl2QuotientEquiv _).symm
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [Subgroup.center_map_equiv, Subgroup.map_bot, Theory.PSL2.sl2_center_eq_bot]

private theorem cubic_mem_central_local (P : Parameters) (hp : P.prime = 2) :
    toCarrier P (cubicElementary P hp) ∈ localFactor P .central := by
  apply levi_le_localFactor P hp .central
  refine ⟨cubicElementary P hp, ?_, rfl⟩
  unfold cubicElementary
  exact ((pinnedRankOneMaps P hp).range_centralFixedEmbedding.le ⟨_,rfl⟩).1

/-- The central-node local residual has trivial center, also at q=2. -/
public theorem central_local_center_eq_bot (P : Parameters) (hp : P.prime = 2) :
    center (localFactor P .central) = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro z hz
  let q := QuotientGroup.mk' (pCore 2 (localFactor P .central))
  have hqz : q z ∈ center (localFactor P .central ⧸ pCore 2 (localFactor P .central)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (localFactor P .central)) y
    exact (map_mul q x z).symm.trans
      ((congrArg q (mem_center_iff.mp hz x)).trans (map_mul q z x))
  rw [central_local_quotient_center P hp, mem_bot] at hqz
  have hcore : z ∈ pCore 2 (localFactor P .central) := (QuotientGroup.eq_one_iff z).mp hqz
  have hrad : z.val ∈ radical P .central := by
    rw [← localFactor_twoCore_map P hp .central]
    exact ⟨z, hcore, rfl⟩
  have hradU : radical P .central ≤ unipotent P := by
    rw [radical_eq_descendedRootSubgroup P hp .central]
    exact descendSubgroup_mono P (rootSubgroup_le_positiveSubgroup P hp .central)
  have hUloc : unipotent P ≤ localFactor P .central := by
    simpa only [coe_unipotentSylow] using unipotentSylow_le_localFactor P hp .central
  have hzU : (⟨z.val, hradU hrad⟩ : unipotent P) ∈ center (unipotent P) := by
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (congrArg (fun y : localFactor P .central => y.val)
      (mem_center_iff.mp hz ⟨x.val, hUloc x.property⟩))
  have hzH : z.val ∈ highestRoot P := by
    rw [← embedded_center_unipotent P hp]
    exact ⟨⟨z.val, hradU hrad⟩, hzU, rfl⟩
  rw [← highestHom_range P hp] at hzH
  obtain ⟨t, ht⟩ := hzH
  change highestHom P hp t = z.val at ht
  have hc : Commute (toCarrier P (cubicElementary P hp)) z.val :=
    congrArg Subtype.val (mem_center_iff.mp hz
      ⟨toCarrier P (cubicElementary P hp), cubic_mem_central_local P hp⟩)
  have ht0 := highest_commuting_cubic P hp t.toAdd (commute_congr rfl ht.symm hc)
  have ht1 : t = 1 := congrArg Multiplicative.ofAdd ht0
  apply Subtype.ext
  exact ht.symm.trans ((congrArg (highestHom P hp) ht1).trans (map_one _))

/-- An involution fixing the actual central local residual fixes the carrier. -/
public theorem central_local_involutory_fixer_eq_one (n : ℕ) (hn : 0 < n)
    (a : MulAut (BinaryCarrier n hn)) (ha : a ^ 2 = 1)
    (hfix : ∀ x ∈ localFactor (binaryParameters n hn) .central, a x = x) : a = 1 := by
  let P := binaryParameters n hn
  have hmap : (localFactor P .central).map a.toMonoidHom = localFactor P .central := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      change a x ∈ localFactor P .central
      rwa [hfix x hx]
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  let σ : localStabilizer P .central := ⟨a, hmap⟩
  have hσ : σ ^ (2 ^ 1) = 1 := Subtype.ext (by simpa using ha)
  have hres : localRestriction P .central σ = 1 := by
    ext x
    exact hfix x.val x.property
  have hquo : localQuotientAction P .central σ = 1 := by
    change Subgroup.quotientAut _ (localRestriction P .central σ) = 1
    rw [hres, map_one]
  obtain ⟨g, hg⟩ := local_inner_twoElement n hn .central σ 1 hσ
    (by rw [hquo]; exact one_mem _)
  have hag : MulAut.conj g.val = a := congrArg Subtype.val hg
  have hgz : g ∈ center (localFactor P .central) := by
    apply mem_center_iff.mpr
    intro x
    apply Subtype.ext
    have hh := hfix x.val x.property
    rw [← hag, MulAut.conj_apply] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  rw [central_local_center_eq_bot P rfl, mem_bot] at hgz
  rw [hgz] at hag
  exact hag.symm.trans (map_one MulAut.conj)

/-- The actual central local marking detects involutions on any perfect cover. -/
public theorem perfect_cover_central_local_involutory_fixer_eq_one
    {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]
    (n : ℕ) (hn : 0 < n) (e : (K ⧸ center K) ≃* BinaryCarrier n hn)
    (B : Subgroup K)
    (hB : B.map (e.toMonoidHom.comp (QuotientGroup.mk' (center K))) =
      localFactor (binaryParameters n hn) .central)
    (a : MulAut K) (ha : a ^ 2 = 1) (hfix : ∀ b ∈ B, a b = b) : a = 1 := by
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply central_local_involutory_fixer_eq_one n hn
  · rw [← map_pow, ha, map_one]
  · intro x hx
    rw [← hB] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    change MulAut.centralQuotientAction e a
      (e (QuotientGroup.mk' (center K) b)) = e (QuotientGroup.mk' (center K) b)
    rw [MulAut.centralQuotientAction_apply, hfix b hb]

end Triality.Standard.Parabolics
