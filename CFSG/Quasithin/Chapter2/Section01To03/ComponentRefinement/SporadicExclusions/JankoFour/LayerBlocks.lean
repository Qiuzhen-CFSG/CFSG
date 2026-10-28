module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.QuotientBlocks
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SporadicExclusions.JankoFour.Contracts
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SimplePowerExtension

/-!
# Block exclusions in Mathieu layers

Suppose K has a normal two-subgroup N, a normal subgroup D of K/N actually
isomorphic to M24^n, and two-group quotient (K/N)/D. Pulling D back to K
gives a normal subgroup P with two-group quotient and a surjection onto
M24^n whose kernel is N restricted to P. These maps retain both extension
kernels and require no splitting or positive lower bound on n.

For a short subnormal subgroup B, two-perfection kills its image in K/P.
The simple-power theorem then uses relative subnormality in P to make each
coordinate image trivial or surjective. It identifies the product kernel
with O₂(B) and a nontrivial coordinate with B/O₂(B). Thus that quotient is
actually M24, whose order excludes every chi-zero type. When n = 0, the
same argument rules out a short subgroup because its quotient is nontrivial.

The final construction supplies the block-obstruction field of the proposed
J4 local cover. Constructing the local family remains a separate obligation.
Source: Aschbacher–Smith C.1.7, C.1.12 (printed pp.123–124), applied to the
J4 exclusion in the proof of 2.3.9(7), printed p.526.
-/

public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

open Subgroup ChapterC Sporadic.Mathieu

private theorem mathieu_center_eq_bot : center M24 = ⊥ := by
  let := m24_isSimpleGroup
  rcases (inferInstance : (center M24).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · let := center_eq_top_iff.mp h
    have hp := (Group.is_simple_iff_prime_card (α := M24)).mp m24_isSimpleGroup
    rw [m24_order] at hp
    norm_num at hp

private theorem mathieu_not_twoGroup : ¬ IsPGroup 2 M24 := by
  intro h
  obtain ⟨n, hn⟩ := h.exists_card_dvd_pow
  rw [m24_order] at hn
  have hd : 3 ∣ 2 ^ n := (by decide : 3 ∣ 244823040).trans hn
  have := Nat.prime_three.dvd_of_dvd_pow hd
  norm_num at this

variable {K : Type*} [Group K]

/-- A block in a Mathieu two-layer extension has actual core quotient M24.
The hypotheses allow the empty direct power and nonsplit extensions. -/
theorem quotient_equiv_m24_of_mathieuTwoLayer
    (hK : HasMathieuTwoLayer K) (B : Subgroup K) (hB : IsBlock B) :
    Nonempty ((B ⧸ pCore 2 B) ≃* M24) := by
  let := m24_isSimpleGroup
  obtain ⟨N, hN, hNtwo, D, hD, n, ⟨e⟩, houter⟩ := hK
  let := hN
  let := hD
  let q := (QuotientGroup.mk' D).comp (QuotientGroup.mk' N)
  have hq : Function.Surjective q :=
    (QuotientGroup.mk'_surjective D).comp (QuotientGroup.mk'_surjective N)
  let P := q.ker
  have hP : IsPGroup 2 (K ⧸ P) :=
    houter.of_equiv (QuotientGroup.quotientKerEquivOfSurjective q hq).symm
  let fD : P →* D := ((QuotientGroup.mk' N).comp P.subtype).codRestrict D (by
    intro x
    exact (QuotientGroup.eq_one_iff _).mp x.property)
  have hfD : Function.Surjective fD := by
    intro d
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective N d.val
    refine ⟨⟨k, ?_⟩, Subtype.ext hk⟩
    change QuotientGroup.mk' D (QuotientGroup.mk' N k) = 1
    rw [hk]
    exact (QuotientGroup.eq_one_iff _).mpr d.property
  have hfDker : fD.ker = N.subgroupOf P := by
    ext x
    change fD x = 1 ↔ x.val ∈ N
    rw [← Subtype.val_inj]
    exact QuotientGroup.eq_one_iff x.val
  let f := e.toMonoidHom.comp fD
  have hfker : IsPGroup 2 f.ker := by
    rw [show f.ker = fD.ker from MonoidHom.ker_mulEquiv_comp fD e, hfDker]
    exact hNtwo.comap_of_injective P.subtype Subtype.val_injective
  exact hB.quotient_equiv_of_simple_power mathieu_center_eq_bot mathieu_not_twoGroup
    P hP f (e.surjective.comp hfD) hfker

/-- Every relatively subnormal subgroup of a finite Mathieu two-layer
extension fails to be a chi-zero block. -/
theorem not_chiZero_subnormal_of_mathieuTwoLayer [Finite K]
    (hK : HasMathieuTwoLayer K) (B : Subgroup K) (hB : B.IsSubnormal) :
    ¬ IsChiZeroBlock B := by
  intro hchi
  obtain ⟨e⟩ := quotient_equiv_m24_of_mathieuTwoLayer hK B
    ⟨inferInstance, hchi.chi.short, hB⟩
  exact not_chiZero_of_quotient_card_m24
    ((Nat.card_congr e.toEquiv).trans m24_order) hchi

variable {G : Type*} [Group G]

/-- This excludes all of the subnormal blocks tested by the actual local
obstruction, including those moved by the specified J(S). -/
theorem blockObstruction_of_mathieuTwoLayer (M S X : Subgroup G)
    (hX : HasMathieuTwoLayer X) : BlockObstruction M S X := by
  intro B hB _
  let : Finite X := hB.1.finite
  exact (not_chiZero_subnormal_of_mathieuTwoLayer hX B hB.1.subnormal hB.2).elim

/-- Discharge the block calculation for a Mathieu local family. The parent
J4 argument still constructs the family with the supplied S and proves generation. -/
def MathieuLocalCover.toCentralizerBlockCover {L S : Subgroup G} {z : G}
    (c : MathieuLocalCover L S z) (M : Subgroup G) : CentralizerBlockCover L M S z where
  locals := c.locals
  generated := c.generated
  within := c.within
  even := c.even
  obstruction := fun X hX => blockObstruction_of_mathieuTwoLayer M S X (c.layers X hX)

end CFSG.Quasithin.Chapter2.ComponentRefinement.JankoFour

end
