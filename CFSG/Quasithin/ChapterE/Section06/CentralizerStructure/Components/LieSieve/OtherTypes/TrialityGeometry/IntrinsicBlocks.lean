module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.Transport
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.TrialityGeometry.IntrinsicBlocks.Restrictions
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.Commutation.ShortTransport
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Arms
public import Theory.SpecificGroups.Triality.SubnormalRadicalActions.Central

/-!
# No chi-zero blocks in the intrinsic triality parabolics

The pulled-back component parabolic is isomorphic to the genuine root
parabolic. Every relatively subnormal chi-zero block therefore gives a
subnormal short subgroup of that root parabolic. Its external radical
commutators have square one by C.1.7. The node's root-action calculation
places all such two-perfect actors in the radical, so the candidate is both
a two-group and two-perfect and hence trivial, contradicting its nonzero
block module.

The arms calculation uses the PSL₂(q³) subsystem and the full central torus;
the central calculation uses the faithful action on the first cubic-field
layer. Both retain arbitrary radical factors. The latter also excludes the
order-three images at q = 2 without asserting perfectness of PSL₂(2).
The conditional interface is preserved, and `noChiZeroBlocks` discharges
its radical-action premise at both nodes. No automorphism-extension
hypothesis or ambient normality is used.

Source: Aschbacher–Smith C.1.7/C.1.12, pp.123–124, and the triality branch
of E.6.8, pp.247–248 (`refs/quasithin.pdf`); GLS3 §2.6.
The local structures are those of F.1.11–12, pp.262–264.
-/

@[expose] public section
noncomputable section

open Subgroup
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry

variable {G : Type*} [Group G] {L : Subgroup G} {P : Parameters}

/-- The exact isomorphism from the ambient component parabolic to its root model. -/
def componentParabolicEquiv (e : L ≃* Carrier P) (a : Node) :
    componentParabolic e a ≃* parabolic P a := by
  let A := (parabolic P a).comap e.toMonoidHom
  let f := e.toMonoidHom.subgroupComap (parabolic P a)
  have hf : Function.Bijective f :=
    ⟨fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h)),
      e.toMonoidHom.subgroupComap_surjective_of_surjective _ e.surjective⟩
  exact (A.equivMapOfInjective L.subtype L.subtype_injective).symm.trans
    (MulEquiv.ofBijective f hf)

namespace IntrinsicBlocks

/-- Root-action rigidity excludes every short subnormal subgroup. The
rigidity hypothesis must still be established separately at each node. -/
theorem not_short_of_radical_action (hp : P.prime = 2) (a : Node)
    (hrigid : ∀ X : Subgroup (parabolic P a), X.IsSubnormal → IsPPerfect 2 X →
      (∀ z ∈ ⁅(radical P a).subgroupOf (parabolic P a), X⁆,
        (z : parabolic P a) ^ 2 = 1) →
      X ≤ (radical P a).subgroupOf (parabolic P a))
    (X : Subgroup (parabolic P a)) (hs : X.IsSubnormal) : ¬ ChapterC.IsShort X := by
  intro hb
  have hle := hrigid X hs hb.twoPerfect
    (fun _ hz => short_radical_commutator_square P hp a X hs hb hz)
  have hXtwo : IsPGroup 2 X :=
    (RadicalCoordinates.radical_isPGroup P hp a).comap_subtype.to_le hle
  have hone := hb.twoPerfect.hom_eq_one_of_isPGroup hXtwo (MonoidHom.id X)
  apply hb.blockU_ne_bot
  apply eq_bot_iff.mpr
  intro x _
  exact mem_bot.mpr (DFunLike.congr_fun hone x)

end IntrinsicBlocks

/-- Transport relative subnormality and shortness to the actual root model,
then apply the explicit node-specific radical-action calculation. -/
theorem noChiZeroBlocks_of_radical_action (hp : P.prime = 2)
    (e : L ≃* Carrier P) (a : Node)
    (hrigid : ∀ X : Subgroup (parabolic P a), X.IsSubnormal → IsPPerfect 2 X →
      (∀ z ∈ ⁅(radical P a).subgroupOf (parabolic P a), X⁆,
        (z : parabolic P a) ^ 2 = 1) →
      X ≤ (radical P a).subgroupOf (parabolic P a)) :
    NoChiZeroBlocks (componentParabolic e a) := by
  intro B hB hs hb
  let E := componentParabolicEquiv e a
  let X := (B.subgroupOf (componentParabolic e a)).map E.toMonoidHom
  have hX : X.IsSubnormal := hs.map E.surjective
  have hshort : ChapterC.IsShort X :=
    hb.chi.short.of_mulEquiv ((subgroupOfEquivOfLe hB).symm.trans
      (E.subgroupMap (B.subgroupOf (componentParabolic e a))))
  exact IntrinsicBlocks.not_short_of_radical_action hp a hrigid X hX hshort

/-- Both genuine characteristic-two triality parabolics have no relatively
subnormal chi-zero block, including at q = 2. The root-action calculations
discharge every additional premise of the conditional transport theorem. -/
theorem noChiZeroBlocks (hp : P.prime = 2) (e : L ≃* Carrier P) (a : Node) :
    NoChiZeroBlocks (componentParabolic e a) := by
  apply noChiZeroBlocks_of_radical_action hp e a
  cases a with
  | arms => exact arms_le_radical_of_subnormal_of_isPPerfect P hp
  | central => exact central_subnormal_radical_le P hp

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.TrialityGeometry
