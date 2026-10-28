module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.Basic
public import Theory.ElementaryAbelian.Quotient

/-!
# The reduced natural module for the actual group YT

Restrict the compatible natural action of M to YT, where Y is the residual
from 15.3.7. Its image is the whole orthogonal actor: the image of Y is the
two-residual, and the image of T is Sylow. Compatibility identifies the
kernel with the actual intrinsic centralizer of V. The first isomorphism
theorem then transfers the actor's trivial two-core to (YT)/C_(YT)(V).
The coordinates also give elementary abelianness, and normalization by M
restricts to normality in YT. Thus these are all clauses of B.2.11.

The residual-image calculation and the actor's trivial two-core are explicit
earlier inputs owned by the residual-action development. V ≤ T is the earlier
module containment. No abstract group-family tag is used, and no general
F.9.1 record is defined here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.2.11–14,
pp.77–78; 15.3.2(1) and 15.3.7, pp.1121–1122; F.9.1, pp.317–318.
-/

@[expose] public section

open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble
variable {G : Type*} [Group G]

/-- The actor map obtained by restricting the actual M-action. -/
noncomputable def restrictedActor {M V : Subgroup G} (d : NaturalOrthogonalAction M V)
    (K : Subgroup G) (hKM : K ≤ M) : K →* OrthogonalActor :=
  d.actor.comp (inclusion hKM)

/-- The kernel is exactly the centralizer inside the restricted group. -/
theorem restrictedActor_kernel {M V K : Subgroup G} (d : NaturalOrthogonalAction M V) (hKM : K ≤ M)
    (hVK : V ≤ K) :
    (restrictedActor d K hKM).ker = centralizer (V.subgroupOf K : Set K) := by
  ext k
  change d.actor (inclusion hKM k) = 1 ↔ _
  change inclusion hKM k ∈ d.actor.ker ↔ _
  rw [d.ker_actor]
  constructor
  · intro hk v hv
    apply Subtype.ext
    exact hk v hv
  · intro hk v hv
    exact congrArg Subtype.val (hk ⟨v, hVK hv⟩ hv)

/-- The residual image and the Sylow image generate the whole orthogonal actor. -/
theorem restrictedActor_onto [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    Function.Surjective (restrictedActor d (residualY M Mc ⊔ (T : Subgroup G))
      (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM)) := by
  apply MonoidHom.range_eq_top.mp
  rw [restrictedActor, MonoidHom.range_comp, Subgroup.inclusion_range,
    Subgroup.subgroupOf_sup (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM,
    Subgroup.map_sup, himage]
  exact twoResidualAmbient_top_sup_sylow ((T.subtype hTM).mapSurjective d.onto)

/-- The natural coordinates make V an elementary abelian two-group. -/
theorem vector_elementary {M V : Subgroup G} (d : NaturalOrthogonalAction M V) : IsElementaryAbelian 2 V := by
  let : IsElementaryAbelian 2 OrthogonalVector := {
    exponent_dvd_p := by
      rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      intro v
      rw [pow_two]
      ext i j
      change (v i).toAdd j + (v i).toAdd j = 0
      exact CharTwo.add_self_eq_zero _ }
  exact IsElementaryAbelian.of_surjective d.coordinates.symm.toMonoidHom
    d.coordinates.symm.surjective


/-- The actual residual is T-invariant by its relative normality in M. -/
theorem residualY_normalized [Finite G] (M Mc : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) :
    (T : Subgroup G) ≤ normalizer (residualY M Mc : Set G) :=
  hTM.trans ((normal_subgroupOf_iff_le_normalizer
    (Chapter14.SourcePreliminaries.sourceResidual_le M Mc)).mp (residualY_normal M Mc))

/-- The intrinsic two-residual of Y is all of Y, as required in F.9.1. -/
theorem residualY_perfect [Finite G] (M Mc : Subgroup G) : pResidual 2 (residualY M Mc) = ⊤ :=
  (pResidual_eq_top_iff 2 _).mpr (residualY_isPPerfect M Mc)

/-- The restricted natural action, including the conjugation compatibility equation. -/
noncomputable def residualSylowAction [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    NaturalOrthogonalAction (residualY M Mc ⊔ (T : Subgroup G)) V where
  normalizes := (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM).trans
    d.normalizes
  coordinates := d.coordinates
  actor := restrictedActor d _ (sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM)
  onto := restrictedActor_onto M Mc V T hTM d himage
  compatible := by
    intro k v
    exact d.compatible (inclusion (sup_le
      (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM) k) v

/-- Normality is inside YT; ambient normality of V is not asserted. -/
theorem vector_normal (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V) :
    (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G))).Normal :=
  normal_subgroupOf_of_le_normalizer
    ((sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM).trans d.normalizes)

/-- The actual centralizer quotient is isomorphic to the orthogonal actor. -/
noncomputable def residualSylowQuotientEquiv [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hVT : V ≤ T) :
    let := vector_normal M Mc V T hTM d
    ((residualY M Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      centralizer (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G)) :
        Set (residualY M Mc ⊔ (T : Subgroup G) : Subgroup G))) ≃* OrthogonalActor := by
  let := vector_normal M Mc V T hTM d
  let hKM := sup_le (Chapter14.SourcePreliminaries.sourceResidual_le M Mc) hTM
  let f := restrictedActor d (residualY M Mc ⊔ (T : Subgroup G)) hKM
  have hk := restrictedActor_kernel d hKM (hVT.trans le_sup_right)
  exact (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f (restrictedActor_onto M Mc V T hTM d himage))

/-- The two-reduced condition transported through the actual quotient isomorphism. -/
theorem quotient_core_eq_bot [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : pCore 2 OrthogonalActor = ⊥) (hVT : V ≤ T) :
    let := vector_normal M Mc V T hTM d
    pCore 2 ((residualY M Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
      centralizer (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G)) :
        Set (residualY M Mc ⊔ (T : Subgroup G) : Subgroup G))) = ⊥ := by
  let := vector_normal M Mc V T hTM d
  let e := residualSylowQuotientEquiv M Mc V T hTM d himage hVT
  apply (Subgroup.map_eq_bot_iff_of_injective (f := e.toMonoidHom) _ e.injective).mp
  rw [pCore_map_iso, hcore]

/-- Every clause of the source definition V ∈ R₂(YT), including the
intrinsic quotient by its centralizer. -/
theorem reduced_module [Finite G] (M Mc V : Subgroup G) (T : Sylow 2 G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M V)
    (himage : ((residualY M Mc).subgroupOf M).map d.actor =
      twoResidualAmbient (⊤ : Subgroup OrthogonalActor))
    (hcore : pCore 2 OrthogonalActor = ⊥) (hVT : V ≤ T) :
    let := vector_normal M Mc V T hTM d
    V ≤ residualY M Mc ⊔ (T : Subgroup G) ∧ IsElementaryAbelian 2 V ∧
      (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G))).Normal ∧
      pCore 2 ((residualY M Mc ⊔ (T : Subgroup G) : Subgroup G) ⧸
        centralizer (V.subgroupOf (residualY M Mc ⊔ (T : Subgroup G)) :
          Set (residualY M Mc ⊔ (T : Subgroup G) : Subgroup G))) = ⊥ :=
  ⟨hVT.trans le_sup_right, vector_elementary d, vector_normal M Mc V T hTM d,
    quotient_core_eq_bot M Mc V T hTM d himage hcore hVT⟩

end CFSG.Quasithin.Chapter15.Section03.FusionCore.CosetSetup.Preamble

end
