module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.TitsSourceLocals
public import Stellmacher.Recognition.Parrott.LocalGeneratorConstruction.Complete
public import Stellmacher.Recognition.Parrott.LocalNormalizer.Fusion
public import Stellmacher.Recognition.Parrott.FirstParabolicCoordinates
public import Theory.SpecificGroups.Tits.FirstParabolicCoordinateTransport

/-!
# An outside first-parabolic actor from intrinsic centralizer structure

The source14.2.3 centralization conclusion puts the given H inside C_G(z).
The original Sylow index five and the explicit lower bound |T|≥2048,
together with |C_G(z)|=10240, force equality. Empty faithful components
supply the local solvability premises for Parrott's normalized generator
construction. Its seven first-actor equations and Sylow conjugacy then
produce a frame and an outside actor on the original Sylow inside H.

The supplied frame may be replaced: the normalization is constructed using
the ambient hypotheses, rather than asserting that arbitrary coordinates
extend. Neither a second actor nor compatibility, an endpoint equivalence,
or generation of H is an input.

This is a conditional reduction. The source theorem still needs
`∃ z, zpowers z = centralInvolutions T ∧ ParrottCentralizerHypotheses z`,
owned by task `qt-e-quintic-intrinsic-centralizer`. In particular, the
nonabelian core structure is not inferred here from the elementary marked
quotient. Final assembly remains with the Weyl-actor task.

Source: Aschbacher--Smith F.1.11--12, pp.262--264, and14.2.20--21,
pp.988--989; Parrott (1972), §§3,5--6, pp.678--684.
-/

public noncomputable section
open Subgroup Stellmacher Theory.GroupTheory Tits.FirstParabolicCoordinates
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

/-- The original outside subgroup is the whole centralizer once the intrinsic
centralizer hypotheses and the source Sylow lower bound are established. -/
theorem source_first_parabolic_eq_centralizer_of_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlower : 2048 ≤ Nat.card (T : Subgroup G))
    (z : G) (hz : z ∈ centralInvolutions T)
    (hp : Recognition.ParrottCentralizerHypotheses z) :
    H = centralizer ({z} : Set G) := by
  have hHZ := (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hHC : H ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (hHZ hx z hz).symm
  apply eq_of_le_of_card_ge hHC
  have hc := ((T : Subgroup G).subgroupOf H).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hH.1.1.2).toEquiv] at hc
  change Nat.card (T : Subgroup G) * (T : Subgroup G).relIndex H = Nat.card H at hc
  rw [hi] at hc
  rw [(hp.card_and_solvable z).1]
  omega

/-- Construct an outside actor and a possibly replaced Sylow frame, retaining
all original ambient hypotheses. The remaining premise is the intrinsic
centralizer theorem, not an assumed frame, actor, or endpoint equivalence. -/
theorem source_weyl_actor_of_intrinsic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hlower : 2048 ≤ Nat.card (T : Subgroup G))
    (_d : SylowCoordinates (T.subtype hH.1.1.2 : Subgroup H))
    (hintrinsic : ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z) :
    ∃ d' : SylowCoordinates (T.subtype hH.1.1.2 : Subgroup H),
      Nonempty (WeylExtension d') := by
  obtain ⟨z, hz, hp⟩ := hintrinsic
  have hzT : z ∈ centralInvolutions T := hz ▸ mem_zpowers z
  have hHC := source_first_parabolic_eq_centralizer_of_intrinsic
    hG T hempty hM hu hmany hcard e H hH hi hlower z hzT hp
  subst H
  let : IsSimpleGroup G := hG.simple
  have hns : ¬ Group.IsSolvable G := fun hs =>
    hG.nonabelian (isMulCommutative_iff.mpr (IsSimpleGroup.comm_iff_isSolvable.mpr hs))
  have hsol := sylow_local_solvable_of_empty_faithful_of_solvable_centralizer
    hG T hempty z hzT (hp.card_and_solvable z).2
  let hlocal : Recognition.ParrottLocalInputs z := {
    derived_normalizer := parrott_derived_normalizer_of_sylow_local_solvability z hp hsol
    second_normalizer_solvable := fun a =>
      parrott_second_normalizer_solvable_of_sylow_local_solvability z a hsol }
  obtain ⟨a, ⟨n⟩⟩ := Recognition.parrott_normalizer_fusion_exists_of_local_inputs hns hp hlocal
  obtain ⟨⟨f, k⟩⟩ := n.exists_local_generators_of_local_inputs hns hlocal hp
  obtain ⟨d, ⟨r⟩⟩ := k.exists_first_weylExtension hp
  exact exists_weylExtension_of_sylow_conjugacy (T.subtype hH.1.1.2) d r

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
