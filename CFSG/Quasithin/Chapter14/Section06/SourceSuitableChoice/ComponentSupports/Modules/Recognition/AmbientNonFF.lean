module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.LinearThreeNonFF
public import CFSG.Quasithin.ChapterB.Section01.ComponentNormalization.Source
public import Theory.Representation.BinaryOffender.AmbientNonFF
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentCriticalPair.TwoComponents.Selection

/-!
# Ambient FF exclusion and original critical endpoint in the exchanged branch

Every best offender normalizes the actual component by B.1.5(4). Its
restriction to the selected natural--dual orbit is trivial because that
image is non-FF. Faithfulness on the orbit forces component centralization;
Sylow conjugation and generalized Fitting self-centralization then exclude
ambient offenders. The proved terminal generation theorem supplies the
residual premise on the original U/Z.

The exclusion transports to any already chosen original action. It rules
out involution transvections and discharges the literal critical-endpoint
selection premise, including the strict rank inequality in14.6.24(b).
This does not identify the seed orbit with the full component support:
the remaining F.9.18 section/quotient exclusions and suitable-vector
assembly belong to qt-e-suitable-component-supports. Original14.6.18
remains hsolv, with final discharge owned by qt-e-14625-source.

Source: Aschbacher--Smith B.1.5(4),14.6.22--24, pp.71,1038--1039.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Chapter13.Section08.CriticalGeometry.Reorientation
open Chapter13.Section08.Components.SourceModels
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (hsolv : ∀ J ∈ Chapter1.HOver G (T : Set G), Group.IsSolvable J → J ≤ M)
include hG hempty hM hunique hmany hcard e hab hsolv


/-- A moved natural seed with the source quadratic bound excludes FF
on the entire original U/Z when the component orbit and T generate H. -/
theorem source_l3_ambient_not_ff
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hgen : conjugateSpanBy K (T : Subgroup G) ⊔ (T : Subgroup G) = H)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation (actorImage H K)
      (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
    (b : ChapterB.QuasisimpleSource.ActionEquiv
      (centralQuotientRepresentation a.representation (actorImage H K) I hI.isIrrPlus.choose)
      (ChapterB.QuasisimpleSource.linearNatural ChapterB.QuasisimpleSource.BinaryField.two 3))
    (hsmall : quadraticRatio (invariantSubspace a.representation (actorImage H K)
      (orbitSpan a.representation
        (actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))) I)
      (orbitSpan_component_invariant a.representation hI.normalizes hI.isIrrPlus)).toRepresentation ≤ 2) :
    ¬ IsFFModule a.representation := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    H hH K hKH hK
  let : IsQuasisimple (actorImage H K) := hD.2
  let j : actorImage H K ≃* BinaryLinearThree.Group := b.groupEquiv
  have hz : center (actorImage H K) = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center BinaryLinearThree.Group at hh
    rw [show center BinaryLinearThree.Group = ⊥ from Matrix.PSL3Two.center_eq_bot,mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  let P := actorImage H T ⊓ normalizer (actorImage H K : Set (H ⧸ pCore 2 H))
  have hP : IsPGroup 2 P := (quotientSylow H T hH.1.2).isPGroup'.of_injective
    (inclusion (show P ≤ (quotientSylow H T hH.1.2 : Subgroup (H ⧸ pCore 2 H)) from inf_le_left))
    (inclusion_injective _)
  have hres : pResidual 2 (H ⧸ pCore 2 H) ≤
      componentOrbit (actorImage H K) (quotientSylow H T hH.1.2) := by
    rw [quotient_componentOrbit H K T hKH hH.1.2,
      ←source_component_orbit_eq_residual hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK hgen, GenerationOne.residual, actorImage_internal,
      map_pResidual_of_surjective 2 _ (QuotientGroup.mk'_surjective _)]
  apply not_ff_of_sylow_best_centralizes_orbit a.representation
    (quotientSylow H T hH.1.2) (actorImage H K) (pCore_quotient_pCore_eq_bot 2) hres
  intro A hAT hA
  exact hA.centralizes_of_nonFF_orbit a.representation hz hP hI
    (le_inf hAT (ChapterB.source_lemma_B_1_5_4 a.representation a.faithful hA hD))
    (source_l3_seed_orbit_not_ff hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK a hI b hsmall)

/-- The original terminal exchanged-component hypotheses give a non-FF
ambient action on U/Z; the natural seed and its small orbit are constructed. -/
theorem terminal_nonnormal_ambient_not_ff
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
        ¬ IsFFModule a.representation := by
  obtain ⟨hU,a,I,hI,⟨b⟩,_,hsmall,_⟩ := terminal_nonnormal_full_component_action
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  exact ⟨hU,a,source_l3_ambient_not_ff hG T hempty hM hunique hmany hcard e hab hsolv
    Mc (terminal_outside hG T hempty hM hunique hmany hcard e) K hKM hK
    (terminal_nonnormal_generated hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn)
    a hI b hsmall⟩

/-- The exclusion holds for the literal action already chosen by another
source consumer, because original conjugation determines that action uniquely. -/
theorem terminal_nonnormal_action_not_ff
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)) :
    ¬ IsFFModule a.representation := by
  obtain ⟨hU,b,hb⟩ := terminal_nonnormal_ambient_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  rwa [b.representation_eq a] at hb

/-- In the exchanged branch, every involution of the original quotient
has fixed codimension at least two, including component exchangers. -/
theorem terminal_nonnormal_no_involution_transvections
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T))
    (t : Mc ⧸ pCore 2 Mc) (ht : orderOf t = 2) :
    2 ≤ fixedCodim a.representation (zpowers t) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  have hno := terminal_nonnormal_action_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn a
  obtain ⟨he,hr,_,_⟩ := involution_actor_rank_and_fixedCodim a.representation t ht
  have hh : rank (zpowers t) < fixedCodim a.representation (zpowers t) :=
    Nat.lt_of_not_ge (fun hle => hno ⟨_,he,hle⟩)
  omega

/-- The original endpoint selection and strict rank inequality of14.6.24(b)
in the exchanged branch. The actor is the image of the same critical
conjugate of U; no full-support decomposition is assumed. -/
theorem terminal_nonnormal_quadraticEndpoint
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc)]
    (a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)) :
    ∃ p : ComponentCriticalPair.TwoComponents.QuadraticEndpoint
        (terminal_hypothesis hG T hempty hM hunique hmany hcard e hab) a.representation,
      rank (((p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf Mc).map
        (QuotientGroup.mk' (pCore 2 Mc))) <
      fixedCodim a.representation
        (((p.endpoint.conjugate (conjugateSpanBy (localModule T M) Mc)).subgroupOf Mc).map
          (QuotientGroup.mk' (pCore 2 Mc))) := by
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  obtain ⟨p⟩ := ComponentCriticalPair.TwoComponents.source_quadraticEndpoint_of_no_transvections
    hG T hempty hM hunique hmany hcard e hab (originalSection a)
    (terminal_nonnormal_no_involution_transvections
      hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn a)
  exact ⟨p,Nat.lt_of_not_ge (fun hle => terminal_nonnormal_action_not_ff
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn a ⟨_,p.member.1,hle⟩)⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
