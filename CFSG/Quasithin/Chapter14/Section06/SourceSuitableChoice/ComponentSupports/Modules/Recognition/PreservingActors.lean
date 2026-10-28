module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.Exchanged

/-!
# Component-preserving actors on the original terminal quotient

The relative exchanged component gives the literal pair geometry in H/O₂(H).
If a small quadratic actor moved it, the quadratic four-group theorem would
mark K/O₂(K) as PSL₂(2ⁿ). The proved source Borel sieve excludes both parities
of n. Thus the actor preserves K*, and every actual subquotient of U_H/Z
inherits a minimal quadratic actor which acts noncentrally on K*.

These inputs feed LinearThreeSections on the unchanged original quotient.
The full support, FF and suitable-vector assembly remains with
qt-e-suitable-component-supports; original 14.6.18 remains with qt-e-14625-source.
Source: Aschbacher--Smith, F.9.18(3,5), pp.325--326, D.3.6--7,
pp.196--199, and 14.6.20--22, pp.1037--1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
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

/-- The exchanged pair geometry on the original quotient, including its trivial component center. -/
theorem source_nonnormal_quotient_geometry
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal) :
    center (actorImage H K) = ⊥ ∧
      RepresentationReduction.SourceRestrictions.Cases.Exchanged.ExchangedGeometry
        (actorImage H K) (componentOrbit (actorImage H K) (actorImage H T))
        (actorImage H T) ⊥ ⊥ := by
  let D := actorImage H K
  let S := actorImage H T
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let : IsSimpleGroup (K ⧸ pCore 2 K) := source_component_quotient_simple
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : IsSimpleGroup D := ec.symm.isSimpleGroup
  let : IsQuasisimple D := hD.2
  have hz : center D = ⊥ :=
    (inferInstance : (center D).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative D (center_eq_top_iff.mp he))
  have hmove : ¬ S ≤ normalizer (D : Set (H ⧸ pCore 2 H)) := by
    intro hh
    have ht := map_le_iff_le_comap.mp hh
    change (T : Subgroup G).subgroupOf H ≤
      (normalizer (((K.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))) :
        Set (H ⧸ pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) at ht
    rw [normalizer_cComponent_quotient hK (pCore 2 H)] at ht
    have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) := by
      intro t htt
      have hh := ht (show (⟨t,hH.1.2 htt⟩ : H) ∈ (T : Subgroup G).subgroupOf H from htt)
      rwa [←subgroupOf_normalizer_eq hKH] at hh
    have he : conjugateSpanBy K (T : Subgroup G) = K :=
      le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy K _)
    exact hn ((normal_subgroupOf_iff_le_normalizer hKH).mpr
      (he ▸ source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv
        H hH K hKH hK))
  have hs : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hH.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  have hi : (normalizer (D : Set (H ⧸ pCore 2 H))).index = 2 := by
    rcases ChapterA.Section03.NonnormalOrdinary.index_and_model_knownSimple hs
      (pCore_quotient_pCore_eq_bot 2) D (hK.map_quotient (pCore 2 H)) with hdn | hm
    · let := hdn
      exact (hmove (by rw [normalizer_eq_top]; exact le_top)).elim
    · exact hm.1
  have geo := exchanged_geometry_of_index_two D S hD hz hi hmove
  exact ⟨hz,geo⟩

/-- A small quadratic actor on the actual source quotient preserves an exchanged component. -/
theorem source_nonnormal_quadratic_actor_normalizes
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥) :
    A ≤ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) := by
  let D := actorImage H K
  let S := actorImage H T
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  obtain ⟨hz,geo⟩ := source_nonnormal_quotient_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  let : IsQuasisimple D := hD.2
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : IsSimpleGroup D :=
    ((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  have hfaith' : A ⊓ centralizer (componentOrbit D S : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [show componentOrbit D S = actorImage H (conjugateSpanBy K (T : Subgroup G)) from
      quotient_componentOrbit H K T hKH hH.1.2]
    exact hfaith
  by_contra hm
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H))) := Module.Finite.of_finite
  let : IsElementaryAbelian 2 A := hA.1.2
  obtain ⟨F,x,hF,_⟩ := OriginalModule.Exchanged.moving_fourGroup_of_small_ratio
    a.representation geo (le_normalizer_componentOrbit D S) a.faithful hD
    hAT hA.2.1 hfaith' hm hA.2.2
  obtain ⟨m,f,hf,hker,_⟩ := ChapterB.ComponentNormalization.QuadraticSource.exists_marked_model hF
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff _).mp (hker.trans hz)
  have model : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ m.n) :=
    ⟨GaloisField 2 m.n,inferInstance,inferInstance,
      GaloisField.card 2 m.n (by have := m.one_lt; omega),
      ⟨ec.trans (MulEquiv.ofBijective f ⟨hinj,hf⟩)⟩⟩
  rcases Nat.even_or_odd m.n with he | ho
  · exact source_nonnormal_component_not_even_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn he model
  · exact source_nonnormal_component_not_odd_psl_two hG T hempty hM hunique hmany hcard e hab hsolv
      H hH K hKH hK hn m.one_lt ho model

/-- Every literal subquotient of U/Z inherits a minimum-ratio actor which
preserves and acts noncentrally on the selected exchanged component. -/
theorem source_nonnormal_subquotient_minimal_actor
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (U : Subrepresentation a.representation) (N : Subrepresentation U.toRepresentation) :
    ∃ C : Subgroup (H ⧸ pCore 2 H),
      C ≤ normalizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      ¬ C ≤ centralizer (actorImage H K : Set (H ⧸ pCore 2 H)) ∧
      C ∈ ChapterD.RPlusBound N.quotientRepresentation 2 ∧
      IsQuadratic N.quotientRepresentation C := by
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := Module.Finite.of_finite
  obtain ⟨_,geo⟩ := source_nonnormal_quotient_geometry
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn
  have hfaith' : A ⊓ centralizer
      (componentOrbit (actorImage H K) (actorImage H T) : Set (H ⧸ pCore 2 H)) = ⊥ := by
    rw [show componentOrbit (actorImage H K) (actorImage H T) =
      actorImage H (conjugateSpanBy K (T : Subgroup G)) from
        quotient_componentOrbit H K T hKH hH.1.2]
    exact hfaith
  have hq : IsQuadratic N.quotientRepresentation A :=
    quadratic_of_equivariant_surjection U.toRepresentation N.quotientRepresentation
      N.toSubmodule.mkQ N.toSubmodule.mkQ_surjective (fun _ _ => rfl) A
      (quadratic_subrepresentation a.representation U hA.2.1)
  have hd : fixedCodim N.quotientRepresentation A ≤ 2 * rank A := by
    have hU := fixedCodim_subrepresentation_le a.representation U A
    have hN := fixedCodim_quotient_add_subrepresentation_le U.toRepresentation N A
    have hh := hA.2.2
    omega
  exact OriginalModule.Exchanged.exists_minimal_actor_on_component N.quotientRepresentation
    geo hAT hA.1 hq hd hfaith'
    (source_nonnormal_quadratic_actor_normalizes
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith)

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
