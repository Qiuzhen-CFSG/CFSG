module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Classification.Sieve.SourceOrbit
public import CFSG.Quasithin.Chapter14.Section06.SourcePlacedQuadraticActor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.SourceModels.Seed
public import CFSG.Quasithin.ChapterD.Section03.SourceInternal

/-!
# Homogeneous component seeds on the original span quotient

The source component quotient is simple and hence an ordinary component of
H/O₂(H). Its original Sylow orbit is normal by the rank-two orbit theorem.
Faithfulness on the literal U_H/Z then selects a genuine homogeneous Irr⁺
seed. The component-orbit two-core calculation verifies D.3.2, and D.3.3
supplies the faithful action on its actual orbit span.

The terminal application retains H=Mc, including the two-normal-component
case. It does not assume H=KT or identify the seed orbit with the entire
moved space. That exhaustion, natural-module recognition and support
assembly remain with qt-e-suitable-component-supports. The allowed input
14.6.18 remains with qt-e-14625-source.
Source: Aschbacher--Smith F.9.18(1), pp.325--326; D.3.2--3, p.193;
the seed chosen in 14.6.22, p.1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Representation.BinaryOffender.Homogeneous
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
variable {G : Type*} [Group G] [Finite G]

/-- The actual Sylow image in the original two-core quotient. -/
@[expose] noncomputable def quotientSylow (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) : Sylow 2 (H ⧸ pCore 2 H) :=
  (T.subtype hTH).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))

@[simp] theorem quotientSylow_coe (H : Subgroup G) (T : Sylow 2 G)
    (hTH : (T : Subgroup G) ≤ H) :
    (quotientSylow H T hTH : Subgroup (H ⧸ pCore 2 H)) = actorImage H T := rfl

/-- The component orbit is the image of the literal ambient conjugate span. -/
theorem quotient_componentOrbit (H K : Subgroup G) (T : Sylow 2 G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H) :
    componentOrbit (actorImage H K) (quotientSylow H T hTH) =
      actorImage H (conjugateSpanBy K (T : Subgroup G)) := by
  rw [quotientSylow_coe]
  rw [componentOrbit, ← conjugateSpanBy_eq_iSup_conj]
  unfold actorImage
  have he : (conjugateSpanBy K (T : Subgroup G)).subgroupOf H =
      conjugateSpanBy (K.subgroupOf H) ((T : Subgroup G).subgroupOf H) := by
    apply map_injective H.subtype_injective
    rw [map_subgroupOf_eq_of_le (conjugateSpanBy_le hKH (hTH.trans H.le_normalizer)),
      map_conjugateSpanBy, map_subgroupOf_eq_of_le hKH, map_subgroupOf_eq_of_le hTH]
  rw [he, map_conjugateSpanBy]

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

/-- Each actual relative component becomes an ordinary component of H/O₂(H). -/
theorem source_quotient_component
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    IsComponent (H ⧸ pCore 2 H) (actorImage H K) := by
  let : IsSimpleGroup (K ⧸ pCore 2 K) := source_component_quotient_simple
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let ec := (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let : IsSimpleGroup (actorImage H K) := ec.symm.isSimpleGroup
  let : Group.IsPerfect (actorImage H K) := (hK.map_quotient (pCore 2 H)).perfect
  have hz : center (actorImage H K) = ⊥ := by
    rcases (inferInstance : (center (actorImage H K)).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative (actorImage H K) (center_eq_top_iff.mp hz)).elim
  exact ⟨(hK.map_quotient (pCore 2 H)).subnormal,
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩⟩

/-- Normality holds for the entire Sylow component orbit in the original quotient. -/
theorem source_quotient_componentOrbit_normal
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent) :
    (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2)).Normal := by
  have hXH : conjugateSpanBy K (T : Subgroup G) ≤ H :=
    conjugateSpanBy_le hKH (hH.1.2.trans H.le_normalizer)
  let : ((conjugateSpanBy K (T : Subgroup G)).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hXH).mpr
      (source_component_orbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
  rw [quotient_componentOrbit H K T hKH hH.1.2]
  exact Normal.map inferInstance _ (QuotientGroup.mk'_surjective (pCore 2 H))

/-- A genuine homogeneous seed exists on the whole original H-span modulo Z. -/
theorem source_exists_homogeneous_seed
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)) :
    ∃ I, IsIrrPlusWith a.representation
      (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2))
      (quotientSylow H T hH.1.2) I := by
  have hc := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let S := quotientSylow H T hH.1.2
  let X := componentOrbit (actorImage H K) S
  let : Group.IsPerfect X := hc.orbit_isPerfect S
  have hX : X ≠ ⊥ := by
    intro he
    exact hc.isCComponent.ne_bot (bot_unique (he ▸ le_componentOrbit (actorImage H K) S))
  exact exists_isIrrPlusWith_of_faithful a.representation a.faithful X S hX
    (le_normalizer_componentOrbit _ _) S.isPGroup'

/-- Every such seed satisfies the genuine internal D.3 hypotheses on U_H/Z. -/
theorem source_internal_module
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation
      (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2))
      (quotientSylow H T hH.1.2) I) :
    ChapterD.Section03.InternalModuleHypotheses KnownSimple.IsKnownSimple a.representation
      (quotientSylow H T hH.1.2)
      (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2)) I := by
  have hs : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hH.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  exact Chapter13.Section08.Components.SourceModels.internal_module_of_component_orbit
    a.representation hs a.faithful (pCore_quotient_pCore_eq_bot 2)
    (actorImage H K) (quotientSylow H T hH.1.2)
    (source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK)
    (source_quotient_componentOrbit_normal hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK) hI

/-- D.3.3 applies to the actual orbit span without an assumed orbit-exhaustion statement. -/
theorem source_faithful_seed_orbit
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    {I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) H) ⧸
      (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) H)))}
    (hI : IsIrrPlusWith a.representation
      (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2))
      (quotientSylow H T hH.1.2) I) :
    let W := orbitSpan a.representation ⊤ I
    ChapterD.Section03.SourceHypotheses KnownSimple.IsKnownSimple
      (subspaceImageRepresentation a.representation W)
      ((quotientSylow H T hH.1.2).mapSurjective
        (invariantActionHom_surjective a.representation W (orbitSpan_invariant a.representation ⊤ I)))
      (restrictedSubgroup a.representation W
        (componentOrbit (actorImage H K) (quotientSylow H T hH.1.2)))
      (I.comap W.subtype) :=
  (source_internal_module hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK a hI).faithfulOrbit_source

/-- Select a seed and its genuine D.3 input on the unchanged terminal U/Z. -/
theorem terminal_component_seed_inputs
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ I,
        IsIrrPlusWith a.representation
          (componentOrbit (actorImage Mc K) (quotientSylow Mc T
            (terminal_outside hG T hempty hM hunique hmany hcard e).1.2))
          (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2) I ∧
        ChapterD.Section03.InternalModuleHypotheses KnownSimple.IsKnownSimple a.representation
          (quotientSylow Mc T (terminal_outside hG T hempty hM hunique hmany hcard e).1.2)
          (componentOrbit (actorImage Mc K) (quotientSylow Mc T
            (terminal_outside hG T hempty hM hunique hmany hcard e).1.2)) I := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,_⟩ := source_rankTwo_quadratic_bound hG T hempty hM hunique hmany hcard e hab Mc hout
  let := hU
  obtain ⟨I,hI⟩ := source_exists_homogeneous_seed
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a
  exact ⟨hU,a,I,hI,source_internal_module
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK a hI⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
