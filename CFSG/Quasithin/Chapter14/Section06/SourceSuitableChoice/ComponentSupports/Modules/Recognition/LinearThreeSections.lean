module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.PreservingActors
public import CFSG.Quasithin.ChapterD.Section02.LinearThreeConstituents

/-!
# Natural component types in the terminal exchanged branch

On every irreducible subquotient of the original U_H/Z, Clifford theory
makes the component restriction semisimple. The proved preservation of
the source quadratic actor supplies a minimal actor detecting the chosen
component. The binary PSL₃ source marking and Chapter D recognition then
give natural coordinates for every noncentral irreducible component type.

At H=Mc, the terminal source hypotheses construct the original action,
placed actor and a component-detecting irreducible subquotient, and hence
an actual natural constituent. This is section recognition; the central
covers, FF elimination and full support decomposition still belong to
qt-e-suitable-component-supports. Original 14.6.18 remains with
qt-e-14625-source and the later suitable clauses with qt-e-suitable-existence.
Source: Aschbacher--Smith, F.9.18(3,5), pp.325--326, and the natural
module argument in 14.6.22, printed p.1038.
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

/-- Every noncentral irreducible component type in an actual irreducible
subquotient of U/Z is natural, with no chosen-type or classification premise. -/
theorem source_nonnormal_subquotient_all_natural
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (U : Subrepresentation a.representation) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation) :
    ChapterD.NaturalLinearThreeTypes N.quotientRepresentation (actorImage H K) := by
  let σ := N.quotientRepresentation
  let D := actorImage H K
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : IsQuasisimple D := hD.2
  let : IsIrreducible σ := hi
  let : IsSemisimpleRepresentation (σ.comp D.subtype) :=
    (isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).mpr
      (subnormal_restriction_semisimple σ D hD.1)
  obtain ⟨C,hCN,hnC,hC,hqC⟩ := source_nonnormal_subquotient_minimal_actor
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith U N
  have hs : IsSQTK KnownSimple.IsKnownSimple (H ⧸ pCore 2 H) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hH.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKH)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKH))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  have hm : ClassicalGroup.IsPSL D 3 2 :=
    (source_nonnormal_component_linear_three
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn).of_mulEquiv ec.symm
  exact ChapterD.naturalLinearThreeTypes_of_minimal_actor σ (K := D) (C := C)
    (source_nonnormal_quotient_geometry
      hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn).1
    hs hm hCN hC hqC hnC

/-- Every component-detecting irreducible subquotient of the original U/Z
contains a genuine natural constituent for the exchanged component. -/
theorem source_nonnormal_subquotient_natural_constituent
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (K : Subgroup G) (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hn : ¬ (K.subgroupOf H).Normal)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    (a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T))
    (A : Subgroup (H ⧸ pCore 2 H))
    (hAT : A ≤ actorImage H T) (hA : QuadraticMember a.representation A)
    (hfaith : A ⊓ centralizer (actorImage H (conjugateSpanBy K (T : Subgroup G)) :
      Set (H ⧸ pCore 2 H)) = ⊥)
    (U : Subrepresentation a.representation) (N : Subrepresentation U.toRepresentation)
    (hi : IsIrreducible N.quotientRepresentation)
    (hdetect : ¬ actorImage H K ≤ N.quotientRepresentation.ker) :
    ∃ (C : Subgroup (H ⧸ pCore 2 H)) (I : Submodule (ZMod 2) (U ⧸ N.toSubmodule))
      (hI : IsIrrPlusWith N.quotientRepresentation (actorImage H K) C I),
      C ∈ ChapterD.RPlusBound N.quotientRepresentation 2 ∧
      IsQuadratic N.quotientRepresentation C ∧
      ∃ F : ChapterB.QuasisimpleSource.BinaryField, F.degree = 1 ∧
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
          (invariantSubspace N.quotientRepresentation (actorImage H K) I hI.invariant).toRepresentation
          (ChapterB.QuasisimpleSource.linearNatural F 3)) := by
  let σ := N.quotientRepresentation
  let D := actorImage H K
  let : Finite (U ⧸ N.toSubmodule) := Module.finite_of_finite (ZMod 2)
  let : Module.Finite (ZMod 2) (U ⧸ N.toSubmodule) := Module.Finite.of_finite
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK
  let : IsQuasisimple D := hD.2
  obtain ⟨C,hCN,hnC,hC,hqC⟩ := source_nonnormal_subquotient_minimal_actor
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith U N
  have hnf : ¬ (⊤ : Submodule (ZMod 2) (U ⧸ N.toSubmodule)) ≤ fixedSpace σ D := by
    intro hh
    apply hdetect
    intro k hk
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro v
    exact hh Submodule.mem_top ⟨k,hk⟩
  obtain ⟨I,hI⟩ := exists_isIrrPlus_of_not_fixed σ D hnf
  let : IsElementaryAbelian 2 C := hC.1.1.2
  obtain ⟨I',_,hI'⟩ := exists_isIrrPlusWith_le_orbitSpan σ hCN
    (IsElementaryAbelian.isPGroup 2 C) hI
  exact ⟨C,I',hI',hC,hqC,source_nonnormal_subquotient_all_natural
    hG T hempty hM hunique hmany hcard e hab hsolv H hH K hKH hK hn a A hAT hA hfaith
    U N hi I' hI'.isIrrPlus⟩

/-- The terminal exchanged source constructs a natural section on the
unchanged Mc-action and U/Z, discharging every actor and section premise. -/
theorem terminal_nonnormal_natural_constituent
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hn : ¬ (K.subgroupOf Mc).Normal) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (U : Subrepresentation a.representation) (N : Subrepresentation U.toRepresentation),
        IsIrreducible N.quotientRepresentation ∧
        ∃ (C : Subgroup (Mc ⧸ pCore 2 Mc)) (I : Submodule (ZMod 2) (U ⧸ N.toSubmodule))
          (hI : IsIrrPlusWith N.quotientRepresentation (actorImage Mc K) C I),
          C ∈ ChapterD.RPlusBound N.quotientRepresentation 2 ∧
          IsQuadratic N.quotientRepresentation C ∧
          ∃ F : ChapterB.QuasisimpleSource.BinaryField, F.degree = 1 ∧
            Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
              (invariantSubspace N.quotientRepresentation (actorImage Mc K) I hI.invariant).toRepresentation
              (ChapterB.QuasisimpleSource.linearNatural F 3)) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  obtain ⟨hU,a,B,_,hB,_,_,hA,hfaith,_⟩ := terminal_nonnormal_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hn
  let := hU
  have hD := source_quotient_component
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
  let : IsQuasisimple (actorImage Mc K) := hD.2
  have hdetect : ¬ actorImage Mc K ≤ a.representation.ker := by
    intro hh
    exact hD.isCComponent.ne_bot
      (bot_unique (hh.trans ((MonoidHom.ker_eq_bot_iff _).mpr a.faithful).le))
  obtain ⟨U,N,hi,hnK⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (actorImage Mc K) hdetect
  exact ⟨hU,a,U,N,hi,source_nonnormal_subquotient_natural_constituent
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK hn a
    (B.map (QuotientGroup.mk' (pCore 2 Mc)))
    (source_internal_actor_le_sylow T hout.1.2 B hB) hA hfaith U N hi hnK⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
