module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Modules.Recognition.SingleLinearThree
public import CFSG.Quasithin.ChapterD.Section02.AlternatingSixTypes
public import Theory.Representation.BinaryOffender.AlternatingSixCentralCover

/-!
# Natural central covers on the original single A₆ component

The component-detecting quadratic actor recognizes every noncentral simple
section of the original U/Z. Occurrence and Clifford restriction transfer
those markings to the selected homogeneous seed. Its literal central
quotient is natural and its fixed kernel has dimension at most one. Thus
its full cover has dimension four or five, with no splitting assumption.

The source application lifts the seed to its actual subgroup W inside
[U,K], retaining Z, the original coordinates, and component-fixed overlap
with every distinct Sylow conjugate. Full support exhaustion and the
index-two stabilizer construction remain separate source steps.
Original14.6.18 remains hsolv, owned by qt-e-14625-source; the residual
identity is supplied conditionally by terminal_component_catalogue_of_mixed_size,
whose mixed-size instantiation remains with qt-e-suitable-existence.
Source: Aschbacher--Smith14.6.21--22, printed pp.1037--1038.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender.Homogeneous Representation.OneCohomology
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open Classification Classification.Sieve
open Chapter13.Section08.SourceCompletion.F918
open Subgroup.NormalSylowQuotientAction
open Chapter13.Section08.CriticalGeometry.Reorientation
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

/-- The original A₆ seed has a marked natural quotient and a retained central kernel. -/
theorem terminal_single_a6_natural_seed
    (K : Subgroup G) (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (hr : (solvableResidual Mc).map Mc.subtype = K)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 6)) :
    ∃ hU : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc),
      let _ := hU
      ∃ a : LocalQuotientAction Mc (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T),
      ∃ (I : Submodule (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
        (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))))
        (hI : IsIrrPlusWith a.representation (actorImage Mc K)
          (actorImage Mc T ⊓ normalizer (actorImage Mc K : Set (Mc ⧸ pCore 2 Mc))) I),
        Nonempty (ChapterB.QuasisimpleSource.ActionEquiv
          (centralQuotientRepresentation a.representation (actorImage Mc K) I hI.isIrrPlus.choose)
          (ChapterB.QuasisimpleSource.alternatingNatural 6)) ∧
        Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ≤ 1 ∧
        Module.finrank (ZMod 2) I =
          4 + Module.finrank (ZMod 2) ((fixedSpace a.representation (actorImage Mc K)).comap I.subtype) ∧
        (Module.finrank (ZMod 2) I = 4 ∨ Module.finrank (ZMod 2) I = 5) := by
  have hout := terminal_outside hG T hempty hM hunique hmany hcard e
  have hTH : (T : Subgroup G) ≤ Mc := hout.1.2
  obtain ⟨hn,hgen⟩ := terminal_single_component_generated
    hG T hempty hM hunique hmany hcard e hab hsolv K hKM hK hr (Or.inr ⟨eK⟩)
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    hout.1.2.trans ((normal_subgroupOf_iff_le_normalizer hKM).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTK) (le_conjugateSpanBy _ _)
  obtain ⟨hU,a,B,I,hB,hI,_,hA,hfaith,_⟩ := source_component_span_inputs
    hG T hempty hM hunique hmany hcard e hab hsolv Mc hout K hKM hK
    (by rw [hspan,hgen])
  let := hU
  let : Module.Finite (ZMod 2) (Additive ((conjugateSpanBy (localModule T M) Mc) ⧸
    (centralInvolutions T).subgroupOf (conjugateSpanBy (localModule T M) Mc))) := Module.Finite.of_finite
  let D := actorImage Mc K
  let : D.Normal := hn.map (QuotientGroup.mk' (pCore 2 Mc)) (QuotientGroup.mk'_surjective _)
  have hD := source_quotient_component hG T hempty hM hunique hmany hcard e hab hsolv
    Mc hout K hKM hK
  let : IsQuasisimple D := hD.2
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  let ec : (K ⧸ pCore 2 K) ≃* D :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKM)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hKM))).symm.trans (cComponentTwoCoreQuotientEquiv hK)
  let j := ec.symm.trans eK
  have hz : center D = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr j ⟨k,hk⟩).property
    change j k ∈ center (alternatingGroup (Fin 6)) at hh
    rw [show center (alternatingGroup (Fin 6)) = ⊥ from alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact j.injective (hh.trans j.map_one.symm)
  have ho := quotient_componentOrbit Mc K T hKM hout.1.2
  rw [hspan] at ho hfaith
  have hIQ : IsIrrPlusWith a.representation D
      (actorImage Mc T ⊓ normalizer (D : Set (Mc ⧸ pCore 2 Mc))) I := by
    rw [ho] at hI
    change IsIrrPlusWith a.representation D (actorImage Mc T) I at hI
    simpa only [normalizer_eq_top,inf_top_eq] using hI
  have hs : IsSQTK KnownSimple.IsKnownSimple (Mc ⧸ pCore 2 Mc) := by
    have hsH := Chapter3.sqtk_of_mem_H hG hout.1.1
    refine ⟨?_,hsH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsH.stronglyQuasithin p hp ho)
  let A := B.map (QuotientGroup.mk' (pCore 2 Mc))
  have hAN : A ≤ normalizer (D : Set (Mc ⧸ pCore 2 Mc)) := by
    rw [normalizer_eq_top]; exact le_top
  obtain ⟨b⟩ := ChapterD.central_alternating_six_of_detecting_actor a.representation
    hD.1 hz hs j hAN hA hfaith hIQ.isIrrPlus
  exact ⟨hU,a,I,hIQ,⟨b⟩,hIQ.isIrrPlus.finrank_of_alternating_six_central_quotient
    a.representation D b.groupEquiv b.linearEquiv b.intertwines⟩

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports.Modules.Recognition
