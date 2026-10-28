module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Actor
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors.Sections
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FaithfulSections
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# The component orbit inside the faithful offender actor

A centerless normal component orbit supplemented by a two-group has trivial
centralizer when the ambient two-core is trivial. The component-normal-subgroup
dichotomy then puts the whole orbit inside every nontrivial normal subgroup.
Applied to the inverse image of the offender actor, this proves its containment
of the original components, without assuming the whole actor is offender-generated.
The same centralizer argument proves faithfulness of nontrivial section actions.
Actual multiplicative and intertwining equivalences retain the original inclusions.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.5.3–6,
printed pp.104–105, and the proof of 13.8.16(1), p.952 (PDF p.969).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

theorem orbit_normal_of_generated (K T : Subgroup D)
    (hgen : conjugateSpanBy K T ⊔ T = ⊤) : (conjugateSpanBy K T).Normal := by
  rw [← normalizer_eq_top_iff]
  apply top_unique
  rw [← hgen]
  exact sup_le (conjugateSpanBy K T).le_normalizer (le_normalizer_conjugateSpanBy K T)

theorem centralizer_orbit_eq_bot (K T : Subgroup D)
    (hgen : conjugateSpanBy K T ⊔ T = ⊤) (hT : IsPGroup 2 T)
    (hZ : center (conjugateSpanBy K T) = ⊥) (hcore : pCore 2 D = ⊥) :
    centralizer (conjugateSpanBy K T : Set D) = ⊥ := by
  let L := conjugateSpanBy K T
  let : L.Normal := orbit_normal_of_generated K T hgen
  let C := centralizer (L : Set D)
  let f := (QuotientGroup.mk' L).comp C.subtype
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro c hc
    have hcL : (c : D) ∈ L := (QuotientGroup.eq_one_iff _).mp hc
    have hz : (⟨c, hcL⟩ : L) ∈ center L := by
      apply mem_center_iff.mpr
      intro l
      exact Subtype.ext (c.property l l.property)
    rw [hZ] at hz
    exact Subtype.ext (congrArg (fun x : L => (x : D)) (mem_bot.mp hz))
  have hp : IsPGroup 2 C := (isPGroup_quotient_of_sup_eq_top L T hT hgen).of_injective f hf
  exact le_bot_iff.mp ((show C ≤ pCore 2 D from le_sSup ⟨inferInstance, hp⟩).trans hcore.le)

theorem orbit_le_normal_of_ne_bot (K T N : Subgroup D)
    (hK : IsComponent D K) [N.Normal] (hN : N ≠ ⊥)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥) :
    conjugateSpanBy K T ≤ N := by
  rcases hK.normal_dichotomy N with hk | hc
  · exact conjugateSpanBy_le hk (by rw [normalizer_eq_top]; exact le_top)
  · have hl : conjugateSpanBy K T ≤ centralizer (N : Set D) :=
      conjugateSpanBy_le (commutator_eq_bot_iff_le_centralizer.mp hc)
        (by rw [normalizer_eq_top]; exact le_top)
    exact (hN (le_bot_iff.mp ((le_centralizer_iff.mp hl).trans hC.le))).elim

theorem orbit_action_faithful (ρ : Representation (ZMod 2) D V)
    (K T : Subgroup D) (hK : IsComponent D K)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hn : ¬ ∀ l ∈ conjugateSpanBy K T, ∀ v, ρ l v = v) :
    Function.Injective ρ := by
  have hk : (actionHom ρ).ker = ⊥ := le_bot_iff.mp
    ((action_kernel_le_centralizer_of_component_orbit ρ K T hK hn).trans hC.le)
  intro a b hab
  apply (MonoidHom.ker_eq_bot_iff (actionHom ρ)).mp hk
  exact imageRepresentation_injective ρ hab

theorem orbit_image_le_offender [Finite D] [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (K T : Subgroup D) (hK : IsComponent D K)
    (hC : centralizer (conjugateSpanBy K T : Set D) = ⊥)
    (hff : IsFFModule (imageRepresentation ρ)) :
    actionSubgroup ρ (conjugateSpanBy K T) ≤ offenderActor (imageRepresentation ρ) := by
  let J := offenderActor (imageRepresentation ρ)
  let N := J.comap (actionHom ρ)
  have hN : N ≠ ⊥ := by
    intro hn
    have hj : J = ⊥ := by
      rw [← map_comap_eq_self_of_surjective (f := actionHom ρ)
          ρ.asGroupHom.rangeRestrict_surjective J,
        show J.comap (actionHom ρ) = ⊥ from hn, Subgroup.map_bot]
    have : Nontrivial J := nontrivial_of_ff _ (offender_isFFModule _ hff)
    obtain ⟨j, hj1⟩ := exists_ne (1 : J)
    exact hj1 (Subtype.ext (mem_bot.mp (hj ▸ j.property)))
  exact map_le_iff_le_comap.mpr (orbit_le_normal_of_ne_bot K T N hK hN hC)

def markedActorEquiv (ρ : Representation (ZMod 2) D V)
    (hfaith : Function.Injective ρ) (A : Subgroup D)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ)) :
    A ≃* (actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)) :=
  (faithfulActionEquiv ρ A (fun a _ ha => hfaith (by ext v; simpa using ha v))).trans
    (subgroupOfEquivOfLe hA).symm

@[simp] theorem markedActorEquiv_apply (ρ : Representation (ZMod 2) D V)
    (hfaith : Function.Injective ρ) (A : Subgroup D)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ)) (a : A) :
    (((markedActorEquiv ρ hfaith A hA a : offenderActor (imageRepresentation ρ)) :
      actionImage ρ)) = actionHom ρ a := rfl

def markedActionEquiv (ρ : Representation (ZMod 2) D V)
    (hfaith : Function.Injective ρ) (A : Subgroup D)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ)) :
    ActionEquiv (ρ.comp A.subtype)
      ((offenderRepresentation (imageRepresentation ρ)).comp
        ((actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ))).subtype) where
  groupEquiv := markedActorEquiv ρ hfaith A hA
  linearEquiv := LinearEquiv.refl _ _
  intertwines _ _ := rfl

theorem marked_isComponent (ρ : Representation (ZMod 2) D V)
    (hfaith : Function.Injective ρ) (A : Subgroup D) (hcomp : IsComponent D A)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ)) :
    IsComponent (offenderActor (imageRepresentation ρ))
      ((actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ))) := by
  let := hcomp.2
  exact ⟨(hcomp.1.map ρ.asGroupHom.rangeRestrict_surjective).subgroupOf,
    IsQuasisimple.of_mulEquiv (markedActorEquiv ρ hfaith A hA)⟩

/-- The same comparison on the canonical commutator spaces, by their literal equality. -/
def markedFactorActionEquiv (ρ : Representation (ZMod 2) D V)
    (hfaith : Function.Injective ρ) (A : Subgroup D)
    (hA : actionSubgroup ρ A ≤ offenderActor (imageRepresentation ρ)) :
    ActionEquiv (factorRepresentation ρ A)
      (factorRepresentation (offenderRepresentation (imageRepresentation ρ))
        ((actionSubgroup ρ A).subgroupOf (offenderActor (imageRepresentation ρ)))) where
  groupEquiv := markedActorEquiv ρ hfaith A hA
  linearEquiv := LinearEquiv.ofEq _ _ (actionImage_marked_commutator ρ A hA ⊤).symm
  intertwines _ _ := Subtype.ext rfl

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.FFFactors
