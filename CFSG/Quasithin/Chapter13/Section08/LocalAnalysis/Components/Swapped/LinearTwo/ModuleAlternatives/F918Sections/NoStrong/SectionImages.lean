module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong.Setup
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.KernelComparison

/-!
# Faithful action images of the two literal sections

Every representation nontrivial on the component orbit of the exchanged
actor is faithful: its kernel centralizes that orbit, whose centralizer is
trivial. This applies separately to a noncentral submodule and every proper
quotient of a commutator-generated module. No irreducibility is required.

The resulting image equivalence sends the action of each element back to
that same element and preserves every marked subgroup. Strong offending
therefore transports in both directions. The final theorem below is only
the transfer step: the intrinsic faithful-module exclusion still has to be
proved from B.4.2 before applying it.

Source: Aschbacher–Smith, 13.8.16(1), printed p.952, and F.9.18(6), p.326.
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong

open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions

universe u v w
variable {𝒦 : GroupClass.{u}} {D : Type u} [Group D] [Finite D]
    {F : Type w} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (d : ExchangedActor 𝒦 D F n)
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

/-- The actual action kernel vanishes on every noncentral orbit section. -/
theorem ExchangedActor.action_kernel_eq_bot
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) : (actionHom ρ).ker = ⊥ := by
  have hk := action_kernel_le_centralizer_of_component_orbit ρ
    d.component (d.sylow : Subgroup D) d.component_isComponent (d.orbit_eq ▸ hn)
  rw [← d.orbit_eq, d.centralizer_eq_bot] at hk
  exact bot_unique hk

/-- Faithfulness concerns D itself, not just the elementary offender. -/
theorem ExchangedActor.faithful_of_noncentral
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) : Function.Injective ρ := by
  have hf := (MonoidHom.ker_eq_bot_iff (actionHom ρ)).mp (d.action_kernel_eq_bot ρ hn)
  intro x y h
  apply hf
  apply imageRepresentation_injective ρ
  exact h

/-- The literal faithful image, with its original lifts, is D. -/
def ExchangedActor.imageEquiv
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) : actionImage ρ ≃* D :=
  actionImageModelEquiv ρ (MonoidHom.id D) Function.surjective_id
    (by rw [d.action_kernel_eq_bot ρ hn, MonoidHom.ker_id])

@[simp] theorem ExchangedActor.imageEquiv_actionHom
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) (g : D) :
    d.imageEquiv ρ hn (actionHom ρ g) = g :=
  actionImageModelEquiv_actionHom ρ _ _ _ g

/-- Every marked subgroup uses the same equivalence, including both
components, their orbit, the Sylow subgroup and its moving element. -/
theorem ExchangedActor.imageEquiv_subgroup
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) (A : Subgroup D) :
    (actionSubgroup ρ A).map (d.imageEquiv ρ hn).toMonoidHom = A := by
  simpa only [ExchangedActor.imageEquiv, Subgroup.map_id] using
    actionImageModelEquiv_subgroup ρ (MonoidHom.id D) Function.surjective_id
      (by rw [d.action_kernel_eq_bot ρ hn, MonoidHom.ker_id]) A

/-- Strong offending is unchanged by this actual image comparison. -/
theorem ExchangedActor.strong_image_iff
    (hn : ¬ ∀ l ∈ d.orbit, ∀ v, ρ l v = v) :
    IsStrongFFModule (imageRepresentation ρ) ↔ IsStrongFFModule ρ := by
  let e := d.imageEquiv ρ hn
  have he (g : actionImage ρ) (v : V) : imageRepresentation ρ g v = ρ (e g) v := by
    obtain ⟨x, rfl⟩ := (show Function.Surjective (actionHom ρ) from
      ρ.asGroupHom.rangeRestrict_surjective) g
    rw [show e (actionHom ρ x) = x from d.imageEquiv_actionHom ρ hn x]
    rfl
  constructor
  · exact strongFF_map_equivariant (imageRepresentation ρ) ρ e.toMonoidHom
      e.injective (LinearEquiv.refl _ _) he
  · apply strongFF_map_equivariant ρ (imageRepresentation ρ) e.symm.toMonoidHom
      e.symm.injective (LinearEquiv.refl _ _)
    intro g v
    simpa using (he (e.symm g) v).symm

/-- Both exact section actions are faithful on D under the source conditions. -/
theorem ExchangedActor.sections_faithful
    (hfull : subspaceCommutator ρ ⊤ d.orbit = ⊤)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤)
    (hnW : ¬ W.toSubmodule ≤ fixedSpace ρ d.orbit) :
    Function.Injective W.toRepresentation ∧ Function.Injective W.quotientRepresentation :=
  ⟨d.faithful_of_noncentral W.toRepresentation
      (subrepresentation_nontrivial_of_not_central ρ d.orbit W hnW),
    d.faithful_of_noncentral W.quotientRepresentation
      (quotient_nontrivial_of_moved_eq_top ρ d.orbit hfull W hW)⟩

/-- Once the intrinsic exclusion is proved, it supplies exactly the hnW
and hnQ premises of `exists_source_section_dichotomy`. This theorem proves
the faithful-image transfer, not the intrinsic B.4.2 exclusion. -/
theorem ExchangedActor.section_exclusions_of_faithful_exclusion [Finite V]
    (hexclude : ∀ (U : Type v) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
      (σ : Representation (ZMod 2) D U), Function.Injective σ → ¬ IsStrongFFModule σ)
    (hfull : subspaceCommutator ρ ⊤ d.orbit = ⊤) :
    (∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ W.toSubmodule ≤ fixedSpace ρ d.orbit →
      ¬ IsStrongFFModule (imageRepresentation W.toRepresentation)) ∧
    (∀ W : Subrepresentation ρ, W ≠ ⊤ →
      ¬ IsStrongFFModule (imageRepresentation W.quotientRepresentation)) := by
  constructor
  · intro W _ hnW hs
    have hn := subrepresentation_nontrivial_of_not_central ρ d.orbit W hnW
    exact hexclude W.toSubmodule W.toRepresentation (d.faithful_of_noncentral _ hn)
      ((d.strong_image_iff _ hn).mp hs)
  · intro W hW hs
    let : Finite (V ⧸ W.toSubmodule) :=
      Finite.of_surjective W.toSubmodule.mkQ W.toSubmodule.mkQ_surjective
    have hn := quotient_nontrivial_of_moved_eq_top ρ d.orbit hfull W hW
    exact hexclude (V ⧸ W.toSubmodule) W.quotientRepresentation
      (d.faithful_of_noncentral _ hn) ((d.strong_image_iff _ hn).mp hs)

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.ModuleAlternatives.F918Sections.NoStrong
