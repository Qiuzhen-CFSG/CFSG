module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.Inputs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.ActorFusion
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry.NormalizerJoins

/-!
# Assembly of characteristic-five positioned-centralizer geometry

Two independent model calculations establish fusion and projected images of
individual actors, and generation by the two centralizers and the normalizers
of their distinguished four- and eight-subgroups. The assembly below combines
these proved calculations to establish the published geometry contract,
including every invariant-family union of actor orbits and maximal overgroup.

When a family has usable actors in both centralizers, their generating join
forces one to escape. Otherwise its weak closure is one of the two nested
orbit spans on the unusable side. The literal normalizer of that span then
forces the other, usable centralizer to escape. No monotonicity of normalizers
is used. The chosen actor remains in the original invariant family, and its
image uses exactly the projective projection after the actual comparison.

The final theorem discharges `Frame.Fusion` and `Frame.Generation` for an
actual common-Sylow frame. It has no E-generation or geometric premise.
Source: Aschbacher--Smith E.1.5, E.1.8 and E.1.14(6), printed pp.210--214;
the last cites Aschbacher (1982), Lemma 4.10.
-/

public section
noncomputable section
open Subgroup GorensteinWalter Matrix
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry

variable {F : Type*} [Field F] [Finite F]
variable {σ : F ≃+* F}

namespace Frame
variable (c : Frame σ) (hF : Nat.card F = 5 ^ 2) (hσ : orderOf σ = 2)

/-- A usable image belonging to the original family, without saturation. -/
@[expose] def FamilyUsable (Ω : Set (Subgroup (innerModel F σ))) (i : Bool) : Prop :=
  ∃ A ∈ Ω, A ≤ (c.T : Subgroup (innerModel F σ)) ∧ c.IsPositioned hF hσ i A

theorem familyUsable_of_usable {Ω : Set (Subgroup (innerModel F σ))}
    (hΩ : IsElementaryFamily Ω) {A : Subgroup (innerModel F σ)} (hA : A ∈ Ω)
    {i : Bool} (hu : c.Usable hF hσ i A) : c.FamilyUsable hF hσ Ω i := by
  obtain ⟨B, ⟨hBT, g, rfl⟩, hpos⟩ := hu
  exact ⟨_, hΩ.2 g A hA, hBT, hpos⟩

variable [Finite (innerModel F σ)]

/-- This is the union calculation used by the actual source assembly. -/
theorem weakClosure_eq_of_not_familyUsable (hf : c.Fusion hF hσ)
    {Ω : Set (Subgroup (innerModel F σ))} (hΩ : IsElementaryFamily Ω)
    (hr : ∀ A ∈ Ω, A ≤ (c.T : Subgroup _) → A ≠ ⊥ →
      Group.rank A = 2 ∨ Group.rank A = 3)
    (hne : ∃ A ∈ Ω, A ≤ (c.T : Subgroup _) ∧ A ≠ ⊥)
    (i : Bool) (hbad : ¬ c.FamilyUsable hF hσ Ω i) :
    weakClosure (c.T : Subgroup (innerModel F σ)) Ω = c.small hF hσ i ∨
      weakClosure (c.T : Subgroup (innerModel F σ)) Ω = c.large hF hσ i := by
  apply weakClosure_eq_of_two_orbitSpans _ _ _ hΩ (c.small_le_large hF hσ i) hne
  intro A hA hAT hbot
  apply hf.spans i A ⟨hΩ.1 A hA, hAT, hbot, hr A hA hAT hbot⟩
  intro hu
  exact hbad (c.familyUsable_of_usable hF hσ hΩ hA hu)

private theorem opposite_centralizer_escapes (hf : c.Fusion hF hσ)
    (hg : c.Generation hF hσ)
    {Ω : Set (Subgroup (innerModel F σ))} (hΩ : IsElementaryFamily Ω)
    (hr : ∀ A ∈ Ω, A ≤ (c.T : Subgroup _) → A ≠ ⊥ →
      Group.rank A = 2 ∨ Group.rank A = 3)
    (hne : ∃ A ∈ Ω, A ≤ (c.T : Subgroup _) ∧ A ≠ ⊥)
    (M : Subgroup (innerModel F σ)) (hM : M ≠ ⊤)
    (hNM : normalizer (weakClosure (c.T : Subgroup _) Ω : Set (innerModel F σ)) ≤ M)
    (i : Bool) (hbad : ¬ c.FamilyUsable hF hσ Ω i) : ¬ c.centralizerAt (!i) ≤ M := by
  intro hCM
  have hw := c.weakClosure_eq_of_not_familyUsable hF hσ hf hΩ hr hne i hbad
  apply hM
  apply top_unique
  rcases hw with hw | hw
  · rw [← hg.small i]
    exact sup_le hCM (hw ▸ hNM)
  · rw [← hg.large i]
    exact sup_le hCM (hw ▸ hNM)

end Frame

/-- The original geometry contract follows from individual-actor fusion and
the five concrete generation identities. All invariant-family union cases
are discharged here; no smaller-group E-generation input is used. -/
theorem hasPositionedCentralizerGeometry_of_frame (hF : Nat.card F = 5 ^ 2)
    (hσ : orderOf σ = 2) [Finite (innerModel F σ)] (c : Frame σ)
    (hf : c.Fusion hF hσ) (hg : c.Generation hF hσ) :
    HasPositionedCentralizerGeometry hF σ hσ := by
  classical
  refine ⟨c.T, ?_⟩
  intro Ω hΩ hr M hM _hTM hNM
  have hne : ∃ A ∈ Ω, A ≤ (c.T : Subgroup _) ∧ A ≠ ⊥ := by
    by_contra hn
    have hw : weakClosure (c.T : Subgroup _) Ω = ⊥ := by
      apply le_bot_iff.mp
      apply sSup_le
      rintro A ⟨hA, hAT⟩
      exact (not_ne_iff.mp (fun h => hn ⟨A, hA, hAT, h⟩)).le
    rw [hw, normalizer_eq_top] at hNM
    exact hM.ne_top (top_unique hNM)
  have finish (i : Bool) (hu : c.FamilyUsable hF hσ Ω i)
      (hout : ¬ c.centralizerAt i ≤ M) :
      ∃ A : Subgroup (innerModel F σ), A ∈ Ω ∧ A ≤ (c.T : Subgroup _) ∧
        ∃ x : innerModel F σ, orderOf x = 2 ∧
          (c.T : Subgroup _) ≤ centralizer ({x} : Set (innerModel F σ)) ∧
          ∃ e : centralizer ({x} : Set (innerModel F σ)) ≃*
              centralizer ({pure σ} : Set (innerModel F σ)),
            PositionedImage (FixedPoints.subfield (zpowers σ) F)
              ((A.subgroupOf (centralizer ({x} : Set (innerModel F σ)))).map
                ((projectiveProjection hF σ hσ).comp e.toMonoidHom)) ∧
            ¬ centralizer ({x} : Set (innerModel F σ)) ≤ M := by
    obtain ⟨A, hA, hAT, hp⟩ := hu
    exact ⟨A, hA, hAT, c.involution i, c.involution_order hσ i, c.sylow_le i,
      c.comparisonAt i, hp, hout⟩
  have hone : c.FamilyUsable hF hσ Ω false ∨ c.FamilyUsable hF hσ Ω true := by
    obtain ⟨A, hA, hAT, hbot⟩ := hne
    exact (hf.coverage A ⟨hΩ.1 A hA, hAT, hbot, hr A hA hAT hbot⟩).imp
      (c.familyUsable_of_usable hF hσ hΩ hA) (c.familyUsable_of_usable hF hσ hΩ hA)
  by_cases hleft : c.FamilyUsable hF hσ Ω false
  · by_cases hright : c.FamilyUsable hF hσ Ω true
    · by_cases hCM : c.centralizerAt false ≤ M
      · apply finish true hright
        intro hDM
        exact hM.ne_top (top_unique (hg.pair ▸ sup_le hCM hDM))
      · exact finish false hleft hCM
    · exact finish false hleft
        (c.opposite_centralizer_escapes hF hσ hf hg hΩ hr hne M hM.ne_top hNM true hright)
  · exact finish true (hone.resolve_left hleft)
      (c.opposite_centralizer_escapes hF hσ hf hg hΩ hr hne M hM.ne_top hNM false hleft)

/-- Final assembly interface for independent, uniformly aligned producers.
Existence of the actual frame is discharged by quadratic-field descent. -/
theorem hasPositionedCentralizerGeometry_of_fusion_and_generation
    (hF : Nat.card F = 5 ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)]
    (hf : ∀ c : Frame σ, c.Fusion hF hσ)
    (hg : ∀ c : Frame σ, c.Generation hF hσ) :
    HasPositionedCentralizerGeometry hF σ hσ := by
  obtain ⟨c⟩ := nonempty_frame hF σ hσ
  exact hasPositionedCentralizerGeometry_of_frame hF hσ c (hf c) (hg c)

/-- Every order-25 field inner model has the published positioned-centralizer
geometry. Both the actor fusion and the five centralizer/normalizer joins are
proved in the actual model, with no additional local or generation premise. -/
theorem hasPositionedCentralizerGeometry
    (hF : Nat.card F = 5 ^ 2) (σ : F ≃+* F) (hσ : orderOf σ = 2)
    [Finite (innerModel F σ)] :
    HasPositionedCentralizerGeometry hF σ hσ := by
  obtain ⟨c, hg⟩ := exists_frame_generation hF σ hσ
  exact hasPositionedCentralizerGeometry_of_frame hF hσ c (c.fusion hF hσ) hg

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.SquareGeometry.FieldWitnesses.PureField.InnerEscape.TwentyFive.Geometry
