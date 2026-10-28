module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Source

/-!
# The three actual Mathieu actors

Construct the native Borel from the fixed binary point, apply the complete
native parabolic calculation, and lift all residuals through H/O₂(H). This
proves the exhaustive source X-family and its pairwise distinctness. The
overlap quotient is transported through the same original projection.
The native calculation retains the cubic layer of the hexad group.
The separate module calculation selects the two members of Y.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The constructed actors with their exact source maps and quotient. This is
an output of the native calculations, never a classification hypothesis. -/
structure SourceActors (H : Subgroup G) (T : Subgroup G)
    (e : coreQuotient H ≃* Native.Model) (Sbar : Subgroup Native.Model)
    (v : Native.Space) where
  borel : Subgroup Native.Model
  parabolic : Subgroup Native.Model
  sylow_le_borel : Sbar ≤ borel
  borel_fixes : borel ≤ Native.pointCentralizer v
  borel_index : (Sbar).relIndex borel = 3
  sylow_le_parabolic : Sbar ≤ parabolic
  parabolic_index : (Sbar).relIndex parabolic = 3
  parabolic_disjoint : Disjoint NativeParabolics.cubic parabolic
  parabolic_moves : ¬ twoResidual parabolic ≤ Native.pointCentralizer v
  catalogue : XFamily H T =
    {firstActor H, liftedActor H e parabolic, borelActor (sourceBorel H e borel)}
  first_ne_second : firstActor H ≠ liftedActor H e parabolic
  first_ne_third : firstActor H ≠ borelActor (sourceBorel H e borel)
  second_ne_third : liftedActor H e parabolic ≠ borelActor (sourceBorel H e borel)
  overlap : Nonempty (coreQuotient
    (firstActor H ⊔ liftedActor H e parabolic ⊔ T) ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))

/-- All three actual residual actors and the source overlap quotient are
constructed from the genuine quotient marking and its Sylow-fixed point. -/
theorem exists_source_actors (H : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* Native.Model) (v : Native.Space) (hv : v ≠ 0)
    (hfixed : ∀ s : S, Native.action (starProjection H e s.val) v = v) :
    Nonempty (SourceActors H ((S : Subgroup H).map H.subtype) e
      ((S : Subgroup H).map (starProjection H e)) v) := by
  let q := starProjection H e
  let T := (S : Subgroup H).map H.subtype
  let Sbar : Sylow 2 Native.Model := S.mapSurjective (f := q) (starProjection_surjective H e)
  have hfix : ∀ s : Sbar, Native.action s.val v = v := by
    rintro ⟨s, hs⟩
    obtain ⟨t, ht, rfl⟩ := hs
    exact hfixed ⟨t, ht⟩
  obtain ⟨qC, i, _, _, hSB, hBC, hBi, _⟩ :=
    (Native.pointCentralizer_borel Sbar v hv hfix).2.2
  let B := Native.pointBorel v qC i
  obtain ⟨P, _, hSP, hPi, _, hdisjoint, _, _, h₁, h₂, h₃, hmove, _, h₁₂, h₁₃,
      h₂₃, hfamily, _, _, _, _, _, _, _, _, hquot⟩ :=
    NativeParabolics.exists_native_parabolics Sbar hv B hSB hBC hBi
  have hfirst : firstActor H = liftedActor H e (twoResidual (pCore 3 Native.Model)) :=
    firstActor_eq_liftedActor H e
  have hsecond : liftedActor H e (twoResidual P) = liftedActor H e P :=
    liftedActor_residual H e P
  have hthird : liftedActor H e (twoResidual B) = borelActor (sourceBorel H e B) :=
    (liftedActor_residual H e B).trans (borelActor_eq_liftedActor H e B).symm
  have hcat := liftedActor_catalogue H S e _ _ _ hfamily
  rw [← hfirst, hsecond, hthird] at hcat
  have hn₁₂ : firstActor H ≠ liftedActor H e P := by
    rw [hfirst, ← hsecond]
    exact liftedActor_ne H e h₁.residual_eq h₂.residual_eq h₁₂
  have hn₁₃ : firstActor H ≠ borelActor (sourceBorel H e B) := by
    rw [hfirst, ← hthird]
    exact liftedActor_ne H e h₁.residual_eq h₃.residual_eq h₁₃
  have hn₂₃ : liftedActor H e P ≠ borelActor (sourceBorel H e B) := by
    rw [← hsecond, ← hthird]
    exact liftedActor_ne H e h₂.residual_eq h₃.residual_eq h₂₃
  have hiso := liftedActor_overlap H S e _ _ h₁.residual_eq h₂.residual_eq hquot
  rw [← hfirst, hsecond] at hiso
  exact ⟨⟨B, P, hSB, hBC, hBi, hSP, hPi, hdisjoint, hmove, hcat,
    hn₁₂, hn₁₃, hn₂₃, hiso⟩⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
