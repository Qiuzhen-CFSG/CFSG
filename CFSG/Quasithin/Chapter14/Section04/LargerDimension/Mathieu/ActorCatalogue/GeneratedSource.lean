module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Assembly

/-!
# The original generated Mathieu subgroup and its cubic section

The native residual calculation retains its common design conjugator and
identifies S* ∨ X₂* ∨ X₃* with the literal hexad preimage. The source lifts
have these same images through H/O₂(H), so the actual ambient generated
subgroup has exactly that image. This connects its elementary order16 core,
cubic extension of S₆ and marked nonsplit 3.A₆ section to the original maps.
The existing SourceActors record and existence theorem remain unchanged.

Source: Aschbacher--Smith, Lemma 14.4.12, printed pp.1011--1012.
-/

@[expose] public section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue

universe u
variable {G : Type u} [Group G] [Finite G]

/-- The literal image of the ambient generated subgroup, before applying
any native parabolic recognition. -/
theorem generated_actors_image (H : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* Native.Model) (P B : Subgroup Native.Model) :
    ((((S : Subgroup H).map H.subtype) ⊔ liftedActor H e P ⊔
      borelActor (sourceBorel H e B)).subgroupOf H).map (starProjection H e) =
      (S : Subgroup H).map (starProjection H e) ⊔ twoResidual P ⊔ twoResidual B := by
  have hSH : (S : Subgroup H).map H.subtype ≤ H := map_subtype_le _
  have hPH := liftedActor_le H e P
  have hBH : borelActor (sourceBorel H e B) ≤ H := by
    rw [borelActor_eq_liftedActor]
    exact liftedActor_le H e B
  have hS : ((S : Subgroup H).map H.subtype).subgroupOf H = (S : Subgroup H) :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [subgroupOf_sup (sup_le hSH hPH) hBH, subgroupOf_sup hSH hPH,
    Subgroup.map_sup, Subgroup.map_sup, hS, liftedActor_image,
    borelActor_eq_liftedActor, liftedActor_image]

/-- A stronger constructed source output retaining the same selected actors,
common design coordinates and image of their original ambient join. -/
structure GeneratedSourceActors (H T : Subgroup G)
    (e : coreQuotient H ≃* Native.Model) (Sbar : Subgroup Native.Model)
    (v : Native.Space) where
  actors : SourceActors H T e Sbar v
  conjugator : Native.Model
  parabolic_position : actors.parabolic.map NativeParabolics.designProjection =
    NativeParabolics.Catalogue.partitionAt (NativeParabolics.designProjection conjugator)
  borel_position : actors.borel.map NativeParabolics.designProjection =
    NativeParabolics.Catalogue.pairAt (NativeParabolics.designProjection conjugator)
  native_generated : Sbar ⊔ twoResidual actors.parabolic ⊔ twoResidual actors.borel =
    NativeParabolics.hexadPreimage
      (NativeParabolics.designProjection conjugator • Sporadic.Mathieu.m22Hexad123)
  generated_image : ((T ⊔ liftedActor H e actors.parabolic ⊔
    borelActor (sourceBorel H e actors.borel)).subgroupOf H).map (starProjection H e) =
    NativeParabolics.hexadPreimage
      (NativeParabolics.designProjection conjugator • Sporadic.Mathieu.m22Hexad123)

/-- All original source actors and their generated subgroup are constructed
with one common native marking. No generated-image equality is an input. -/
theorem exists_generated_source_actors (H : Subgroup G) (S : Sylow 2 H)
    (e : coreQuotient H ≃* Native.Model) (v : Native.Space) (hv : v ≠ 0)
    (hfixed : ∀ s : S, Native.action (starProjection H e s.val) v = v) :
    Nonempty (GeneratedSourceActors H ((S : Subgroup H).map H.subtype) e
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
  obtain ⟨P, x, hSP, hPi, _, hdisjoint, hP, hB, h₁, h₂, h₃, hmove, _, h₁₂, h₁₃,
      h₂₃, hfamily, hD, _, _, _, _, _, _, _, hquot⟩ :=
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
  let a : SourceActors H T e (Sbar : Subgroup Native.Model) v :=
    ⟨B, P, hSB, hBC, hBi, hSP, hPi, hdisjoint, hmove, hcat,
      hn₁₂, hn₁₃, hn₂₃, hiso⟩
  refine ⟨⟨a, x, hP, hB, hD, ?_⟩⟩
  exact (generated_actors_image H S e P B).trans hD



namespace GeneratedSourceActors
variable {H T : Subgroup G} {e : coreQuotient H ≃* Native.Model}
  {Sbar : Subgroup Native.Model} {v : Native.Space}
  (a : GeneratedSourceActors H T e Sbar v)

/-- The actual D* through the source two-core projection. -/
def sourceImage : Subgroup Native.Model :=
  ((T ⊔ liftedActor H e a.actors.parabolic ⊔
    borelActor (sourceBorel H e a.actors.borel)).subgroupOf H).map (starProjection H e)

omit [Finite G] in
/-- The elementary order16 core belongs to the image of the original
ambient join, with its defining projection unchanged. -/
theorem sourceImage_twoCore :
    IsElementaryAbelian 2 (pCore 2 a.sourceImage) ∧
      Nat.card (pCore 2 a.sourceImage) = 16 :=
  ⟨NativeParabolics.GeneratedHexad.twoCore_elementary
      (NativeParabolics.conjugate_hexad_mem (NativeParabolics.designProjection a.conjugator))
      a.generated_image,
    NativeParabolics.GeneratedHexad.twoCore_card
      (NativeParabolics.conjugate_hexad_mem (NativeParabolics.designProjection a.conjugator))
      a.generated_image⟩

omit [Finite G] in
/-- The original D*/O₂(D*) maps onto S₆ with its literal surviving cubic
kernel. Its full A₆ preimage is the genuine nonsplit triple cover. -/
theorem sourceImage_quotient :
    ∃ q : coreQuotient a.sourceImage →* Equiv.Perm (Fin 6),
      Function.Surjective q ∧ Nat.card q.ker = 3 ∧
      Theory.GroupTheory.IsQuasisimple ((alternatingGroup (Fin 6)).comap q) ∧
      ∃ f : ((alternatingGroup (Fin 6)).comap q) →* alternatingGroup (Fin 6),
        Function.Surjective f ∧ f.ker = center ((alternatingGroup (Fin 6)).comap q) ∧
        Nat.card f.ker = 3 ∧
        (∃ eqv : ((alternatingGroup (Fin 6)).comap q) ≃* Atlas.Codes.HexEvenAutomorphisms,
          Atlas.Codes.hexEvenCoordinate.comp eqv.toMonoidHom = f) ∧
        ¬ ∃ j : alternatingGroup (Fin 6) →* ((alternatingGroup (Fin 6)).comap q),
          f.comp j = MonoidHom.id _ := by
  have hb := NativeParabolics.conjugate_hexad_mem
    (NativeParabolics.designProjection a.conjugator)
  refine ⟨NativeParabolics.GeneratedHexad.quotientProjection hb a.generated_image,
    NativeParabolics.GeneratedHexad.quotientProjection_surjective hb a.generated_image,
    NativeParabolics.GeneratedHexad.quotientProjection_kernel_card hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenSubgroup_isQuasisimple hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenProjection hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenProjection_surjective hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenProjection_kernel_eq_center hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenProjection_kernel_card hb a.generated_image,
    NativeParabolics.GeneratedHexad.exists_hexacode_equiv hb a.generated_image,
    NativeParabolics.GeneratedHexad.evenProjection_nonsplit hb a.generated_image⟩

end GeneratedSourceActors

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue
