module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixContainedSetup
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCentralizer
public import Theory.Representation.HexacodeAction.SixDimensionalRecognition.Normalizer

/-!
# The full original automizer in the prescribed hexacode coordinates

E.6.1 puts N_G(U) inside N_G(K). Thus the full original automizer normalizes
the actual K-image. The exact binary normalizer of the even hexacode image
extends the prescribed component marking to an injective full-actor map.
The component image is precisely the even subgroup, and every original
vector retains its coordinates.

Source: Aschbacher–Smith, 12.7.6 and 12.7.10, using K.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource Hexacode.SixDimensional Atlas.Codes
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Extend the same chosen hexacode chart to every actual ambient automizer. -/
theorem original_tripleSix_full_automizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction) :
    ∃ f : Automizer U →* HexAutomorphisms, Function.Injective f ∧
      (∀ k : K, f (U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩) =
        (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (inducedAutomizer U K).map f = hexSign.ker ∧
      (∀ (b : Automizer U) (u : U),
        (tripleSixPointCoordinates D a (b.val u)).toAdd =
          Hexacode.action (f b) (tripleSixPointCoordinates D a u).toAdd) := by
  let := D.elementary
  let c := tripleSixPointCoordinates D a
  let E : Additive U ≃ₗ[ZMod 2] hexacode :=
    LinearEquiv.ofBijective (c.toMonoidHom.toAdditiveLeft.toZModLinearMap 2) c.bijective
  let A := coordinateAction (automizerRepresentation U) E
  let B := inducedAutomizer U K
  have hn := (original_chosen_hypothesisE61_at h structural D).normalizer_le
  let I := K.subgroupOf (normalizer (U : Set G))
  let : I.Normal := (normal_subgroupOf_iff_le_normalizer D.normalizes).mpr hn
  let : B.Normal := (inferInstance : I.Normal).map
    U.normalizerMonoidHom.rangeRestrict U.normalizerMonoidHom.rangeRestrict_surjective
  have hAu (b : Automizer U) (u : U) :
      A b (c u).toAdd = (c (b.val u)).toAdd := by
    change E (automizerRepresentation U b (E.symm (E (Additive.ofMul u)))) = _
    rw [E.symm_apply_apply]
    rfl
  have hAk (k : K) : A (U.normalizerMonoidHom.rangeRestrict
      ⟨k, D.normalizes k.property⟩) =
      hexAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨u, hu⟩ := c.surjective (Multiplicative.ofAdd v)
    have hv : (c u).toAdd = v := congrArg Multiplicative.toAdd hu
    rw [← hv, hAu]
    have he := tripleSixPointCoordinates_conjugate D a k u
    have hh : c.symm (Multiplicative.ofAdd
        (Hexacode.evenAction (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k))
          (c u).toAdd)) = U.normalizerMonoidHom ⟨k, D.normalizes k.property⟩ u :=
      Subtype.ext he
    have hc := congrArg c hh
    rw [c.apply_symm_apply] at hc
    exact (congrArg Multiplicative.toAdd hc).symm
  have himage : B.map A = evenBinaryImage := by
    apply le_antisymm
    · rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      refine ⟨a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨n, hn⟩), ?_⟩
      exact (hAk ⟨n, hn⟩).symm
    · rintro _ ⟨g, rfl⟩
      obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K) (a.groupEquiv.symm g)
      refine ⟨U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩,
        ⟨⟨k, D.normalizes k.property⟩, k.property, rfl⟩, ?_⟩
      rw [hAk, hk, a.groupEquiv.apply_symm_apply]
      rfl
  have hmem (b : Automizer U) : A b ∈ hexAction.range := by
    rw [← normalizer_evenBinaryImage, ← himage]
    exact le_normalizer_map A ⟨b, by rw [B.normalizer_eq_top]; trivial, rfl⟩
  let j := A.codRestrict hexAction.range hmem
  let f := (MonoidHom.ofInjective hexAction_injective).symm.toMonoidHom.comp j
  have hf (b : Automizer U) : hexAction (f b) = A b :=
    MonoidHom.apply_ofInjective_symm hexAction_injective (j b)
  have hfk (k : K) : f (U.normalizerMonoidHom.rangeRestrict
      ⟨k, D.normalizes k.property⟩) =
      (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) k)).val := by
    apply hexAction_injective
    rw [hf, hAk]
  refine ⟨f, ?_, hfk, ?_, ?_⟩
  · intro b d hbd
    apply coordinateAction_injective (automizerRepresentation U) E
      (automizerRepresentation_injective U)
    rw [← hf, ← hf, hbd]
  · apply le_antisymm
    · rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
      rw [hfk ⟨n, hn⟩]
      exact (a.groupEquiv (QuotientGroup.mk' (pCore 2 K) ⟨n, hn⟩)).property
    · intro g hg
      obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (pCore 2 K)
        (a.groupEquiv.symm ⟨g, hg⟩)
      refine ⟨U.normalizerMonoidHom.rangeRestrict ⟨k, D.normalizes k.property⟩,
        ⟨⟨k, D.normalizes k.property⟩, k.property, rfl⟩, ?_⟩
      rw [hfk, hk, a.groupEquiv.apply_symm_apply]
  · intro b u
    exact (hAu b u).symm.trans (LinearEquiv.congr_fun (hf b).symm (c u).toAdd)

end CFSG.Quasithin.Chapter12.Section07
