module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMixedBound

/-!
# Consuming the mixed source size theorem on the original natural pair

The abelian natural pair forces |T| at least 512. Its contradiction needs
only the mixed F.1.12 bound |T| at most 256, with all of that theorem's
source, quasithin and Sylow hypotheses supplied by the original pair.
Neither a parabolic identification nor a Borel identification is needed.

`NaturalMixedSizeInput` is the literal numerical contract also consumed by
Chapter10's `MixedZeroCore.MixedSizeInput`, without importing Chapter10.
Its unconditional proof belongs to the existing independent owner
qt-d-tensor-mixed-size-bound. This module is a conditional consumer,
not a proof of mixed recognition or source 6.1.19.
S5 escape, initial 6.1.4–5, omega escape and final 6.1.27 assembly remain
with qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith, F.1.12(I), printed pp.262–264, and 6.1.19,
printed p.675 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition

/-- The exact numerical mixed-source premise. This definition asserts no
recognition theorem; the existing mixed-size owner must supply its proof. -/
@[expose] def NaturalMixedSizeInput (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (K U S : Subgroup G),
    ChapterF.Source.HypothesisF11 ![K,U] S →
    IsQuasithin (ChapterF.Source.generated ![K,U] S) →
    Chapter1.IsSylowIn 2 S (ChapterF.Source.generated ![K,U] S) →
    Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) →
    Nonempty ((U ⧸ pCore 2 U) ≃* Equiv.Perm (Fin 3)) →
    ChapterF.Source.borel U S ≤ normalizer (S : Set G) → Nat.card S ≤ 256

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R B : Subgroup G}

/-- The weaker numerical input already excludes the original mixed pair.
All its structural premises are discharged here, on the literal subgroups. -/
theorem natural_cubic_amalgam_false_of_mixed_size
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hsize : NaturalMixedSizeInput G)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) : False := by
  let H := ChapterF.Source.generated ![L,B] (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) H := by
    refine ⟨T.subtype hTH, ?_⟩
    rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH]
  have heL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F, _, _, _, hcard, eL, _⟩ := hnat
    exact ⟨eL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hcard).some)⟩
  have hhi := hsize L B T hF (h.simpleQTKE.quasithin.subgroup H) hSyl heL ⟨e⟩
    (hF.cubic_borel_normalizes_S 1 e)
  have hlo := natural_cubic_amalgam_sylow_card_ge_512 h hnat hF e hBI hab
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
