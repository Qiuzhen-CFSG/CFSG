module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryMixedCubic

/-!
# The abelian mixed pair forces a Sylow subgroup larger than every model

Let V be the original natural layer and U its right-parabolic conjugate
span. The literal kernel C_LT(V) = O2(LT) puts the abelian U inside the
left two-core. Equality would make U normal in both actual parabolics,
contradicting the source pair's trivial generated two-core. Thus the
left core strictly contains U.

The checked cubic action gives |U| at least 64. Since the left core is a
two-group, its order is at least 128; its actual A5 or S5 quotient then
forces |T| at least 512. Every candidate mixed Borel has Sylow order at
most 256, so even an isomorphism of the whole Borel is now impossible.
No identification of either parabolic is needed for this size argument.

The final conditional theorem supplies all original source, quasithin and
Sylow premises to the existing Borel-recognition contract. That recognition
is not proved here. It, S5 parabolic escape, initial 6.1.4–5, omega escape
and unconditional 6.1.27 remain with qt-d-1222-rankone-recognition-natural.
The Chapter12 extension applies the result to the same original witness.

Source: Aschbacher–Smith 6.1.19, printed p.675, and F.1.12(I),
printed pp.262–264 (`refs/quasithin.pdf`).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R B : Subgroup G}

/-- The right span is strictly inside the full left core. Equality would
produce a nontrivial common normal two-subgroup of the source pair. -/
theorem natural_cubic_amalgam_right_span_lt_left_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    conjugateSpanBy (layer L R)
        (ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1) <
      (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  let X := L ⊔ (T : Subgroup G)
  let Q := X.pCoreIn 2
  have hr := natural_cubic_amalgam_right_quotient h hnat hF e hBI
  have hUQJ := (natural_cubic_amalgam_right_span h hnat hF e hr).2.1
  have hUT : U ≤ (T : Subgroup G) := hUQJ.trans
    ((natural_cubic_amalgam_right_core_le_line_sylow e hr).trans inf_le_left)
  have hUU := (natural_cubic_amalgam_right_elementary_span h hnat hF e hr hBI hab).1
  have hUV : U ≤ centralizer (layer L R : Set G) :=
    hUU.trans (hab.trans (centralizer_le (Escape.layer_le_U _ _ _)))
  have hUQ : U ≤ Q :=
    (le_inf (hUT.trans le_sup_right) hUV).trans_eq (local_layer_centralizer_eq_core h hnat)
  apply lt_of_le_of_ne hUQ
  intro he
  have hXQ : X ≤ normalizer (Q : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hzero : U = ⊥ := hF.common_normal_eq_bot U (hUT.trans le_sup_right) (by
    intro i
    fin_cases i
    · change ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 0 ≤ normalizer (U : Set G)
      rw [(natural_cubic_amalgam_products hF e).1]
      exact he.symm ▸ hXQ
    · exact le_normalizer_conjugateSpanBy (layer L R) J)
  exact h.nontrivial_action (bot_unique ((le_conjugateSpanBy (layer L R) J).trans_eq hzero))

/-- The abelian mixed branch forces Sylow order at least 512, using the
strict core inclusion, cubic orbit congruence and original left quotient. -/
theorem natural_cubic_amalgam_sylow_card_ge_512
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    512 ≤ Nat.card T := by
  let J := ChapterF.Source.parabolic ![L,B] (T : Subgroup G) 1
  let U := conjugateSpanBy (layer L R) J
  let X := L ⊔ (T : Subgroup G)
  have hr := natural_cubic_amalgam_right_quotient h hnat hF e hBI
  have h64 : 64 ≤ Nat.card U :=
    (natural_cubic_amalgam_right_cubic_sizes h hnat hF e hr hBI hab).1
  have hlt : Nat.card U < Nat.card (X.pCoreIn 2) :=
    Set.ncard_lt_ncard (natural_cubic_amalgam_right_span_lt_left_core h hnat hF e hBI hab)
  have hQ64 : 64 < Nat.card (pCore 2 X) := by
    have hh := h64.trans_lt hlt
    simpa only [pCoreIn,card_map_of_injective X.subtype_injective] using hh
  obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := X)).exists_card_eq
  have hk7 : 7 ≤ k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    (show 2^6 < 2^k from hk ▸ hQ64)
  have hQ128 : 128 ≤ Nat.card (pCore 2 X) := by
    rw [hk]
    exact Nat.pow_le_pow_right (by decide : 0 < 2) hk7
  have heL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,_,hF,eL,_⟩ := hnat
    exact ⟨eL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  have hcases := hF.mixed_first_core_size_cases heL.some e
  rw [(natural_cubic_amalgam_products hF e).1] at hcases
  change 128 ≤ Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) at hQ128
  rcases hcases with hcase | hcase <;> omega

/-- All four concrete whole Borels are excluded by their Sylow orders.
This uses no parabolic isomorphism or compatibility of its maps. -/
theorem natural_cubic_amalgam_not_mixed_borel
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    ¬ ChapterF.Source.MixedBorelModel (ChapterF.Source.commonBorel ![L,B] (T : Subgroup G)) := by
  intro hm
  have hlo := natural_cubic_amalgam_sylow_card_ge_512 h hnat hF e hBI hab
  have hhi := hF.sylow_card_le_of_mixedBorelModel hm
  omega

/-- Borel recognition alone now suffices to exclude the abelian mixed
branch. The original pair supplies the quasithin and Sylow hypotheses;
recognition itself remains an explicit source input. -/
theorem natural_cubic_amalgam_false_of_borel_recognition
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (recognition : ChapterF.Source.MixedA5S3BorelRecognition G)
    (hF : ChapterF.Source.HypothesisF11 ![L,B] (T : Subgroup G))
    (e : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hBI : B ≤ Escape.I (T : Subgroup G) L R)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) : False := by
  let H := ChapterF.Source.generated ![L,B] (T : Subgroup G)
  have hTH : (T : Subgroup G) ≤ H := le_sup_right
  have hSyl : Chapter1.IsSylowIn 2 (T : Subgroup G) H := by
    refine ⟨T.subtype hTH,?_⟩
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]
  have heL : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨F,_,_,_,hF,eL,_⟩ := hnat
    exact ⟨eL.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL.trans
      (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some)⟩
  exact natural_cubic_amalgam_not_mixed_borel h hnat hF e hBI hab
    (recognition L B T hF (h.simpleQTKE.quasithin.subgroup H) hSyl heL ⟨e⟩
      (hF.cubic_borel_normalizes_S 1 e))
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
