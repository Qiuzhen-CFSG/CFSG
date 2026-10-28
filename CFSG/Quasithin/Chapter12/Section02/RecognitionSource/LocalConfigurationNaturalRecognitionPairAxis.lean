module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalRecognition
public import CFSG.Quasithin.ChapterI.Section06To08.PairElementary.FullAxis
public import CFSG.Quasithin.ChapterI.Section06To08.TIConjugates

/-!
# Transporting the TI-pair axis to the original LT action

The opposite mutual normalizer centralizes a nonidentity point of V. NoEscape
therefore places it in N_G(L), as well as N_G(V). An explicit comparison of
the common normalizer's action with LT then transports its full hyperplane
radical to the literal chosenJoinLinearAction image. The nonidentity point
is obtained from the already proved bound |V| > 4.

These conditional theorems apply full-action recognition and the original
natural-marking consumer. They do not assert source 12.2.20: constructing a
hyperplane pair and proving the common-normalizer comparison remain source
obligations. The original marking remains a separate input.
No natural row, irreducibility or invariant odd subgroup is assumed here.
Source: Aschbacher–Smith, 12.2.10 and the construction before 12.2.20,
printed pp.798,802; I.6.2(2a), pp.424–425.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
theorem pair_opposite_normalizer_le_component_normalizer
    (hnone : NoEscape L V) (A : Subgroup G) (hVA : Disjoint V A)
    (hU : V ⊓ normalizer (A : Set G) ≠ ⊥) :
    A ⊓ normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hU
  have hu1 : (u : G) ≠ 1 := fun he => hu (Subtype.ext he)
  intro b hb
  exact hnone u u.property.1 hu1 (mem_centralizer_singleton_iff.mpr
    (ti_pair_commute_of_mutual_normalizers V A hVA u.property.1 u.property.2 hb.1 hb.2).symm)

theorem chosen_pair_axis_ne_bot
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (A : Subgroup G)
    (f : letI := D.elementary; Module.Dual (ZMod 2) (Additive V))
    (hker : ∀ v : Additive V, f v = 0 ↔ (v.toMul : G) ∈ normalizer (A : Set G)) :
    V ⊓ normalizer (A : Set G) ≠ ⊥ := by
  let := D.elementary
  intro hbot
  have hfi : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro v hv
    have hv1 : (v.toMul : G) = 1 := mem_bot.mp (hbot ▸
      (show (v.toMul : G) ∈ V ⊓ normalizer (A : Set G) from
        ⟨v.toMul.property, (hker v).mp hv⟩))
    exact congrArg Additive.ofMul (Subtype.ext hv1)
  have hc := Nat.card_le_card_of_injective f hfi
  rw [Nat.card_congr Additive.toMul, Nat.card_zmod] at hc
  have hlarge := chosen_card_gt_four h D
  omega

theorem chosenFullAxis_of_pair_axis_and_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (g : G) (hneq : V.map (MulAut.conj g).toMonoidHom ≠ V)
    (f : letI := D.elementary; Module.Dual (ZMod 2) (Additive V)) (hf : f ≠ 0)
    (hker : ∀ v : Additive V, f v = 0 ↔
      (v.toMul : G) ∈ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (hcompare : ∀ n ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G),
      ∃ j ∈ L ⊔ (T : Subgroup G), ∀ v ∈ V, n * v * n⁻¹ = j * v * j⁻¹) :
    ChosenFullAxis D hT := by
  let := D.elementary
  let A := V.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hVA : Disjoint V A := ((hTI.eq_or_disjoint_conjugate g).resolve_left hneq).symm
  have hA : IsTISubgroup A := hTI.map_equiv (MulAut.conj g)
  have hc : Nat.card V = Nat.card A := (card_map_of_injective (MulAut.conj g).injective).symm
  have hB := pair_opposite_normalizer_le_component_normalizer hnone A hVA
    (chosen_pair_axis_ne_bot h D A f hker)
  refine ⟨f, hf, ?_⟩
  rw [← pairNormalizerLinearAction_range_eq_radical V A hVA hTI hA hc f hf hker]
  rintro a ⟨b, rfl⟩
  obtain ⟨j, hj, he⟩ := hcompare b ⟨hB b.property, b.property.2⟩
  refine ⟨⟨j, hj⟩, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  change j * (v.toMul : G) * j⁻¹ = (b : G) * (v.toMul : G) * (b : G)⁻¹
  exact (he v.toMul v.toMul.property).symm

theorem chosenFullAxis_of_pair_hyperplane_and_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom)))
    (hcompare : ∀ n ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G),
      ∃ j ∈ L ⊔ (T : Subgroup G), ∀ v ∈ V, n * v * n⁻¹ = j * v * j⁻¹) :
    ChosenFullAxis D hT := by
  let := D.elementary
  obtain ⟨f, hf, hker⟩ := pairAxisSpace_exists_form V _ hhyper
  have hneq : V.map (MulAut.conj g).toMonoidHom ≠ V := by
    intro he
    apply hf
    apply LinearMap.ext
    intro v
    apply (hker v).mpr
    rw [he]
    exact V.le_normalizer v.toMul.property
  exact chosenFullAxis_of_pair_axis_and_comparison h D hT hnone hTI g hneq f hf hker hcompare

theorem chosenJoinLinearAction_range_eq_top_of_pair_hyperplane_and_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom)))
    (hcompare : ∀ n ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G),
      ∃ j ∈ L ⊔ (T : Subgroup G), ∀ v ∈ V, n * v * n⁻¹ = j * v * j⁻¹) :
    letI := D.elementary
    (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤ :=
  chosenJoinLinearAction_range_eq_top_of_full_axis_at h D structural
    (chosenFullAxis_of_pair_hyperplane_and_comparison h D _ hnone hTI g hhyper hcompare)

theorem natural_action_of_pair_hyperplane_and_comparison
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : Group.IsSolvable H) (hm : ¬ V ≤ H.pCoreIn 2)
    (g : G)
    (hhyper : letI := D.elementary
      IsCoatom (pairAxisSpace V (V.map (MulAut.conj g).toMonoidHom)))
    (hcompare : ∀ n ∈ normalizer (L : Set G) ⊓ normalizer (V : Set G),
      ∃ j ∈ L ⊔ (T : Subgroup G), ∀ v ∈ V, n * v * n⁻¹ = j * v * j⁻¹)
    (markingStep : (letI := D.elementary
      (chosenJoinLinearAction D (((structural L h).2.2 V D).1)).range = ⊤) →
      ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Nonempty (ChapterB.QuasisimpleSource.ActionEquiv D.quotientAction
        (Representation.specialLinearNatural (k := ZMod 2) d))) :
    ∃ d, (3 ≤ d ∧ d ≤ 5) ∧ Chapter6.Source.IsConjugationModel L V
      (Representation.specialLinearNatural (k := ZMod 2) d) := by
  exact natural_action_of_solvable_axis_and_marking h D structural hnone hTI hH hs hm
    (fun hnone hTI _ _ _ =>
      chosenFullAxis_of_pair_hyperplane_and_comparison h D _ hnone hTI g hhyper hcompare)
    markingStep

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
