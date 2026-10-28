module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerReduction
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleRows
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleAlternatingActor
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Model
public import Theory.Representation.SLHigherNaturalFirstCohomology.Elementary

/-!
# Four concrete models for the reducible block reduction

Failure of Sylow-normalizer containment produces a second maximal two-local,
so the guarded source classification applies with its original hypotheses.
A natural module has no fixed vector. In the four-dimensional A₇ row,
nonzero fixed space would give a faithful A₇ action on at most three binary
dimensions, contradicting its order. The other irreducible rows vanish too.

The remaining chosen modules are the binary SL₃ extension, the A₆ and A₈
augmentation cores, and the seven-dimensional G₂(2)′ Weyl module. Existing
central-cover recognition constructs these actual models. The A₆ actor is
still L/C_L(V), while the A₈ multiplier argument recovers L/O₂(L).
None of these markings asserts that the chosen V equals the module generated
by Ω₁Z(T), or identifies the canonical block module without further proof.

Source: Aschbacher–Smith 12.2.2(3), p.795, and 12.2.16, pp.799–800;
the specialized use in the reduction through 3.3.25(1), pp.586–600.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- An escaping Sylow normalizer supplies the actual multiple-overgroup guard. -/
theorem many_of_escape
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) :
    1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard := by
  have hT : (T : Subgroup G) ≠ ⊥ :=
    fun he => D.ne_bot (bot_unique (D.le_sylow.trans_eq he))
  have hN : IsTwoLocal (normalizer (T : Set G)) := ⟨T, hT, T.isPGroup', rfl⟩
  obtain ⟨N, hNN, hmax⟩ := Finite.exists_le_maximal hN
  apply Set.one_lt_ncard_iff_nontrivial_and_finite.mpr
  refine ⟨⟨normalizer (L : Set G), ⟨(maximal_unique h D).1,
    D.sylow_normalizes_component⟩, N, ⟨hmax, (T : Subgroup G).le_normalizer.trans hNN⟩, ?_⟩,
    Set.toFinite _⟩
  intro he
  exact hescape (he ▸ hNN)

private theorem fixed_quotientAction (D : ChosenModule T L V) (v : D.space)
    (hv : v ∈ G2WeylModel.Fixed D) (q : L ⧸ pCore 2 L) : D.quotientAction q v = v := by
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  exact Subtype.ext (hv ((subgroupOfEquivOfLe
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l))

/-- The natural linear row is incompatible with the original nonzero fixed space. -/
theorem not_natural_of_nonzero_fixed (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥) {n : ℕ} (hn : 2 ≤ n)
    (e : ActionEquiv D.quotientAction (specialLinearNatural (k := ZMod 2) n)) : False := by
  apply G2WeylModel.fixed_ne_bot D hne
  apply bot_unique
  intro v hv
  have hf : e.linearEquiv v ∈ OneCohomology.fixed (specialLinearNatural (k := ZMod 2) n) := by
    intro g
    obtain ⟨q,rfl⟩ := e.groupEquiv.surjective g
    rw [← e.intertwines, fixed_quotientAction D v hv]
  rw [OneCohomology.SLHigherNatural.fixed_eq_bot hn] at hf
  exact e.linearEquiv.injective (hf.trans e.linearEquiv.map_zero.symm)

/-- A₇ cannot act faithfully on the central quotient of a reducible four-space. -/
theorem not_alternatingSevenFour_of_nonzero_fixed (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (e : letI := D.actionCentralizer_normal
      (L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 7))
    (hd : Module.finrank (ZMod 2) D.space = 4) : False := by
  let := D.actionCentralizer_normal
  let : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (L ⧸ (centralizer (V : Set G)).subgroupOf L) := e.isSimpleGroup
  have hf : Function.Injective D.faithfulCentralAction := by
    apply D.faithfulCentralAction.ker_eq_bot_iff.mp
    apply D.faithfulCentralAction.normal_ker.eq_bot_or_eq_top.resolve_right
    intro ht
    apply D.centralAction_ne_one
    apply MonoidHom.ext
    intro l
    exact DFunLike.congr_fun (D.faithfulCentralAction.ker_eq_top_iff.mp ht)
      (QuotientGroup.mk' ((centralizer (V : Set G)).subgroupOf L) l)
  have hpos : 0 < Module.finrank (ZMod 2) (G2WeylModel.Fixed D) :=
    Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr
      (G2WeylModel.fixed_ne_bot D hne))
  have hsum := (G2WeylModel.Fixed D).finrank_quotient_add_finrank
  rw [hd] at hsum
  have hup : Module.finrank (ZMod 2) D.chosenCentralQuotient ≤ 3 := by
    change Module.finrank (ZMod 2) (D.space ⧸ G2WeylModel.Fixed D) ≤ 3
    omega
  let : Finite D.chosenCentralQuotient := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) D.chosenCentralQuotient) :=
    Finite.of_injective (fun f => (f : D.chosenCentralQuotient → D.chosenCentralQuotient))
      DFunLike.coe_injective
  have hc := Nat.card_le_card_of_injective D.faithfulCentralAction hf
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin,
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Module.finrank_linearMap] at hc
  norm_num [Nat.factorial] at hc
  interval_cases hh : Module.finrank (ZMod 2) D.chosenCentralQuotient <;> norm_num [hh] at hc

/-- The surviving full chosen-module models, before intrinsic block recognition. -/
inductive ReducibleModels (D : ChosenModule T L V) : Prop
  | linearThree (model : Section04.SmallFusion.SLThreeExtension D)
  | alternatingSix (model : letI := D.actionCentralizer_normal
      ActionEquiv D.faithfulAction (BinaryPermutation.alternatingCoreRepresentation (Fin 6)))
  | alternatingEight (model : ActionEquiv D.quotientAction
      (BinaryPermutation.alternatingCoreRepresentation (Fin 8)))
  | g2 (model : ActionEquiv D.quotientAction (Atlas.G2.Natural.OrthogonalCover.action (ZMod 2)))

/-- Construct the four marked models from the seven original source rows. -/
theorem reducibleModels_of_module_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (rows : ModuleAlternatives1222 D) : ReducibleModels D := by
  cases rows with
  | linear n hn e => exact (not_natural_of_nonzero_fixed D hne (by omega) e).elim
  | linearThreeExtension e hd _ =>
      obtain ⟨E⟩ := slThreeExtension_of_four_dimensional D e hd hne
      exact .linearThree E
  | linearFiveExterior _ _ hi => exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim
  | alternating n hlo hhi e =>
      obtain ⟨hn, ⟨E⟩⟩ := alternating_core_of_nonzero_fixed D hne n hlo hhi e
      rcases hn with rfl | rfl
      · exact .alternatingSix E
      · obtain ⟨E'⟩ := alternatingEight_quotientAction_of_faithfulAction D h.quasisimple E
        exact .alternatingEight E'
  | alternatingSevenFour e hd => exact (not_alternatingSevenFour_of_nonzero_fixed D hne e hd).elim
  | g2 e =>
      obtain ⟨E, _, _⟩ := g2_weyl_model D hne e
      exact .g2 E
  | tripleSix _ _ _ hi => exact (hne (fixedSubgroup_eq_bot_of_irreducible D hi)).elim

/-- Actual consumer of the guarded classification; the escape supplies its guard. -/
theorem reducibleModels_of_escape
    (modules : Theorem1222ModulesOfMany.{u} KnownSimple.IsKnownSimple)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hne : V ⊓ centralizer (L : Set G) ≠ ⊥)
    (hescape : ¬ normalizer (T : Set G) ≤ normalizer (L : Set G)) : ReducibleModels D :=
  reducibleModels_of_module_alternatives h D hne
    (modules G T L V (many_of_escape h D hescape) h D)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
