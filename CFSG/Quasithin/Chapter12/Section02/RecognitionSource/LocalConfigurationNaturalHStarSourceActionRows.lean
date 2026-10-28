module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalHStarSourceResidualModels
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationNaturalMovementAt
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.NormalSupplementActions
public import Theory.Representation.PSL3Two.IrreducibleCatalogue
public import Theory.Representation.BinaryFullLinearRecognition
public import Theory.Alternating.OddCentralCovers

/-!
# The equal-overcomponent case of the original H-star restriction

Transport the literal LT conjugation action to the chosen space and its
original central quotient. Minimal parabolicity excludes the natural SL3
row, the nonsplit four-space (whose irreducible central quotient has dimension
three), the natural A6 row and the faithful irreducible hexacode row.
Together with the earlier model exclusions, only the orthogonal A5 central
action survives. Its actual L/O2(L) quotient is A5: the Schur multiplier bounds
the central kernel by two, while this quotient has trivial two-core.

When the H-star generating component equals its maximal overcomponent,
this proves the A5 identification and every chosen central action. The rank
bound and original movement conclusion of 12.2.18 are actual applications.
The guarded overcomponent construction now leaves proper containment or
this proved A5 case. Proper embeddings, the whole H-star core-module
restriction and the nonsolvable TI-pair exclusion remain with
qt-d-12213-hstar-natural; this module does not assert full 12.2.7 or 12.2.19.

Source: Aschbacher--Smith, 12.2.7, printed pp.797--798, and 12.2.18,
pp.800--801, using H.6.1 for the binary SL3 central quotient and K.1.1--3
for the alternating and hexacode normalizers. Concrete model proofs retain
their ATLAS attribution in the imported modules.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def joinCoordinates (D : ChosenModule T L V) :
    letI := D.elementary; D.space ≃ₗ[ZMod 2] Additive V := by
  let := D.elementary
  exact (MulEquiv.toAdditiveRight D.spaceEquiv).toLinearEquiv (ZMod.map_smul _)

private def joinAction (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) D.space := by
  let := D.elementary
  exact (joinCoordinates D).symm.conjRingEquiv.toMonoidHom.comp
    (RecognitionSource.chosenJoinAction D hT)

omit [Finite G] in
private theorem joinAction_component (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (l : L.subgroupOf (L ⊔ (T : Subgroup G))) :
    joinAction D hT l = D.chosenAction ((subgroupOfEquivOfLe le_sup_left) l) := by
  let := D.elementary
  apply LinearMap.ext
  intro v
  apply (joinCoordinates D).injective
  change (joinCoordinates D) ((joinCoordinates D).symm
    (RecognitionSource.chosenJoinAction D hT l ((joinCoordinates D) v))) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Additive.toMul.injective
  apply Subtype.ext
  change (l.val : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (l.val : G)⁻¹ =
    (D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction _ v)) : G)
  rw [D.spaceEquiv_apply,D.spaceEquiv_apply]
  rfl

omit [Finite G] in
private theorem join_supplement (L : Subgroup G) (T : Sylow 2 G) :
    L.subgroupOf (L ⊔ (T : Subgroup G)) ⊔
      ((T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) :
        Subgroup (L ⊔ (T : Subgroup G) : Subgroup G)) = ⊤ := by
  apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le le_sup_left]
  change L ⊔ ((T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G))).map _ = _
  rw [map_subgroupOf_eq_of_le le_sup_right, ← MonoidHom.range_eq_map, range_subtype]

private theorem faithful_of_equiv {A B X Y : Type*} [Group A] [Group B]
    [AddCommGroup X] [Module (ZMod 2) X] [AddCommGroup Y] [Module (ZMod 2) Y]
    {ρ : Representation (ZMod 2) A X} {σ : Representation (ZMod 2) B Y}
    (e : ActionEquiv ρ σ) (hf : Function.Injective σ) : Function.Injective ρ := by
  intro a b hab
  apply e.groupEquiv.injective
  apply hf
  apply LinearMap.ext
  intro y
  obtain ⟨x,rfl⟩ := e.linearEquiv.surjective y
  rw [← e.intertwines,← e.intertwines,hab]

private theorem quotient_not_solvable
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    ¬ Group.IsSolvable (L ⧸ pCore 2 L) := by
  let := h.quasisimple
  let : IsSimpleGroup ((L ⧸ pCore 2 L) ⧸ center (L ⧸ pCore 2 L)) := IsQuasisimple.simple
  let : Nontrivial (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk'_surjective (center (L ⧸ pCore 2 L))).nontrivial
  exact Group.IsPerfect.not_isSolvable _

/-- A chosen natural SL₃ module rules out minimal parabolicity of its literal join. -/
theorem ChosenModule.not_natural_three_of_minimalParabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤) :
    ¬ Nonempty (ActionEquiv D.quotientAction (specialLinearNatural (k := ZMod 2) 3)) := by
  rintro ⟨e⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let q : K →* (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk' (pCore 2 L)).comp (subgroupOfEquivOfLe le_sup_left).toMonoidHom
  exact ChapterB.not_minimalParabolic_of_quotient_natural_three _ K (join_supplement L T)
    (joinAction D hT) D.quotientAction
    (faithful_of_equiv e (specialLinearNatural_injective 3)) q
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
    (joinAction_component D hT) (quotient_not_solvable h) e hP

/-- The triple-six row is excluded using its actual faithful irreducible action. -/
theorem ChosenModule.not_tripleSix_of_minimalParabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    (e : (L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)
    (hd : Module.finrank (ZMod 2) D.space = 6)
    (hf : Function.Injective D.quotientAction) (hi : IsIrreducible D.quotientAction) : False := by
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let q : K →* (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk' (pCore 2 L)).comp (subgroupOfEquivOfLe le_sup_left).toMonoidHom
  exact ChapterB.not_minimalParabolic_of_quotient_hexacode _ K
    (joinAction D hT) D.quotientAction hf q
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
    (joinAction_component D hT) (quotient_not_solvable h) e hi hd hP

end CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

private def joinCentral (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Subrepresentation (joinAction D hT) where
  toSubmodule := (fixedSpace (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G)))).comap D.space.subtype
  apply_mem_toSubmodule := by
    let J := L ⊔ (T : Subgroup G)
    let K := L.subgroupOf J
    let : K.Normal := normal_subgroupOf_of_le_normalizer
      (sup_le L.le_normalizer D.sylow_normalizes_component)
    have he : fixedSpace (joinAction D hT) K =
        (fixedSpace (reducedRepresentation J) K).comap D.space.subtype := by
      ext v
      constructor
      · intro hv l
        have hh := hv l
        change joinAction D hT l v = v at hh
        rw [joinAction_component] at hh
        exact congrArg Subtype.val hh
      · intro hv l
        change joinAction D hT l v = v
        rw [joinAction_component]
        exact Subtype.ext (hv l)
    intro g v hv
    rw [← he] at hv ⊢
    exact (fixedSubrepresentation (joinAction D hT) K).apply_mem_toSubmodule g hv

private def joinCentralAction (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G)) :
    Representation (ZMod 2) (L ⊔ (T : Subgroup G) : Subgroup G) D.chosenCentralQuotient :=
  (joinCentral D hT).quotientRepresentation

omit [Finite G] in
private theorem joinCentralAction_component (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (l : L.subgroupOf (L ⊔ (T : Subgroup G))) :
    joinCentralAction D hT l = D.chosenCentralAction ((subgroupOfEquivOfLe le_sup_left) l) := by
  apply LinearMap.ext
  intro v
  induction v using Submodule.Quotient.induction_on with
  | _ v =>
    change Submodule.Quotient.mk (joinAction D hT l v) =
      Submodule.Quotient.mk (D.chosenAction _ v)
    rw [joinAction_component]

/-- The literal alternating-six central quotient excludes the H-star join. -/
theorem ChosenModule.not_natural_six_of_minimalParabolic
    (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤) :
    letI := D.actionCentralizer_normal
    ¬ Nonempty (ActionEquiv D.faithfulCentralAction (alternatingNatural 6)) := by
  let := D.actionCentralizer_normal
  rintro ⟨e⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let Q := L ⧸ (centralizer (V : Set G)).subgroupOf L
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let q : K →* Q := (QuotientGroup.mk' _).comp
    (subgroupOfEquivOfLe le_sup_left).toMonoidHom
  have hs : ¬ Group.IsSolvable Q := by
    intro hs
    let := hs
    let : Group.IsSolvable (alternatingGroup (Fin 6)) :=
      Group.isSolvable_of_surjective (f := e.groupEquiv.toMonoidHom) e.groupEquiv.surjective
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance
  have hf : Function.Injective D.faithfulCentralAction :=
    faithful_of_equiv e ((BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)).comp
      (alternatingGroup (Fin 6)).subtype_injective)
  exact ChapterB.not_minimalParabolic_of_quotient_natural_six _ K
    (joinCentralAction D hT) D.faithfulCentralAction hf q
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
    (joinCentralAction_component D hT) hs e hP

end CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

open scoped IsMulCommutative
private theorem three_central_dimension (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space ≤ 4) :
    Module.finrank (ZMod 2) D.chosenCentralQuotient = 3 := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let τ := D.centralQuotientAction.comp e.symm.toMonoidHom
  let : IsIrreducible τ := (irreducible_comp_surjective_iff _ e.symm.surjective _).mpr
    D.centralQuotientAction_irreducible
  have hf : Function.Injective τ :=
    (D.centralQuotientAction_injective e.isSimpleGroup).comp e.symm.injective
  have hn : ∃ g v, τ g v ≠ v := by
    obtain ⟨g,hg⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    by_contra! hh
    apply hg
    apply hf
    apply LinearMap.ext
    intro v
    simpa only [map_one,Module.End.one_apply] using hh g v
  have hdim : Module.finrank (ZMod 2) D.chosenCentralQuotient ≤ 4 :=
    (Submodule.finrank_quotient_le _).trans hd
  rcases BinaryLinearThree.IrreducibleCatalogue.classify_nontrivial τ hn with hc | hc | hc
  · obtain ⟨c⟩ := hc
    simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using c.toLinearEquiv.finrank_eq
  · obtain ⟨c⟩ := hc
    simpa [BinaryLinearThree.Vector, Matrix.PSL3Two.Fano.Vector] using c.toLinearEquiv.finrank_eq
  · obtain ⟨c⟩ := hc
    have hc := c.toLinearEquiv.finrank_eq.trans BinaryLinearThree.finrank_steinberg
    omega

/-- This excludes both the natural three-space and the nonsplit four-space:
the original central quotient is a faithful natural three-space in both cases. -/
theorem ChosenModule.not_small_linearThree_of_minimalParabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (hd : Module.finrank (ZMod 2) D.space ≤ 4) : False := by
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  have hf := D.centralQuotientAction_injective e.isSimpleGroup
  obtain ⟨a,b,hb⟩ := BinaryFullLinearRecognition.exists_natural_equiv D.centralQuotientAction hf e
    (three_central_dimension D e hd)
  let c : ActionEquiv D.centralQuotientAction (specialLinearNatural (k := ZMod 2) 3) := ⟨a,b,hb⟩
  let J := L ⊔ (T : Subgroup G)
  let K := L.subgroupOf J
  let : K.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  let q : K →* (L ⧸ pCore 2 L) :=
    (QuotientGroup.mk' (pCore 2 L)).comp (subgroupOfEquivOfLe le_sup_left).toMonoidHom
  exact ChapterB.not_minimalParabolic_of_quotient_natural_three _ K (join_supplement L T)
    (joinCentralAction D hT) D.centralQuotientAction hf q
    ((QuotientGroup.mk'_surjective _).comp (subgroupOfEquivOfLe le_sup_left).surjective)
    (joinCentralAction_component D hT) (quotient_not_solvable h) c hP
end CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter12.Section02
open ChapterB.QuasisimpleSource
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- A faithful A₅ central quotient identifies the actual two-core quotient.
The possible central kernel is killed by the order-two Schur multiplier and
triviality of the quotient's two-core. -/
theorem ChosenModule.core_five_of_faithful_five
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V) :
    letI := D.actionCentralizer_normal
    Nonempty ((L ⧸ (centralizer (V : Set G)).subgroupOf L) ≃* alternatingGroup (Fin 5)) →
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) := by
  let := D.actionCentralizer_normal
  rintro ⟨e⟩
  let Q := L ⧸ pCore 2 L
  let := h.quasisimple
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let r := e.toMonoidHom.comp D.coreToFaithful
  have hr : Function.Surjective r := e.surjective.comp D.coreToFaithful_surjective
  have hk : r.ker = center Q := by
    have hh := IsQuasisimple.comap_center_of_surjective r hr
    rw [alternatingGroup.center_eq_bot (by simp : 4 ≤ Nat.card (Fin 5)), MonoidHom.comap_bot] at hh
    exact hh
  let E : (Q ⧸ center Q) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r hr)
  have hd := GLS3.Chapter5.OddCentralCovers.center_card_dvd_two_of_nonexceptional
    5 (by decide) (by decide) (by decide) E
  have hz : center Q = ⊥ := by
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hd with hc | hc
    · exact (eq_bot_iff_card _).mpr hc
    · have hp : IsPGroup 2 (center Q) := IsPGroup.of_card (n := 1) (by simpa using hc)
      have hle : center Q ≤ pCore 2 Q := le_sSup ⟨inferInstance,hp⟩
      rw [pCore_quotient_pCore_eq_bot] at hle
      exact bot_unique hle
  exact ⟨QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hz.symm).trans E)⟩

/-- Exactly the orthogonal A₅ central action survives the seven chosen-module
rows when the chosen component and T form a minimal parabolic. -/
theorem ChosenModule.five_of_minimalParabolic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hT : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show
      (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)) ⊤)
    (rows : ModuleAlternatives1222 D) :
    letI := D.actionCentralizer_normal
    Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (ActionEquiv D.faithfulCentralAction (alternatingNatural 5)) := by
  let := D.actionCentralizer_normal
  have ha : Nonempty (ActionEquiv D.faithfulCentralAction (alternatingNatural 5)) := by
    rcases D.minimalParabolic_rows hT hP rows with hn | hn | hn | hn
    · exact (D.not_natural_three_of_minimalParabolic h hT hP hn).elim
    · obtain ⟨⟨e⟩,hd,_⟩ := hn
      exact (D.not_small_linearThree_of_minimalParabolic h hT hP e hd.le).elim
    · obtain ⟨n,hn,e⟩ := hn
      rcases hn with rfl | rfl
      · exact e
      · exact (D.not_natural_six_of_minimalParabolic hT hP e).elim
    · obtain ⟨⟨e⟩,hd,hf,hi⟩ := hn
      exact (D.not_tripleSix_of_minimalParabolic h hT hP e hd hf hi).elim
  obtain ⟨e⟩ := ha
  exact ⟨D.core_five_of_faithful_five h ⟨e.groupEquiv⟩,⟨e⟩⟩

namespace RecognitionSource
open ChapterI.Section06To08
variable {H X Y W : Subgroup G}

/-- The maximal case of source 12.2.7(2), with all other seven-module rows
excluded on their literal actions. The proper overcomponent case is separate. -/
theorem HStarGeneratingComponent.five_of_eq_at
    (C : HStarGeneratingComponent T L H X)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T Y) (he : X = Y)
    (E : ChosenModule T Y W) :
    letI := E.actionCentralizer_normal
    Nonempty ((Y ⧸ pCore 2 Y) ≃* alternatingGroup (Fin 5)) ∧
      Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5)) := by
  have hgen : Y ⊔ (T : Subgroup G) = H := he ▸ C.generates
  subst H
  exact E.five_of_minimalParabolic hY ((structural Y hY).2.2 W E).1
    (chosen_hstar_minimalParabolic_at h D structural hTI hH) (modules Y W hY E)

/-- Actual 12.2.18 rank application in the equal-overcomponent case. -/
theorem chosen_hstar_quotient_rank_of_eq_overcomponent_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (C : HStarGeneratingComponent T L H X)
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T X) :
    primeRank 2 (H ⧸ pCore 2 H) ≤ 2 := by
  obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural X hY).2.1
  exact chosen_hstar_quotient_rank_of_five_overcomponent_at h D structural modules hTI hH
    C le_rfl hY (C.five_of_eq_at h D structural modules hTI hH hY rfl E).1

/-- The corresponding original movement conclusion of 12.2.18; no rank
or quotient-identification callback remains in this equal-overcomponent branch. -/
theorem chosen_movement_of_eq_overcomponent_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (C : HStarGeneratingComponent T L H X)
    (hY : Hypothesis1223 KnownSimple.IsKnownSimple T X) : ¬ V ≤ H.pCoreIn 2 :=
  chosen_movement_of_quotient_rank_at h D structural hnone hTI hH
    (chosen_hstar_quotient_rank_of_eq_overcomponent_at h D structural modules hTI hH C hY)

/-- The same-G,T guarded construction now leaves only proper containment
or the actual A₅ quotient and orthogonal chosen central actions. -/
theorem chosen_hstar_residual_overcomponent_five_of_many_at
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    ∃ X Y : Subgroup G, HStarGeneratingComponent T L H X ∧
      X = (pResidual 2 H).map H.subtype ∧ X ≤ Y ∧
      Hypothesis1223 KnownSimple.IsKnownSimple T Y ∧
      (X < Y ∨ (X = Y ∧ Nonempty ((Y ⧸ pCore 2 Y) ≃* alternatingGroup (Fin 5)) ∧
        ∀ (W : Subgroup G) (E : ChosenModule T Y W), letI := E.actionCentralizer_normal
          Nonempty (ActionEquiv E.faithfulCentralAction (alternatingNatural 5)))) := by
  obtain ⟨X,Y,C,hres,hXY,hY⟩ := chosen_hstar_exists_residual_overcomponent_of_many_at
    h D structural modules hmany hnone hTI hH hs
  refine ⟨X,Y,C,hres,hXY,hY,?_⟩
  by_cases he : X = Y
  · obtain ⟨⟨W,⟨E⟩⟩⟩ := (structural Y hY).2.1
    exact Or.inr ⟨he,(C.five_of_eq_at h D structural modules hTI hH hY he E).1,
      fun W E => (C.five_of_eq_at h D structural modules hTI hH hY he E).2⟩
  · exact Or.inl (lt_of_le_of_ne hXY he)
end RecognitionSource
end CFSG.Quasithin.Chapter12.Section02
