module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearLayerDecomposition
public import Theory.GroupTheory.GeneralizedFitting.CenterlessTwoQuotient
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.Representation.AlternatingFive.AmplifiedDeleted.CubicMultiplicity

/-!
# Multiplicity of the literal exceptional whole layer

The image of L in LT/C_LT(R₂(LT)) is its original quotient L/O₂(L):
the chosen module detects the kernel, while O₂(L) centralizes the whole
reduced group. This image is normal, its quotient is a two-group, and its
centralizer is trivial because the whole action has trivial two-core.
Thus the actual whole actor embeds in Aut(A₅)=S₅.

Transport the supplied ambient conjugation model to binary deleted-core
coordinates with the same quotient marking. The amplified displacement
bounds allow arbitrary mixing of the copies. A cubic elementary actor of
ratio at most two then bounds the full multiplicity by two.

Source: Aschbacher--Smith 5.1.3, 5.1.14(4) and 5.1.19,
refs/quasithin.pdf, printed pp.630--631,638,643--644.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
namespace RankOneModule
/-- The literal quotient acting faithfully on the entire reduced group. -/
abbrev wholeActor (T : Sylow 2 G) (L : Subgroup G) :=
  (L ⊔ (T : Subgroup G) : Subgroup G) ⧸ centralizer
    (ReducedModule (L ⊔ (T : Subgroup G)) : Set (L ⊔ (T : Subgroup G) : Subgroup G))
/-- The original centralizer quotient map. -/
def wholeProjection (T : Sylow 2 G) (L : Subgroup G) :
    (L ⊔ (T : Subgroup G) : Subgroup G) →* wholeActor T L := QuotientGroup.mk' _
/-- Restrict the original quotient map to L. -/
def wholeComponentProjection (T : Sylow 2 G) (L : Subgroup G) : L →* wholeActor T L :=
  (wholeProjection T L).comp (L.inclusion le_sup_left)

omit [Finite G] in
/-- The quotient action agrees with the original intrinsic conjugation. -/
theorem wholeAction_projection (x : (L ⊔ (T : Subgroup G) : Subgroup G)) :
    wholeAction T L (wholeProjection T L x) = reducedRepresentation _ x := by
  apply LinearMap.ext
  intro v
  apply Additive.toMul.injective
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply _ _ _ _ x v

omit [Finite G] in
/-- Component restriction commutes with the literal quotient projection. -/
theorem wholeAction_componentProjection (l : L) :
    wholeAction T L (wholeComponentProjection T L l) = wholeComponentAction T L l :=
  wholeAction_projection _

omit [Finite G] in
/-- Factoring by the exact centralizer makes the whole action faithful. -/
theorem wholeAction_faithful : Function.Injective (wholeAction T L) :=
  NormalElementaryQuotient.representation_injective _ _ _ _

end RankOneModule
namespace ChosenModule
open RankOneModule

/-- The chosen subgroup detects the component kernel on the whole module. -/
theorem wholeComponentProjection_ker (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    (wholeComponentProjection T L).ker = pCore 2 L := by
  apply le_antisymm
  · intro l hl
    apply (D.alternatingFive_chosen_centralizer e).le
    intro v hv
    obtain ⟨w,hw,he⟩ := D.le_reduced hv
    have hact : wholeComponentAction T L l = 1 := by
      rw [← wholeAction_componentProjection,show wholeComponentProjection T L l = 1 from hl,
        map_one]
    have hh := congrArg (fun a : wholeSpace T L => (a.toMul.val : G))
      (LinearMap.congr_fun hact (Additive.ofMul ⟨w,hw⟩))
    change (l : G) * (w : G) * (l : G)⁻¹ = (w : G) at hh
    change (w : G) = v at he
    rw [he] at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro l hl
    apply wholeAction_faithful
    rw [wholeAction_componentProjection,map_one]
    exact wholeComponentAction_core D.sylow_normalizes_component hl

omit [Finite G] in
/-- Relative normality of L in LT descends to its actual quotient image. -/
theorem wholeComponentProjection_normal (D : ChosenModule T L V) :
    (wholeComponentProjection T L).range.Normal := by
  let : (L.subgroupOf (L ⊔ (T : Subgroup G))).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer D.sylow_normalizes_component)
  rw [wholeComponentProjection,MonoidHom.range_comp,inclusion_range]
  exact (inferInstance : ((L.subgroupOf (L ⊔ (T : Subgroup G))).map
    (QuotientGroup.mk' (centralizer (ReducedModule (L ⊔ (T : Subgroup G)) :
      Set (L ⊔ (T : Subgroup G) : Subgroup G))))).Normal)

/-- The original L/O₂(L) marking transported by the first isomorphism theorem. -/
def wholeComponentMarking (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    (wholeComponentProjection T L).range ≃* alternatingGroup (Fin 5) :=
  (QuotientGroup.quotientKerEquivRange (wholeComponentProjection T L)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (D.wholeComponentProjection_ker e)).trans e)

/-- The transported marking retains the literal quotient representatives. -/
theorem wholeComponentMarking_projection (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) (l : L) :
    D.wholeComponentMarking e ((wholeComponentProjection T L).rangeRestrict l) =
      e (QuotientGroup.mk' (pCore 2 L) l) := by
  change e (QuotientGroup.quotientMulEquivOfEq _
    ((QuotientGroup.quotientKerEquivRange _).symm
      ((wholeComponentProjection T L).rangeRestrict l))) = _
  congr 1
  have hh : (QuotientGroup.quotientKerEquivRange (wholeComponentProjection T L))
      (QuotientGroup.mk' _ l) = (wholeComponentProjection T L).rangeRestrict l := rfl
  rw [← hh,MulEquiv.symm_apply_apply]
  rfl

omit [Finite G] in
/-- The Sylow supplement makes the quotient by the component image a two-group. -/
theorem wholeComponent_quotient_two (D : ChosenModule T L V) :
    let := D.wholeComponentProjection_normal
    IsPGroup 2 (wholeActor T L ⧸ (wholeComponentProjection T L).range) := by
  let := D.wholeComponentProjection_normal
  let J := L ⊔ (T : Subgroup G)
  let X := L.subgroupOf J
  let q := wholeProjection T L
  let K := (wholeComponentProjection T L).range
  let : X.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer D.sylow_normalizes_component)
  have htwo : IsPGroup 2 (J ⧸ X) := by
    apply isPGroup_quotient_of_sup_eq_top X ((T : Subgroup G).subgroupOf J)
      T.isPGroup'.comap_subtype
    rw [← subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
  have hx : X ≤ K.comap q := by
    intro x hx
    exact ⟨⟨x,hx⟩,rfl⟩
  apply htwo.of_surjective (QuotientGroup.map X K q hx)
  apply QuotientGroup.map_surjective_of_surjective
  exact (QuotientGroup.mk'_surjective K).comp (QuotientGroup.mk'_surjective _)


/-- The component centralizer is a normal two-subgroup, hence trivial. -/
theorem wholeComponent_centralizer (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) :
    centralizer ((wholeComponentProjection T L).range : Set (wholeActor T L)) = ⊥ := by
  let := D.wholeComponentProjection_normal
  let K := (wholeComponentProjection T L).range
  let a := D.wholeComponentMarking e
  have hz : center K = ⊥ := by
    apply bot_unique
    intro x hx
    have hh := (centerCongr a ⟨x,hx⟩).property
    change a x ∈ center (alternatingGroup (Fin 5)) at hh
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at hh
    exact a.map_eq_one_iff.mp hh
  have hp := centralizer_isPGroup_of_centerless_quotient K hz D.wholeComponent_quotient_two
  have hle : centralizer (K : Set (wholeActor T L)) ≤ pCore 2 (wholeActor T L) :=
    le_sSup ⟨inferInstance,hp⟩
  exact bot_unique (hle.trans_eq isPReduced_reducedPSubgroup.quotient_pCore_eq_bot)


/-- The A₅ inside the quotient acts via the original marking. -/
theorem wholeAction_componentMarking (D : ChosenModule T L V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (g : alternatingGroup (Fin 5)) :
    wholeAction T L ((D.wholeComponentMarking e).symm g).val =
      wholeMarkedAction D.sylow_normalizes_component e g := by
  obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  dsimp only [Function.comp_apply]
  rw [wholeMarkedAction_mk,← D.wholeComponentMarking_projection e l,
    MulEquiv.symm_apply_apply]
  exact wholeAction_componentProjection l

/-- Multiplicity on the entire layer is bounded by its actual cubic ratio. -/
theorem rankOne_whole_multiplicity_le_two_of_cubicRatio (D : ChosenModule T L V)
    (hq : BinaryOffender.cubicRatio (wholeAction T L) ≤ 2)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)) {k : ℕ}
    (c : AlternatingFive.AmplifiedDeleted.Coordinates (ι := Fin k)
      (wholeMarkedAction D.sylow_normalizes_component e)) : k ≤ 2 := by
  let := D.wholeComponentProjection_normal
  obtain ⟨p,hp,hcov⟩ := AlternatingFive.exists_symmetric_actor_of_centralizer_eq_bot
    (wholeAction T L) (wholeComponentProjection T L).range (D.wholeComponentMarking e)
    (D.wholeComponent_centralizer e)
  apply AlternatingFive.deleted_multiplicity_le_two_of_faithful_symmetric_action
    (wholeAction T L) (wholeMarkedAction D.sylow_normalizes_component e) p hp c
    ?_ hq
  intro q g v
  simpa only [D.wholeAction_componentMarking e] using hcov q g v


/-- Recover binary coordinates from the literal ambient conjugation model. -/
theorem whole_coordinates_of_model (D : ChosenModule T L V) {k : ℕ}
    (hm : Chapter6.Source.IsConjugationModel L (wholeReduced T L) (Chapter6.Source.a5Copies k)) :
    ∃ e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5),
      Nonempty (AlternatingFive.AmplifiedDeleted.Coordinates (ι := Fin k)
        (wholeMarkedAction D.sylow_normalizes_component e)) := by
  obtain ⟨e,f,hf⟩ := hm
  let b := wholeSpaceEquiv T L
  let z : wholeSpace T L ≃+ (Fin k → BinaryPermutation.natural (Fin 5)) :=
    (AddEquiv.additiveMultiplicative (wholeSpace T L)).symm.trans
      ((b.trans f).toAdditive.trans
        (AddEquiv.additiveMultiplicative (Fin k → BinaryPermutation.natural (Fin 5))))
  let c : wholeSpace T L ≃ₗ[ZMod 2] (Fin k → BinaryPermutation.natural (Fin 5)) :=
    LinearEquiv.ofBijective (z.toAddMonoidHom.toZModLinearMap 2) z.bijective
  have hc (l : L) (v : wholeSpace T L) : c (wholeComponentAction T L l v) =
      Chapter6.Source.a5Copies k (e (QuotientGroup.mk' (pCore 2 L) l)) (c v) := by
    apply Multiplicative.ofAdd.injective
    apply f.symm.injective
    apply Subtype.val_injective
    change (f.symm (f (b (Multiplicative.ofAdd (wholeComponentAction T L l v)))) : G) = _
    rw [f.symm_apply_apply]
    change (b (Multiplicative.ofAdd (wholeComponentAction T L l v)) : G) =
      (f.symm (Multiplicative.ofAdd (Chapter6.Source.a5Copies k
        (e (QuotientGroup.mk' (pCore 2 L) l)) (f (b (Multiplicative.ofAdd v))).toAdd)) : G)
    rw [hf]
    rfl
  let d := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  refine ⟨e,⟨⟨c.trans (LinearEquiv.piCongrRight fun _ => d.symm),?_⟩⟩⟩
  intro g v
  obtain ⟨l,rfl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective _) g
  dsimp only [Function.comp_apply]
  rw [wholeMarkedAction_mk]
  apply funext
  intro i
  change d.symm (c (wholeComponentAction T L l v) i) =
    BinaryPermutation.coreRepresentation (Fin 5)
      (e (QuotientGroup.mk' (pCore 2 L) l)).val (d.symm (c v i))
  rw [hc]
  apply d.injective
  rw [d.apply_symm_apply]
  change _ = BinaryPermutation.coreEquivNatural (Fin 5) (by decide) _
  rw [BinaryPermutation.coreEquivNatural_equivariant]
  rw [show BinaryPermutation.coreEquivNatural (Fin 5) (by decide) (d.symm (c v i)) =
    c v i from d.apply_symm_apply _]
  rfl

/-- Bound the exact number of copies in any model of the literal whole layer. -/
theorem rankOne_linear_layer_multiplicity_of_cubicRatio (D : ChosenModule T L V) {k : ℕ}
    (heq : wholeReduced T L = commutatorLayer T L)
    (hm : Chapter6.Source.IsConjugationModel L (commutatorLayer T L) (Chapter6.Source.a5Copies k))
    (hq : BinaryOffender.cubicRatio (wholeAction T L) ≤ 2) : k ≤ 2 := by
  rw [← heq] at hm
  obtain ⟨e,⟨c⟩⟩ := D.whole_coordinates_of_model hm
  exact D.rankOne_whole_multiplicity_le_two_of_cubicRatio hq e c

/-- The multiplicity contract applied to the actual outside HStar witness. -/
theorem rankOne_linear_layer_multiplicity (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L) {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) {k : ℕ}
    (heq : wholeReduced T L = commutatorLayer T L)
    (hm : Chapter6.Source.IsConjugationModel L (commutatorLayer T L) (Chapter6.Source.a5Copies k)) :
    k ≤ 2 :=
  D.rankOne_linear_layer_multiplicity_of_cubicRatio heq hm
    (D.rankOne_whole_cubicRatio_le_two h hH)

end ChosenModule
end CFSG.Quasithin.Chapter12.Section02
