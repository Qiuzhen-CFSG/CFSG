module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.ThompsonFusion
public import Theory.Representation.BinaryPermutation.FourBlockThompson
public import Theory.GroupAction.ModelConjugation

/-!
# Thompson control of the original four-block preimage

When C_V(L) is nontrivial, the original augmentation cover supplies core
coordinates compatible with both conjugation by L and the original map
V -> V/C_V(L). Transport the full LT-action through these coordinates.
Its kernel is the original Q, since C_LT(V)=Q.

Let R be the full preimage of the two block Klein groups in this action.
The intrinsic core calculation excludes every nontrivial offender image,
so J(R) lies in Q. Thompson heredity gives J(R)=J(Q), and original
normalizer uniqueness gives N_G(R)<=M. The marked L-action fills the
radical, giving |R:Q|=16. Sylow conjugacy inside LT places R in the original
T while retaining the actual conjugator, Q, index and normalizer control.

This proves the four-block Thompson calculation needed by 12.6.1(4) in
the nontrivial fixed-space branch. Identifying and aligning the source
L1 and its R1 in the contrary-fusion argument remain necessary for
12.6.19; full 12.6.2 and fixed-space elimination 12.6.23 are not asserted.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4), printed p.823, and the fusion argument 12.6.19, p.828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open Theory.SpecificGroups.SymmetricEight
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

@[expose] noncomputable def coreMarkedAction
    (h : LT T L ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) :
    LT T L →* MulAut (Multiplicative (core (Fin 8))) :=
  Theory.GroupAction.ModelConjugation.action (LT T L) V h E.toAddEquiv.toMultiplicativeRight

@[expose] noncomputable def fourBlockPreimage
    (h : LT T L ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) : Subgroup G :=
  (FourBlockThompson.radicalImage.comap (coreMarkedAction h E)).map (LT T L).subtype

private theorem coreMarkedAction_ker
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) :
    (coreMarkedAction (sup_le H.chosen.normalizes hTV) E).ker = pCore 2 (LT T L) := by
  apply map_injective (LT T L).subtype_injective
  change (Theory.GroupAction.ModelConjugation.action (LT T L) V
    (sup_le H.chosen.normalizes hTV) E.toAddEquiv.toMultiplicativeRight).ker.map
      (LT T L).subtype = _
  exact (Theory.GroupAction.ModelConjugation.action_ker_map (LT T L) V
    (sup_le H.chosen.normalizes hTV) E.toAddEquiv.toMultiplicativeRight).trans
      (H.join_centralizer_eq_core hTV)

/-- Thompson replacement controls the full original preimage of the four-block radical. -/
theorem SourceHypothesis.fourBlockPreimage_thompson
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) :
    let R := fourBlockPreimage (sup_le H.chosen.normalizes hTV) E
    Q T L ≤ R ∧ R ≤ LT T L ∧ IsPGroup 2 R ∧
      elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) ∧
      normalizer (R : Set G) ≤ M L := by
  let J := LT T L
  have hVJ : V ≤ J := H.chosen.le_component.trans le_sup_left
  have hJV : J ≤ normalizer (V : Set G) := sup_le H.chosen.normalizes hTV
  let U := V.subgroupOf J
  let : U.Normal := normal_subgroupOf_of_le_normalizer hJV
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hVJ
  let e : U ≃* Multiplicative (core (Fin 8)) :=
    (subgroupOfEquivOfLe hVJ).trans E.toAddEquiv.toMultiplicativeRight
  let a := coreMarkedAction hJV E
  let S := FourBlockThompson.radicalImage.comap a
  let R := S.map J.subtype
  have hk : a.ker = pCore 2 J := coreMarkedAction_ker H hTV E
  have hQS : a.ker ≤ S := comap_mono bot_le
  have hQR : Q T L ≤ R := by
    change (pCore 2 J).map J.subtype ≤ S.map J.subtype
    exact map_mono (hk ▸ hQS)
  have hUS : U ≤ S := by
    intro u hu
    apply hQS
    rw [show a = Theory.GroupAction.ModelConjugation.action J V hJV
      E.toAddEquiv.toMultiplicativeRight from rfl,
      Theory.GroupAction.ModelConjugation.action_ker]
    intro v hv
    exact congrArg V.subtype
      (mul_comm (⟨v,hv⟩ : V) (⟨u,hu⟩ : V))
  have hka : a.ker = centralizer (U : Set J) := by
    rw [show a = Theory.GroupAction.ModelConjugation.action J V hJV
      E.toAddEquiv.toMultiplicativeRight from rfl,
      Theory.GroupAction.ModelConjugation.action_ker]
    ext x
    constructor
    · intro hx u hu
      exact Subtype.ext (hx u hu)
    · intro hx u hu
      exact congrArg J.subtype (hx ⟨u,hVJ hu⟩ hu)
  have hJ : elementaryAbelianMaxJ S ≤ a.ker := by
    rw [hka]
    apply FourBlockThompson.thompson_le_centralizer U S hUS e a
    · intro x u
      change E.toAddEquiv.toMultiplicativeRight
        (V.normalizerMonoidHom (inclusion hJV x)
          (E.toAddEquiv.toMultiplicativeRight.symm
            (E.toAddEquiv.toMultiplicativeRight ((subgroupOfEquivOfLe hVJ) u)))) = _
      rw [MulEquiv.symm_apply_apply]
      rfl
    · exact hka
    · exact map_comap_le _ _
  have hJR : elementaryAbelianMaxJ R ≤ Q T L := by
    rw [elementaryAbelianMaxJ_map_injective J.subtype J.subtype_injective S]
    exact (map_mono hJ).trans_eq (congrArg (map J.subtype) hk)
  have he : elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) :=
    (elementaryAbelianMaxJ_eq_of_intermediate R (Q T L) hJR hQR).symm
  have hp : IsPGroup 2 S :=
    ((IsElementaryAbelian.isPGroup 2 FourBlockCoreAction.kleinGroup).map
      FourBlockThompson.coreAut).comap_of_ker_isPGroup a (hk.symm ▸ pCore_isPGroup)
  refine ⟨hQR,map_subtype_le _,hp.map _,he,?_⟩
  exact (normalizer_le_normalizer_elementaryAbelianMaxJ R).trans
    (he ▸ H.core_thompson_normalizer)

omit [Finite G] in
/-- The original marked core makes the preimage's automorphism image exactly the radical. -/
theorem OrthogonalMarking.fourBlockPreimage_image
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    (FourBlockThompson.radicalImage.comap
      (coreMarkedAction (sup_le chosen.normalizes hTV) E)).map
      (coreMarkedAction (sup_le chosen.normalizes hTV) E) =
        FourBlockThompson.radicalImage := by
  apply map_comap_eq_self
  rintro _ ⟨k,hk,rfl⟩
  have hkalt : k ∈ alternatingGroup (Fin 8) :=
    TerminalOrthogonal.FourBlockResidual.R_le_P
      (TerminalOrthogonal.FourBlockResidual.kleinGroup_le_R hk) |>.1
  obtain ⟨l,hl⟩ := D.actorMap_surjective ⟨k,hkalt⟩
  refine ⟨inclusion (show L ≤ LT T L from le_sup_left) l,?_⟩
  apply MulEquiv.ext
  intro w
  let e : V ≃* Multiplicative (core (Fin 8)) := E.toAddEquiv.toMultiplicativeRight
  obtain ⟨u,rfl⟩ := e.surjective w
  change e (V.normalizerMonoidHom
    (inclusion (sup_le chosen.normalizes hTV) (inclusion le_sup_left l))
    (e.symm (e u))) = _
  rw [e.symm_apply_apply]
  change E (seedRepresentation L V chosen.normalizes l (Additive.ofMul u)) =
    coreRepresentation (Fin 8) k (E (Additive.ofMul u))
  rw [hE,hl]
  rfl

/-- The full preimage has the source radical index, with the original Q as kernel. -/
theorem SourceHypothesis.fourBlockPreimage_index
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    (Q T L).relIndex (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E) = 16 := by
  let a := coreMarkedAction (sup_le H.chosen.normalizes hTV) E
  change ((pCore 2 (LT T L)).map (LT T L).subtype).relIndex
    ((FourBlockThompson.radicalImage.comap a).map (LT T L).subtype) = _
  rw [relIndex_map_map_of_injective _ _ (LT T L).subtype_injective,
    ←coreMarkedAction_ker H hTV E, relIndex_ker,
    D.fourBlockPreimage_image H.chosen hTV E hE]
  change Nat.card (FourBlockCoreAction.kleinGroup.map FourBlockThompson.coreAut) = 16
  rw [card_map_of_injective FourBlockThompson.coreAut_injective,
    TerminalOrthogonal.FourBlockResidual.kleinGroup_card]

/-- The original nontrivial fixed space supplies compatible core coordinates and
its controlled full four-block preimage, without a model-action premise. -/
theorem SourceHypothesis.exists_controlled_fourBlockPreimage
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      let R := fourBlockPreimage (sup_le H.chosen.normalizes hTV) E
      Q T L ≤ R ∧ R ≤ LT T L ∧ IsPGroup 2 R ∧
        (Q T L).relIndex R = 16 ∧
        elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R : Set G) ≤ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  obtain ⟨hq,hr,hp,hj,hn⟩ := H.fourBlockPreimage_thompson hTV E
  exact ⟨E,hE,hproj,hq,hr,hp,H.fourBlockPreimage_index D hTV E hE,hj,hn⟩

/-- Place the controlled four-block preimage in the original Sylow by an
actual conjugator in LT, retaining Q and its index. -/
theorem SourceHypothesis.exists_fourBlockPreimage_in_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    ∃ g : LT T L,
      let R := (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
        (MulAut.conj (g : G)).toMonoidHom
      Q T L ≤ R ∧ R ≤ (T : Subgroup G) ∧ (Q T L).relIndex R = 16 ∧
        elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R : Set G) ≤ M L := by
  let J := LT T L
  let R := fourBlockPreimage (sup_le H.chosen.normalizes hTV) E
  obtain ⟨hQR,hRJ,hp,hj,hn⟩ := H.fourBlockPreimage_thompson hTV E
  have hi := H.fourBlockPreimage_index D hTV E hE
  obtain ⟨P,hP⟩ := (hp.comap_of_injective J.subtype J.subtype_injective).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J P
    (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right))
  let c := (MulAut.conj (g : G)).toMonoidHom
  have hnQ : J ≤ normalizer (Q T L : Set G) := J.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image J (pCore 2 J))
  have hQ : (Q T L).map c = Q T L := mem_normalizer_iff_map_conj_eq.mp (hnQ g.property)
  have hT : R.map c ≤ (T : Subgroup G) := by
    rintro _ ⟨r,hr,rfl⟩
    have ht : g * (⟨r,hRJ hr⟩ : J) * g⁻¹ ∈
        (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right) : Subgroup J) := by
      rw [←hg]
      exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hP hr)
    exact ht
  have hQRg : Q T L ≤ R.map c := hQ ▸ map_mono hQR
  have hjg : elementaryAbelianMaxJ (R.map c) = elementaryAbelianMaxJ (Q T L) := by
    rw [elementaryAbelianMaxJ_map_injective c (MulAut.conj (g : G)).injective R,
      hj, ←elementaryAbelianMaxJ_map_injective c (MulAut.conj (g : G)).injective (Q T L),hQ]
  refine ⟨g,hQRg,hT,?_,hjg,?_⟩
  · rw [←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj (g : G)).injective]
    exact hi
  · exact (normalizer_le_normalizer_elementaryAbelianMaxJ _).trans
      (hjg ▸ H.core_thompson_normalizer)

/-- The original nontrivial fixed space constructs the marked four-block
radical in the original T, with the original quotient projection retained. -/
theorem SourceHypothesis.exists_controlled_fourBlock_in_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥) :
    ∃ E : Additive V ≃ₗ[ZMod 2] core (Fin 8),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      ∃ g : LT T L,
        let R := (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
          (MulAut.conj (g : G)).toMonoidHom
        Q T L ≤ R ∧ R ≤ (T : Subgroup G) ∧ (Q T L).relIndex R = 16 ∧
          elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) ∧
          normalizer (R : Set G) ≤ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  exact ⟨E,hE,hproj,H.exists_fourBlockPreimage_in_sylow D hTV E hE⟩

end CFSG.Quasithin.Chapter12.Section06
