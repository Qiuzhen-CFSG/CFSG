module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockThompson
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockPoint
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreImageRestriction

/-!
# The original weight-four residual and its controlled local core

The compatible seven-dimensional core marking sends a selected original
weight-four point to the first four-letter word. The actual action image
of O²(C_L(v₄)) is A₄ × A₄, and the displayed quotient map identifies its
quotient by O₂ with the literal E₉. The same action on LT has kernel Q.
Core-image transport therefore identifies the previously controlled full
four-block preimage with Q O₂(O²(C_L(v₄))) and O₂(Q O²(C_L(v₄))).

The original Thompson and normalizer conclusions apply to this literal
core. Sylow conjugacy places it in the unchanged T and transports its
point by the same element of LT. The final constructor obtains the core
coordinates from the original nontrivial C_V(L), preserving the projection
V -> V/C_V(L) and requiring no extra model-action premise.

Alignment with O₂(L₁T₄), conjugacy of L₁ in the contrary-fusion argument,
full fusion, HS/J₄ exclusion, weak closure and fixed-space elimination
remain required. Neither 12.6.2 nor 12.6.23 is asserted. Earlier
invariance/TI retain qt-d-1222-source; final earlier-source discharge stays
with qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4) and the proof of 12.6.19, printed pp.823 and 828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open BinaryPermutation.TerminalOrthogonal
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The source weight-four residual has the literal two alternating block factors
as its image under the original action, without a recognition premise. -/
theorem OrthogonalMarking.Lv_image_fourBlock
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ((Lv L (v : G)).subgroupOf L).map
      ((alternatingGroup (Fin 8)).subtype.comp D.actorMap) = FourBlockResidual.R := by
  let a := (alternatingGroup (Fin 8)).subtype.comp D.actorMap
  let C := (CLv L (v : G)).subgroupOf L
  have hc (l : L) : l ∈ C ↔ a l ∈ FourBlockPoint.stabilizer := by
    change (l : G) ∈ L ⊓ Gv (v : G) ↔ _
    rw [mem_inf, and_iff_right l.property]
    change (l : G) ∈ centralizer ({(v : G)} : Set G) ↔
      coreRepresentation (Fin 8) (a l) FourBlockPoint.point = FourBlockPoint.point
    rw [←hv]
    change (l : G) ∈ centralizer ({(v : G)} : Set G) ↔
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E (Additive.ofMul v)) = E (Additive.ofMul v)
    rw [←hE]
    rw [E.injective.eq_iff,mem_centralizer_singleton_iff]
    constructor
    · intro hh
      apply Additive.toMul.injective
      apply Subtype.ext
      change (l : G) * (v : G) * (l : G)⁻¹ = v
      rw [hh,mul_inv_cancel_right]
    · intro hh
      have he := congrArg (fun w : Additive V => (w.toMul : G)) hh
      exact mul_inv_eq_iff_eq_mul.mp he
  have hm : C.map a = alternatingGroup (Fin 8) ⊓ FourBlockPoint.stabilizer := by
    apply le_antisymm
    · rintro _ ⟨l,hl,rfl⟩
      exact ⟨(D.actorMap l).property,(hc l).mp hl⟩
    · rintro g ⟨hg,hs⟩
      obtain ⟨l,hl⟩ := D.actorMap_surjective ⟨g,hg⟩
      have he : a l = g := congrArg Subtype.val hl
      exact ⟨l,(hc l).mpr (he ▸ hs),he⟩
  have hr : (pResidual 2 C).map C.subtype = (Lv L (v : G)).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [map_subgroupOf_eq_of_le (Lv_le_L L _),map_embedded_pResidual,
      map_subgroupOf_eq_of_le (show CLv L (v : G) ≤ L from inf_le_left)]
    rfl
  rw [←hr,map_embedded_pResidual,hm]
  exact FourBlockPoint.even_stabilizer_residual

private theorem marked_action_kernel
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

omit [Finite G] in
private theorem marked_action_on_L
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    (coreMarkedAction (sup_le chosen.normalizes hTV) E).comp
      (inclusion (show L ≤ LT T L from le_sup_left)) =
      FourBlockThompson.coreAut.comp ((alternatingGroup (Fin 8)).subtype.comp D.actorMap) := by
  apply MonoidHom.ext
  intro l
  apply MulEquiv.ext
  intro w
  let e : V ≃* Multiplicative (core (Fin 8)) := E.toAddEquiv.toMultiplicativeRight
  obtain ⟨u,rfl⟩ := e.surjective w
  change e (V.normalizerMonoidHom
    (inclusion (sup_le chosen.normalizes hTV) (inclusion le_sup_left l))
    (e.symm (e u))) = _
  rw [e.symm_apply_apply]
  exact hE l (Additive.ofMul u)

/-- In the original LT action, the same point residual has exactly the
marked A₄ × A₄ image. -/
theorem OrthogonalMarking.Lv_coreMarkedAction_image_fourBlock
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ((Lv L (v : G)).subgroupOf (LT T L)).map
      (coreMarkedAction (sup_le chosen.normalizes hTV) E) =
      FourBlockResidual.R.map FourBlockThompson.coreAut := by
  have hinc : ((Lv L (v : G)).subgroupOf L).map
      (inclusion (show L ≤ LT T L from le_sup_left)) =
      (Lv L (v : G)).subgroupOf (LT T L) := by
    apply map_injective (LT T L).subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le
      ((Lv_le_L L _).trans (show L ≤ LT T L from le_sup_left))]
    change ((Lv L (v : G)).subgroupOf L).map L.subtype = _
    exact map_subgroupOf_eq_of_le (Lv_le_L L _)
  rw [←hinc,map_map,marked_action_on_L chosen D hTV E hE,←map_map,
    D.Lv_image_fourBlock chosen E hE v hv]

/-- The saved full four-block preimage is precisely Q O₂(L₁), where
L₁ is the original O²(C_L(v₄)). This identifies its local core without
replacing Q or the marked vector. -/
theorem SourceHypothesis.fourBlockPreimage_eq_sup_point_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    fourBlockPreimage (sup_le H.chosen.normalizes hTV) E =
      Q T L ⊔ (Lv L (v : G)).pCoreIn 2 := by
  let J := LT T L
  let a := coreMarkedAction (sup_le H.chosen.normalizes hTV) E
  let B := (Lv L (v : G)).subgroupOf J
  have hk : a.ker = pCore 2 J := marked_action_kernel H hTV E
  have hm := D.Lv_coreMarkedAction_image_fourBlock H.chosen hTV E hE v hv
  have hp : (B.pCoreIn 2).map a = FourBlockThompson.radicalImage := by
    rw [map_pCoreIn_of_ker_isPGroup a (hk.symm ▸ pCore_isPGroup),hm]
    rw [←map_pCoreIn_of_ker_isPGroup FourBlockThompson.coreAut
      (by rw [MonoidHom.ker_eq_bot _ FourBlockThompson.coreAut_injective];
          exact IsPGroup.of_bot),FourBlockPoint.residual_core]
    rfl
  change (FourBlockThompson.radicalImage.comap a).map J.subtype = _
  rw [←hp,comap_map_eq,hk,Subgroup.map_sup]
  have he : (B.pCoreIn 2).map J.subtype = (Lv L (v : G)).pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 _ _ ((Lv_le_L L _).trans (show L ≤ LT T L from le_sup_left)),
      map_subgroupOf_eq_of_le ((pCoreIn_le 2 _).trans ((Lv_le_L L _).trans (show L ≤ LT T L from le_sup_left)))]
  rw [he]
  exact sup_comm _ _

/-- The same controlled preimage is the two-core of Q L₁. -/
theorem SourceHypothesis.fourBlockPreimage_eq_join_point_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    fourBlockPreimage (sup_le H.chosen.normalizes hTV) E =
      (Q T L ⊔ Lv L (v : G)).pCoreIn 2 := by
  let J := LT T L
  let a := coreMarkedAction (sup_le H.chosen.normalizes hTV) E
  let B := (Lv L (v : G)).subgroupOf J
  let A := a.ker ⊔ B
  have hk : a.ker = pCore 2 J := marked_action_kernel H hTV E
  have hm : A.map a = FourBlockResidual.R.map FourBlockThompson.coreAut := by
    rw [Subgroup.map_sup,map_ker_self,bot_sup_eq]
    exact D.Lv_coreMarkedAction_image_fourBlock H.chosen hTV E hE v hv
  have hp : (A.map a).pCoreIn 2 = FourBlockThompson.radicalImage := by
    rw [hm,←map_pCoreIn_of_ker_isPGroup FourBlockThompson.coreAut
      (by rw [MonoidHom.ker_eq_bot _ FourBlockThompson.coreAut_injective];
          exact IsPGroup.of_bot),FourBlockPoint.residual_core]
    rfl
  have ha : FourBlockThompson.radicalImage.comap a ≤ A := by
    have hi : FourBlockThompson.radicalImage ≤ A.map a := hp ▸ pCoreIn_le 2 (A.map a)
    exact (comap_mono hi).trans_eq (comap_map_eq_self le_sup_left)
  have hc := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 a A (hk.symm ▸ pCore_isPGroup)
  rw [hp,inf_eq_right.mpr ha] at hc
  have he : A.map J.subtype = Q T L ⊔ Lv L (v : G) := by
    rw [Subgroup.map_sup,hk,map_subgroupOf_eq_of_le ((Lv_le_L L _).trans (show L ≤ LT T L from le_sup_left))]
    rfl
  change (FourBlockThompson.radicalImage.comap a).map J.subtype = _
  rw [hc,map_pCoreIn_of_ker_isPGroup J.subtype
    (by rw [J.subtype.ker_eq_bot J.subtype_injective]; exact IsPGroup.of_bot),he]

/-- The original weight-four point supplies the local radical in Q L₁ and
its normalizer control, on the unchanged full Q-extension. -/
theorem SourceHypothesis.weight_four_local_core_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    let R₁ := (Q T L ⊔ Lv L (v : G)).pCoreIn 2
    Q T L ≤ R₁ ∧ (Q T L).relIndex R₁ = 16 ∧
      elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
      normalizer (R₁ : Set G) ≤ M L := by
  rw [←H.fourBlockPreimage_eq_join_point_core D hTV E hE v hv]
  obtain ⟨hq,_,_,hj,hn⟩ := H.fourBlockPreimage_thompson hTV E
  exact ⟨hq,H.fourBlockPreimage_index D hTV E hE,hj,hn⟩

/-- The weight-four residual maps onto the literal product of the alternating
block factors through the original conjugation quotient. -/
@[expose] noncomputable def OrthogonalMarking.fourBlockPointMap
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    Lv L (v : G) →* FourBlockResidual.R :=
  (((alternatingGroup (Fin 8)).subtype.comp D.actorMap).comp
    (inclusion (Lv_le_L L (v : G)))).codRestrict _ (fun x => by
      rw [←D.Lv_image_fourBlock chosen E hE v hv]
      exact ⟨⟨x.val,Lv_le_L L _ x.property⟩,x.property,rfl⟩)

theorem OrthogonalMarking.fourBlockPointMap_surjective
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    Function.Surjective (D.fourBlockPointMap chosen E hE v hv) := by
  intro r
  obtain ⟨l,hl,he⟩ := (D.Lv_image_fourBlock chosen E hE v hv).ge r.property
  exact ⟨⟨l.val,hl⟩,Subtype.ext he⟩

/-- The composite onto E₉ has exactly the original local two-core as kernel. -/
theorem SourceHypothesis.fourBlockPointQuotient_ker
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    (FourBlockResidual.quotientMap.comp
      (D.fourBlockPointMap H.chosen E hE v hv)).ker = pCore 2 (Lv L (v : G)) := by
  let f := D.fourBlockPointMap H.chosen E hE v hv
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = D.actorMap.ker.comap (inclusion (Lv_le_L L (v : G))) := by
      ext x
      change (⟨_,_⟩ : FourBlockResidual.R) = 1 ↔ _
      rw [Subtype.ext_iff]
      change (D.actorMap (inclusion (Lv_le_L L (v : G)) x)).val = (1 : alternatingGroup (Fin 8)).val ↔
        D.actorMap (inclusion (Lv_le_L L (v : G)) x) = 1
      exact Subtype.ext_iff.symm
    rw [he,D.actorMap_ker H.chosen H.source.quasisimple]
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective (Lv_le_L L _))
  let q := FourBlockResidual.quotientMap.comp f
  have hkq : IsPGroup 2 q.ker := by
    change IsPGroup 2 (FourBlockResidual.quotientMap.comp f).ker
    rw [←MonoidHom.comap_ker,FourBlockResidual.quotientMap_ker]
    exact (IsElementaryAbelian.isPGroup 2 FourBlockResidual.E16).comap_of_ker_isPGroup f hk
  have hzero : pCore 2 FourBlockResidual.E9 = ⊥ := by
    have hp : IsPGroup 2 (pCore 2 FourBlockResidual.E9) := pCore_isPGroup
    have h3 := (IsElementaryAbelian.isPGroup 3 FourBlockResidual.E9).to_subgroup
      (pCore 2 FourBlockResidual.E9)
    simpa only [inf_idem] using (hp.disjoint_of_coprime h3 (by decide)).eq_bot
  have hh := q.comap_pCore_of_ker_isPGroup
    (FourBlockResidual.quotientMap_surjective.comp
      (D.fourBlockPointMap_surjective H.chosen E hE v hv)) hkq
  rwa [hzero,MonoidHom.comap_bot] at hh

/-- The source L₁/O₂(L₁) is the genuine E₉, with its quotient map retained. -/
@[expose] noncomputable def SourceHypothesis.fourBlockPointQuotientEquiv
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    Star (Lv L (v : G)) ≃* FourBlockResidual.E9 :=
  (QuotientGroup.quotientMulEquivOfEq (H.fourBlockPointQuotient_ker D E hE v hv).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (FourBlockResidual.quotientMap_surjective.comp
        (D.fourBlockPointMap_surjective H.chosen E hE v hv)))

@[simp] theorem SourceHypothesis.fourBlockPointQuotientEquiv_mk
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) (x : Lv L (v : G)) :
    H.fourBlockPointQuotientEquiv D E hE v hv (QuotientGroup.mk' _ x) =
      FourBlockResidual.quotientMap (D.fourBlockPointMap H.chosen E hE v hv x) := rfl

/-- Place the literal weight-four local core in the original Sylow, carrying
its point by the same LT-conjugator. -/
theorem SourceHypothesis.weight_four_local_core_in_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ∃ (g : LT T L) (w : V),
      (w : G) = (g : G) * (v : G) * (g : G)⁻¹ ∧
      let R := (Q T L ⊔ Lv L (w : G)).pCoreIn 2
      Q T L ≤ R ∧ R ≤ (T : Subgroup G) ∧ (Q T L).relIndex R = 16 ∧
        elementaryAbelianMaxJ R = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R : Set G) ≤ M L := by
  obtain ⟨g,hq,ht,hi,hj,hn⟩ := H.exists_fourBlockPreimage_in_sylow D hTV E hE
  let c := (MulAut.conj (g : G)).toMonoidHom
  let w : V := ⟨(g : G) * (v : G) * (g : G)⁻¹,
    ((sup_le H.chosen.normalizes hTV g.property) (v : G)).mp v.property⟩
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component g.property)
  have hQ : (Q T L).map c = Q T L := mem_normalizer_iff_map_conj_eq.mp
    (((LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (LT T L) (pCore 2 (LT T L)))) g.property)
  have hpoint : (Gv (v : G)).map c = Gv (w : G) :=
    map_pointCentralizer (MulAut.conj (g : G)) (v : G)
  have hC : (CLv L (v : G)).map c = CLv L (w : G) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (g : G)).injective,hL,hpoint]
    rfl
  have hB : (Lv L (v : G)).map c = Lv L (w : G) := by
    rw [Lv,map_embedded_pResidual,hC]
    rfl
  have he : (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map c =
      (Q T L ⊔ Lv L (w : G)).pCoreIn 2 := by
    rw [H.fourBlockPreimage_eq_join_point_core D hTV E hE v hv,
      map_pCoreIn_of_ker_isPGroup c
        (by rw [MonoidHom.ker_eq_bot _ (MulAut.conj (g : G)).injective];
            exact IsPGroup.of_bot),Subgroup.map_sup,hQ,hB]
  exact ⟨g,w,rfl,he ▸ hq,he ▸ ht,he ▸ hi,he ▸ hj,he ▸ hn⟩

/-- Nontrivial original fixed space constructs the point and its controlled
local core, retaining the given action and quotient projection. -/
theorem SourceHypothesis.exists_weight_four_local_core_control
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (v : V),
      (∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) ∧
      (∀ w, coreToNatural (Fin 8) (E w) = D.coordinates (Submodule.Quotient.mk w)) ∧
      E (Additive.ofMul v) = FourBlockPoint.point ∧
      ((Lv L (v : G)).subgroupOf L).map
        ((alternatingGroup (Fin 8)).subtype.comp D.actorMap) = FourBlockResidual.R ∧
      Nonempty (Star (Lv L (v : G)) ≃* FourBlockResidual.E9) ∧
      let R₁ := (Q T L ⊔ Lv L (v : G)).pCoreIn 2
      Q T L ≤ R₁ ∧ (Q T L).relIndex R₁ = 16 ∧
        elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R₁ : Set G) ≤ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  let v := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  exact ⟨E,v,hE,hproj,hv,D.Lv_image_fourBlock H.chosen E hE v hv,
    ⟨H.fourBlockPointQuotientEquiv D E hE v hv⟩,H.weight_four_local_core_control D hTV E hE v hv⟩

end CFSG.Quasithin.Chapter12.Section06
