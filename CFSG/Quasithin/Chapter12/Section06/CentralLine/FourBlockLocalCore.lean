module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockPoint
public import Theory.Representation.BinaryPermutation.EightCoreAction

/-!
# The source weight-four point and O₂(L₁T₄)

Extend the original core coordinates to the whole LT action, with kernel
Q. Every subgroup between QL₁ and C_LT(v₄) maps between A₄ × A₄ and the
four-block stabilizer. Its two-core is therefore the same full preimage
of V₄ × V₄. In particular O₂(L₁T₄)=O₂(QL₁)=O₂(C_LT(v₄)).

Transport this entire interval by the same LT-conjugator as its point.
The original Thompson and normalizer control now apply to the literal
source core O₂(L₁T₄). Counting the original weight-four orbit gives 70.
Sylow selection then constructs an actual L-conjugate with T₄ Sylow in
C_M(v₄), |T:T₄|=2, and C_LT(v₄)=L₁T₄. The final application constructs
its coordinates from the original nontrivial C_V(L) and retains the
original quotient projection, full Q-extension and one conjugator.

The contrary-fusion L₁-conjugacy, HS/J₄ exclusions, weak closure,
splitting and fixed-space elimination remain required. Neither 12.6.2
nor 12.6.23 is asserted. The earlier invariance/TI clauses retain
qt-d-1222-source; their final discharge stays with qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4) and the proof of 12.6.19, printed pp.823 and 828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- The original LT action extends the given core marking to actual eight-letter
permutations, with exactly the original Q as kernel. -/
theorem SourceHypothesis.exists_core_permutation_action
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w)) :
    ∃ f : LT T L →* Equiv.Perm (Fin 8),
      (∀ l : L, f (inclusion le_sup_left l) = (D.actorMap l).val) ∧
      (∀ a w, E (seedRepresentation (LT T L) V
        (sup_le H.chosen.normalizes hTV) a w) = coreRepresentation (Fin 8) (f a) (E w)) ∧
      FourBlockThompson.coreAut.comp f = coreMarkedAction (sup_le H.chosen.normalizes hTV) E ∧
      f.ker = pCore 2 (LT T L) := by
  let J := LT T L
  let hn : J ≤ normalizer (V : Set G) := sup_le H.chosen.normalizes hTV
  let A := L.subgroupOf J
  let : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component)
  let e : A ≃* L := subgroupOfEquivOfLe (show L ≤ J from le_sup_left)
  obtain ⟨f,hf,ha,_⟩ := EightCoreAction.exists_ambient_hom
    (seedRepresentation J V hn) A (D.actorMap.comp e.toMonoidHom)
    (D.actorMap_surjective.comp e.surjective) E (fun l w => hE (e l) w)
  have he : FourBlockThompson.coreAut.comp f = coreMarkedAction hn E := by
    apply MonoidHom.ext
    intro a
    apply MulEquiv.ext
    intro w
    let eV : V ≃* Multiplicative (core (Fin 8)) := E.toAddEquiv.toMultiplicativeRight
    obtain ⟨u,rfl⟩ := eV.surjective w
    change coreRepresentation (Fin 8) (f a) (E (Additive.ofMul u)) =
      E (seedRepresentation J V hn a (E.symm (E (Additive.ofMul u))))
    rw [E.symm_apply_apply]
    exact (ha a (Additive.ofMul u)).symm
  refine ⟨f,(fun l => hf ⟨inclusion le_sup_left l,l.property⟩),ha,he,?_⟩
  have hk : f.ker = (coreMarkedAction hn E).ker := by
    rw [←he]
    ext a
    change f a = 1 ↔ FourBlockThompson.coreAut (f a) = 1
    rw [←FourBlockThompson.coreAut.map_one,FourBlockThompson.coreAut_injective.eq_iff]
  rw [hk]
  apply map_injective J.subtype_injective
  exact (Theory.GroupAction.ModelConjugation.action_ker_map J V hn
    E.toAddEquiv.toMultiplicativeRight).trans (H.join_centralizer_eq_core hTV)

/-- Every original intermediate point group, from QL₁ up to C_LT(v₄),
has the same controlled full preimage as its two-core. -/
theorem SourceHypothesis.weight_four_intermediate_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (X : Subgroup G) (hlo : Q T L ⊔ Lv L (v : G) ≤ X)
    (hhi : X ≤ LT T L ⊓ Gv (v : G)) :
    X.pCoreIn 2 = fourBlockPreimage (sup_le H.chosen.normalizes hTV) E := by
  obtain ⟨f,hf,ha,he,hk⟩ := H.exists_core_permutation_action D hTV E hE
  let J := LT T L
  let B := X.subgroupOf J
  have hBJ : X ≤ J := hhi.trans inf_le_left
  have hinc : ((Lv L (v : G)).subgroupOf L).map
      (inclusion (show L ≤ J from le_sup_left)) = (Lv L (v : G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le ((Lv_le_L L _).trans (show L ≤ J from le_sup_left))]
    change ((Lv L (v : G)).subgroupOf L).map L.subtype = _
    exact map_subgroupOf_eq_of_le (Lv_le_L L _)
  have hfl : f.comp (inclusion (show L ≤ J from le_sup_left)) =
      (alternatingGroup (Fin 8)).subtype.comp D.actorMap := MonoidHom.ext hf
  have hm : ((Lv L (v : G)).subgroupOf J).map f = FourBlockResidual.R := by
    rw [←hinc,map_map,hfl,D.Lv_image_fourBlock H.chosen E hE v hv]
  have hr : FourBlockResidual.R ≤ B.map f := by
    rw [←hm]
    exact map_mono (comap_mono (le_sup_right.trans hlo))
  have hb : B.map f ≤ FourBlockResidual.H := by
    rintro _ ⟨x,hx,rfl⟩
    apply FourBlockPoint.stabilizer_le
    change coreRepresentation (Fin 8) (f x) FourBlockPoint.point = FourBlockPoint.point
    rw [←hv,←ha]
    apply congrArg E
    apply Additive.toMul.injective
    apply Subtype.ext
    change x.val * (v : G) * x.val⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp (hhi hx).2)
  have hc := FourBlockPoint.intermediate_core (B.map f) hr hb
  have hker : f.ker ≤ B := by
    rw [hk]
    intro x hx
    exact hlo (mem_sup_left (mem_map_of_mem J.subtype hx))
  have hpre : Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup.comap f ≤ B := by
    have hh := comap_mono (f := f) (FourBlockResidual.kleinGroup_le_R.trans hr)
    rwa [comap_map_eq_self hker] at hh
  have hB := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f B (hk.symm ▸ pCore_isPGroup)
  rw [hc,inf_eq_right.mpr hpre] at hB
  have hmodel : Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup.comap f =
      FourBlockThompson.radicalImage.comap (coreMarkedAction (sup_le H.chosen.normalizes hTV) E) := by
    rw [←he]
    ext x
    change f x ∈ Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup ↔
      FourBlockThompson.coreAut (f x) ∈
        Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup.map FourBlockThompson.coreAut
    exact (mem_map_iff_mem FourBlockThompson.coreAut_injective).symm
  rw [hmodel] at hB
  change X.pCoreIn 2 = (FourBlockThompson.radicalImage.comap _).map J.subtype
  rw [hB,pCoreIn_subgroupOf 2 X J hBJ,map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hBJ)]

/-- The literal source local core O₂(L₁T₄) equals the controlled full preimage. -/
theorem SourceHypothesis.weight_four_sylow_join_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    (Lv L (v : G) ⊔ Tv T (v : G)).pCoreIn 2 =
      (Q T L ⊔ Lv L (v : G)).pCoreIn 2 := by
  rw [←H.fourBlockPreimage_eq_join_point_core D hTV E hE v hv]
  apply H.weight_four_intermediate_core D hTV E hE v hv
  · exact sup_le ((Q_le_Tv H.chosen v).trans le_sup_right) le_sup_left
  · exact sup_le (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
      (inf_le_inf le_sup_right le_rfl)


/-- Transport the entire interval of original point groups by the same LT
conjugator, retaining the full Q-extension and the marked point. -/
theorem SourceHypothesis.weight_four_conjugate_intermediate_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (X : Subgroup G) (hlo : Q T L ⊔ Lv L (w : G) ≤ X)
    (hhi : X ≤ LT T L ⊓ Gv (w : G)) :
    X.pCoreIn 2 = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
      (MulAut.conj (g : G)).toMonoidHom := by
  let c := (MulAut.conj (g : G)).toMonoidHom
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component g.property)
  have hJ : (LT T L).map c = LT T L := mem_normalizer_iff_map_conj_eq.mp
    ((LT T L).le_normalizer g.property)
  have hQ : (Q T L).map c = Q T L := mem_normalizer_iff_map_conj_eq.mp
    (((LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (LT T L) (pCore 2 (LT T L)))) g.property)
  have hp : (Gv (v : G)).map c = Gv (w : G) := by
    rw [hw]
    exact map_pointCentralizer (MulAut.conj (g : G)) (v : G)
  have hC : (CLv L (v : G)).map c = CLv L (w : G) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (g : G)).injective,hL,hp]
    rfl
  have hB : (Lv L (v : G)).map c = Lv L (w : G) := by
    rw [Lv,map_embedded_pResidual,hC]
    rfl
  have hlo' : Q T L ⊔ Lv L (v : G) ≤ X.comap c := by
    apply map_le_iff_le_comap.mp
    rwa [Subgroup.map_sup,hQ,hB]
  have hhi' : X.comap c ≤ LT T L ⊓ Gv (v : G) := by
    have hh := comap_mono (f := c) hhi
    rw [←hJ,←hp,←map_inf _ _ _ (MulAut.conj (g : G)).injective,
      comap_map_eq_self_of_injective (MulAut.conj (g : G)).injective] at hh
    exact hh
  have hc := congrArg (map c)
    (H.weight_four_intermediate_core D hTV E hE v hv (X.comap c) hlo' hhi')
  rw [map_pCoreIn_of_ker_isPGroup c
    (by rw [MonoidHom.ker_eq_bot _ (MulAut.conj (g : G)).injective]; exact IsPGroup.of_bot),
    map_comap_eq_self (by rw [MonoidHom.range_eq_top_of_surjective _ (MulAut.conj (g : G)).surjective]; exact le_top)] at hc
  exact hc

/-- The original source subgroup O₂(L₁T₄), at the transported point, inherits
all saved Thompson control and lies in the unchanged Sylow T. -/
theorem SourceHypothesis.weight_four_source_core_in_sylow
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ∃ (g : LT T L) (w : V),
      (w : G) = (g : G) * (v : G) * (g : G)⁻¹ ∧
      let R₁ := (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2
      R₁ = (Q T L ⊔ Lv L (w : G)).pCoreIn 2 ∧
      R₁ = Rv T L (w : G) ∧
      R₁ = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
        (MulAut.conj (g : G)).toMonoidHom ∧
      Q T L ≤ R₁ ∧ R₁ ≤ (T : Subgroup G) ∧ (Q T L).relIndex R₁ = 16 ∧
        elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R₁ : Set G) ≤ M L := by
  obtain ⟨g,w,hw,hq,ht,hi,hj,hn⟩ := H.weight_four_local_core_in_sylow D hTV E hE v hv
  have hlow : Q T L ⊔ Lv L (w : G) ≤ LT T L ⊓ Gv (w : G) :=
    sup_le (le_inf (pCoreIn_le 2 (LT T L)) ((Q_le_Tv H.chosen w).trans inf_le_right))
      (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
  have hmid := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w hw
    (Lv L (w : G) ⊔ Tv T (w : G))
    (sup_le ((Q_le_Tv H.chosen w).trans le_sup_right) le_sup_left)
    (sup_le (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
      (inf_le_inf le_sup_right le_rfl))
  have hlo := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w hw
    (Q T L ⊔ Lv L (w : G)) le_rfl hlow
  have hhi := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w hw
    (LT T L ⊓ Gv (w : G)) hlow le_rfl
  have he := hmid.trans hlo.symm
  exact ⟨g,w,hw,he,hmid.trans hhi.symm,hmid,he ▸ hq,he ▸ ht,he ▸ hi,he ▸ hj,he ▸ hn⟩

/-- The nontrivial original fixed space constructs the complete source core
alignment, with the original quotient projection and the same conjugator. -/
theorem SourceHypothesis.exists_weight_four_source_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V ≠ ⊥) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (v : V),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      E (Additive.ofMul v) = FourBlockPoint.point ∧
      ∃ (g : LT T L) (w : V),
        (w : G) = (g : G) * (v : G) * (g : G)⁻¹ ∧
        let R₁ := (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2
        R₁ = (Q T L ⊔ Lv L (w : G)).pCoreIn 2 ∧ R₁ = Rv T L (w : G) ∧
        R₁ = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
          (MulAut.conj (g : G)).toMonoidHom ∧
        Q T L ≤ R₁ ∧ R₁ ≤ (T : Subgroup G) ∧ (Q T L).relIndex R₁ = 16 ∧
          elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
          normalizer (R₁ : Set G) ≤ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  let v := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  exact ⟨E,v,hE,hproj,hv,H.weight_four_source_core_in_sylow D hTV E hE v hv⟩


omit [Finite G] in
/-- Count the literal weight-four orbit on V, including its nontrivial fixed line. -/
theorem OrthogonalMarking.weight_four_point_index
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    (Gv (v : G)).relIndex L = 70 := by
  let j : core (Fin 8) → G := fun x => ((E.symm x).toMul : G)
  have hj : Function.Injective j :=
    Subtype.val_injective.comp (Additive.toMul.injective.comp E.symm.injective)
  have he (l : L) :
      j (alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E (Additive.ofMul v))) =
        (l : G) * (v : G) * (l : G)⁻¹ := by
    rw [←hE]
    change ((E.symm (E (seedRepresentation L V chosen.normalizes l (Additive.ofMul v)))).toMul : G) = _
    rw [E.symm_apply_apply]
    rfl
  have himg : j '' (Set.range fun a : alternatingGroup (Fin 8) =>
      alternatingCoreRepresentation (Fin 8) a (E (Additive.ofMul v))) =
      conjugacyOrbit L (v : G) := by
    ext y
    constructor
    · rintro ⟨_,⟨a,rfl⟩,rfl⟩
      obtain ⟨l,rfl⟩ := D.actorMap_surjective a
      exact ⟨l,(he l).symm⟩
    · rintro ⟨l,rfl⟩
      exact ⟨_,⟨D.actorMap l,rfl⟩,he l⟩
  rw [Gv,←conjugacyOrbit_ncard_eq_relIndex,←himg,Set.ncard_image_of_injective _ hj,
    EightCore.orbit_card,hv]
  have hw : wordWeight FourBlockPoint.point.val = 4 := by decide
  rw [hw]
  rfl

/-- Choose the source weight-four point by an actual L-conjugator so that
T₄ is Sylow in C_M(v₄) and has index two in the original T. -/
theorem OrthogonalMarking.exists_weight_four_sylow_position
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ∃ l : L, let w := conjugation L V chosen.normalizes l v
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 2 := by
  let J := M L ⊓ normalizer (V : Set G)
  have hTJ : (T : Subgroup G) ≤ J := le_inf chosen.sylow_normalizes_component hTV
  have hLJ : L ≤ J := le_inf L.le_normalizer chosen.normalizes
  obtain ⟨n,hn⟩ := exists_local_point_sylow T J hTJ (v : G)
  obtain ⟨l,hl⟩ := D.normalizer_orbit_control chosen n n.property.1 n.property.2 v
  let w := conjugation L V chosen.normalizes l v
  have hvne : v ≠ 1 := by
    intro he
    have hz : FourBlockPoint.point = 0 := by rw [←hv,he]; exact E.map_zero
    have hh := congrArg (fun x : core (Fin 8) => x.val 0) hz
    exact one_ne_zero hh
  have hwne : w ≠ 1 := fun he => hvne
    ((conjugation L V chosen.normalizes l).injective (he.trans (map_one _).symm))
  have hnw : (n : G)*(v : G)*(n : G)⁻¹ = (w : G) := hl
  rw [hnw] at hn
  have hC : J ⊓ Gv (w : G) = Mv L (w : G) := by
    apply le_antisymm (inf_le_inf inf_le_left le_rfl)
    exact le_inf (le_inf inf_le_left (Mv_le_module_normalizer_of_TI hTI w hwne)) inf_le_right
  let C := J ⊓ Gv (w : G)
  let C' := C.subgroupOf J
  have hodd : ¬ 2 ∣ ((T : Subgroup G).subgroupOf J).relIndex C' := by
    rwa [relIndex_subgroupOf (show C ≤ J from inf_le_left)]
  have hindex : C'.index = 70 := by
    change (J ⊓ Gv (w : G)).relIndex J = 70
    rw [inf_relIndex_left,Gv,point_centralizer_index_of_orbit_control L J hLJ (w : G)
      (fun n => D.normalizer_orbit_control chosen n n.property.1 n.property.2 w),
      ←conjugacyOrbit_ncard_eq_relIndex]
    change (conjugacyOrbit L ((l : G)*(v : G)*(l : G)⁻¹)).ncard = 70
    rw [conjugacyOrbit_normalizer L (v : G) (l : G) (L.le_normalizer l.property),
      conjugacyOrbit_ncard_eq_relIndex]
    exact D.weight_four_point_index chosen E hE v hv
  have hi := (T.subtype hTJ).relIndex_eq_pow_factorization C' hodd
  rw [hindex] at hi
  have hf : (Nat.factorization 70) 2 = 1 := by
    rw [show 70 = 2 * 35 from rfl,Nat.factorization_mul (by decide) (by decide),
      Finsupp.add_apply,Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 35)]
  rw [hf] at hi
  have he : C'.relIndex (T.subtype hTJ) = (Tv T (w : G)).relIndex (T : Subgroup G) := by
    rw [Sylow.coe_subtype,relIndex_subgroupOf hTJ,Tv,inf_relIndex_left]
    apply congrArg Subgroup.index
    ext t
    change ((t : G) ∈ J ∧ (t : G) ∈ Gv (w : G)) ↔ (t : G) ∈ Gv (w : G)
    exact and_iff_right (hTJ t.property)
  rw [he] at hi
  have hTvC : Tv T (w : G) ≤ C := le_inf (inf_le_left.trans hTJ) inf_le_right
  have hp : IsPGroup 2 ((Tv T (w : G)).subgroupOf C) :=
    (T.isPGroup'.to_le (show Tv T (w : G) ≤ (T : Subgroup G) from inf_le_left)).comap_subtype
  have hoddTv : ¬ 2 ∣ ((Tv T (w : G)).subgroupOf C).index := by
    change ¬ 2 ∣ (Tv T (w : G)).relIndex C
    rw [show Tv T (w : G) = (T : Subgroup G) ⊓ C from by
      dsimp only [Tv,C]; rw [←inf_assoc,inf_of_le_left hTJ],inf_relIndex_right]
    exact hn
  have hs : Chapter1.IsSylowIn 2 (Tv T (w : G)) C :=
    ⟨hp.toSylow hoddTv,map_subgroupOf_eq_of_le hTvC⟩
  exact ⟨l,hC ▸ hs,hi⟩


/-- Source 12.6.19's selected weight-four position, with its actual L-conjugator,
Sylow index, local factorization and controlled O₂(L₁T₄) all constructed. -/
theorem SourceHypothesis.selected_weight_four_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    ∃ l : L, let w := conjugation L V H.chosen.normalizes l v
      let R₁ := (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2
      Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
      (Tv T (w : G)).relIndex (T : Subgroup G) = 2 ∧
      LT T L ⊓ Gv (w : G) = Lv L (w : G) ⊔ Tv T (w : G) ∧
      R₁ = (Q T L ⊔ Lv L (w : G)).pCoreIn 2 ∧ R₁ = Rv T L (w : G) ∧
      R₁ = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
        (MulAut.conj (l : G)).toMonoidHom ∧
      Q T L ≤ R₁ ∧ R₁ ≤ Tv T (w : G) ∧ (Q T L).relIndex R₁ = 16 ∧
        elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
        normalizer (R₁ : Set G) ≤ M L := by
  obtain ⟨l,hs,hi⟩ := D.exists_weight_four_sylow_position H.chosen hTV hTI E hE v hv
  let w := conjugation L V H.chosen.normalizes l v
  let g : LT T L := inclusion le_sup_left l
  let c := (MulAut.conj (l : G)).toMonoidHom
  let R₁ := (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2
  have hlow : Q T L ⊔ Lv L (w : G) ≤ LT T L ⊓ Gv (w : G) :=
    sup_le (le_inf (pCoreIn_le 2 (LT T L)) ((Q_le_Tv H.chosen w).trans inf_le_right))
      (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
  have hmid := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w rfl
    (Lv L (w : G) ⊔ Tv T (w : G))
    (sup_le ((Q_le_Tv H.chosen w).trans le_sup_right) le_sup_left)
    (sup_le (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
      (inf_le_inf le_sup_right le_rfl))
  have hlo := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w rfl
    (Q T L ⊔ Lv L (w : G)) le_rfl hlow
  have hhi := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w rfl
    (LT T L ⊓ Gv (w : G)) hlow le_rfl
  have hR : R₁ = Rv T L (w : G) := hmid.trans hhi.symm
  change R₁ = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map c at hmid
  have hQ : (Q T L).map c = Q T L := mem_normalizer_iff_map_conj_eq.mp
    (((LT T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (LT T L) (pCore 2 (LT T L)))) g.property)
  obtain ⟨hq,_,_,hj,_⟩ := H.fourBlockPreimage_thompson hTV E
  have hqr : Q T L ≤ R₁ := by rw [hmid,←hQ]; exact map_mono hq
  have hjr : elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) := by
    rw [hmid,elementaryAbelianMaxJ_map_injective c (MulAut.conj (l : G)).injective,
      hj,←elementaryAbelianMaxJ_map_injective c (MulAut.conj (l : G)).injective,hQ]
  have hir : (Q T L).relIndex R₁ = 16 := by
    rw [hmid,←hQ,relIndex_map_map_of_injective _ _ (MulAut.conj (l : G)).injective]
    exact H.fourBlockPreimage_index D hTV E hE
  have hs' := hs.restrict
    (show Tv T (w : G) ≤ LT T L ⊓ Gv (w : G) from inf_le_inf le_sup_right le_rfl)
    (show LT T L ⊓ Gv (w : G) ≤ Mv L (w : G) from
      inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  have hfac := localCentralizer_eq_Lv_sup_Tv H.chosen.sylow_normalizes_component (w : G) hs'
  obtain ⟨P,hP⟩ := hs'
  have hrt : R₁ ≤ Tv T (w : G) := by
    rw [hR]
    exact (pCoreIn_le_sylow (LT T L ⊓ Gv (w : G)) P).trans_eq hP
  exact ⟨l,hs,hi,hfac,hmid.trans hlo.symm,hR,hmid,hqr,hrt,hir,hjr,
    (normalizer_le_normalizer_elementaryAbelianMaxJ R₁).trans
      (hjr ▸ H.core_thompson_normalizer)⟩

/-- Construct the entire source weight-four position from the original nontrivial
fixed space, keeping the quotient projection and a single actual L-conjugator. -/
theorem SourceHypothesis.exists_selected_weight_four_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : CentralLine.HasTIConjugatesIn V (M L)) (hz : ZV L V ≠ ⊥) :
    ∃ (E : Additive V ≃ₗ[ZMod 2] core (Fin 8)) (v : V),
      (∀ l u, E (seedRepresentation L V H.chosen.normalizes l u) =
        alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E u)) ∧
      (∀ u, coreToNatural (Fin 8) (E u) = D.coordinates (Submodule.Quotient.mk u)) ∧
      E (Additive.ofMul v) = FourBlockPoint.point ∧
      ∃ l : L, let w := conjugation L V H.chosen.normalizes l v
        let R₁ := (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 2 ∧
        LT T L ⊓ Gv (w : G) = Lv L (w : G) ⊔ Tv T (w : G) ∧
        R₁ = (Q T L ⊔ Lv L (w : G)).pCoreIn 2 ∧ R₁ = Rv T L (w : G) ∧
        R₁ = (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
          (MulAut.conj (l : G)).toMonoidHom ∧
        Q T L ≤ R₁ ∧ R₁ ≤ Tv T (w : G) ∧ (Q T L).relIndex R₁ = 16 ∧
          elementaryAbelianMaxJ R₁ = elementaryAbelianMaxJ (Q T L) ∧
          normalizer (R₁ : Set G) ≤ M L := by
  obtain ⟨E,hE,hproj⟩ := D.core_marking_of_fixed_ne_bot H.chosen hz
  let v := (E.symm FourBlockPoint.point).toMul
  have hv : E (Additive.ofMul v) = FourBlockPoint.point := E.apply_symm_apply _
  exact ⟨E,v,hE,hproj,hv,H.selected_weight_four_core D hTV hTI E hE v hv⟩

end CFSG.Quasithin.Chapter12.Section06
