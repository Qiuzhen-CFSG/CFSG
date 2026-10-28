module
public import CFSG.Quasithin.Chapter12.Section06.CentralLine.FourBlockLocalCore
public import Theory.Representation.BinaryPermutation.TerminalOrthogonal.FourBlockNormalizer

/-!
# Preserving the original four-block core under contrary fusion

The literal A₄ × A₄ image of L₁ has normalizer equal to the unordered
four-block stabilizer. Hence for every L₁ ≤ X ≤ N_LT(L₁), its two-core
is X intersected with the original full preimage of V₄ × V₄. This remains
valid when X does not contain Q. Transport the formula by the same
LT-conjugator as the weight-four point.

If a fusion conjugator fixes L₁ and sends T₄ into LT, the transported
O₂(L₁T₄) is contained in the original core. Equal orders give equality,
and its proved normalizer control puts the conjugator in M. An actual
L-correction preserves the required LT containment, so L-conjugacy of
the residual suffices for the contrary-fusion contradiction.

At the other end of that argument, the original E₉ quotient makes L₁
its own prime-to-three residual. Thus fusion into a point whose centralizer
lies in M sends L₁ into O^{3′}(M)=L. The final application constructs the
selected point and its core coordinates from the original nontrivial
C_V(L), retaining the quotient projection and the same L-conjugator.

The source assertion that this fused residual is L-conjugate to L₁ is
still required, as are the remaining fusion, HS/J₄ exclusion, weak closure,
splitting and fixed-space elimination arguments. Neither 12.6.2 nor
12.6.23 is asserted. Earlier invariance/TI retain qt-d-1222-source; their
final discharge remains with qt-d-12634-source.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004,
12.6.1(4--5) and the proof of 12.6.19, printed pp.823 and 828.
-/

public section
open Subgroup Theory.GroupTheory BinaryPermutation Stellmacher
open BinaryPermutation.TerminalOrthogonal
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

/-- An overgroup of the original weight-four residual inside its LT-normalizer
has two-core equal to its intersection with the controlled full preimage.
The overgroup need not contain Q. -/
theorem SourceHypothesis.weight_four_normalizer_intermediate_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (X : Subgroup G) (hlo : Lv L (v : G) ≤ X)
    (hhi : X ≤ LT T L ⊓ normalizer (Lv L (v : G) : Set G)) :
    X.pCoreIn 2 = X ⊓ fourBlockPreimage (sup_le H.chosen.normalizes hTV) E := by
  obtain ⟨f,hf,_,he,hk⟩ := H.exists_core_permutation_action D hTV E hE
  let J := LT T L
  let B := X.subgroupOf J
  have hBJ : X ≤ J := hhi.trans inf_le_left
  have hLJ : Lv L (v : G) ≤ J := (Lv_le_L L _).trans le_sup_left
  have hinc : ((Lv L (v : G)).subgroupOf L).map
      (inclusion (show L ≤ J from le_sup_left)) = (Lv L (v : G)).subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [map_map,map_subgroupOf_eq_of_le hLJ]
    change ((Lv L (v : G)).subgroupOf L).map L.subtype = _
    exact map_subgroupOf_eq_of_le (Lv_le_L L _)
  have hfl : f.comp (inclusion (show L ≤ J from le_sup_left)) =
      (alternatingGroup (Fin 8)).subtype.comp D.actorMap := MonoidHom.ext hf
  have hm : ((Lv L (v : G)).subgroupOf J).map f = FourBlockResidual.R := by
    rw [←hinc,map_map,hfl,D.Lv_image_fourBlock H.chosen E hE v hv]
  have hr : FourBlockResidual.R ≤ B.map f := by
    rw [←hm]
    exact map_mono (comap_mono hlo)
  have hn : B ≤ normalizer ((Lv L (v : G)).subgroupOf J : Set J) := by
    rw [←subgroupOf_normalizer_eq hLJ]
    exact comap_mono (hhi.trans inf_le_right)
  have hb : B.map f ≤ FourBlockResidual.H := by
    rw [←FourBlockPoint.residual_normalizer,←hm]
    exact (map_mono hn).trans (le_normalizer_map f)
  have hc := FourBlockPoint.intermediate_core (B.map f) hr hb
  have hB := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f B (hk.symm ▸ pCore_isPGroup)
  rw [hc] at hB
  have hmodel : Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup.comap f =
      FourBlockThompson.radicalImage.comap (coreMarkedAction (sup_le H.chosen.normalizes hTV) E) := by
    rw [←he]
    ext x
    change f x ∈ Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup ↔
      FourBlockThompson.coreAut (f x) ∈
        Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.kleinGroup.map FourBlockThompson.coreAut
    exact (mem_map_iff_mem FourBlockThompson.coreAut_injective).symm
  rw [hmodel] at hB
  have hh := congrArg (map J.subtype) hB
  rw [map_inf _ _ _ J.subtype_injective,map_subgroupOf_eq_of_le hBJ,
    pCoreIn_subgroupOf 2 X J hBJ,
    map_subgroupOf_eq_of_le ((pCoreIn_le 2 X).trans hBJ)] at hh
  exact hh.symm

/-- Transport the normalizer interval by the same LT-conjugator as its point,
without requiring the transported overgroup to contain the original Q. -/
theorem SourceHypothesis.weight_four_conjugate_normalizer_core
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (X : Subgroup G) (hlo : Lv L (w : G) ≤ X)
    (hhi : X ≤ LT T L ⊓ normalizer (Lv L (w : G) : Set G)) :
    X.pCoreIn 2 = X ⊓ (fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
      (MulAut.conj (g : G)).toMonoidHom := by
  let c := (MulAut.conj (g : G)).toMonoidHom
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component g.property)
  have hJ : (LT T L).map c = LT T L := mem_normalizer_iff_map_conj_eq.mp
    ((LT T L).le_normalizer g.property)
  have hp : (Gv (v : G)).map c = Gv (w : G) := by
    rw [hw]
    exact map_pointCentralizer (MulAut.conj (g : G)) (v : G)
  have hC : (CLv L (v : G)).map c = CLv L (w : G) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (g : G)).injective,hL,hp]
    rfl
  have hB : (Lv L (v : G)).map c = Lv L (w : G) := by
    rw [Lv,map_embedded_pResidual,hC]
    rfl
  have hN : (normalizer (Lv L (v : G) : Set G)).map c =
      normalizer (Lv L (w : G) : Set G) := by
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj (g : G)).bijective,hB]
  have hlo' : Lv L (v : G) ≤ X.comap c := by
    apply map_le_iff_le_comap.mp
    rwa [hB]
  have hhi' : X.comap c ≤ LT T L ⊓ normalizer (Lv L (v : G) : Set G) := by
    have hh := comap_mono (f := c) hhi
    rw [←hJ,←hN,←map_inf _ _ _ (MulAut.conj (g : G)).injective,
      comap_map_eq_self_of_injective (MulAut.conj (g : G)).injective] at hh
    exact hh
  have hc := congrArg (map c)
    (H.weight_four_normalizer_intermediate_core D hTV E hE v hv (X.comap c) hlo' hhi')
  rw [map_pCoreIn_of_ker_isPGroup c
    (by rw [MonoidHom.ker_eq_bot _ (MulAut.conj (g : G)).injective]; exact IsPGroup.of_bot),
    map_inf _ _ _ (MulAut.conj (g : G)).injective,
    map_comap_eq_self (by rw [MonoidHom.range_eq_top_of_surjective _ (MulAut.conj (g : G)).surjective]; exact le_top)] at hc
  exact hc

/-- After correcting the residual, the original core is preserved. Containment
of the transported T₄ in LT suffices; neither equality of Sylows nor preservation
of Q by the fusion conjugator is assumed. -/
theorem SourceHypothesis.weight_four_core_preserved
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (a : G) (hA : (Lv L (w : G)).map (MulAut.conj a).toMonoidHom = Lv L (w : G))
    (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L) :
    ((Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2).map
      (MulAut.conj a).toMonoidHom = (Lv L (w : G) ⊔ Tv T (w : G)).pCoreIn 2 := by
  let X := Lv L (w : G) ⊔ Tv T (w : G)
  let c := (MulAut.conj a).toMonoidHom
  have hX : X ≤ LT T L ⊓ Gv (w : G) :=
    sup_le (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
      (inf_le_inf le_sup_right le_rfl)
  have hR := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w hw X
    (sup_le ((Q_le_Tv H.chosen w).trans le_sup_right) le_sup_left) hX
  have hn : X ≤ normalizer (Lv L (w : G) : Set G) :=
    (hX.trans (inf_le_inf
      (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)).trans
        (Mv_le_normalizer_Lv L (w : G))
  have hn' : X.map c ≤ normalizer (Lv L (w : G) : Set G) := by
    rw [←hA]
    exact (map_mono hn).trans (le_normalizer_map c)
  have hlow : Lv L (w : G) ≤ X.map c := by
    rw [←hA]
    exact map_mono le_sup_left
  have hhigh : X.map c ≤ LT T L := by
    rw [Subgroup.map_sup,hA]
    exact sup_le ((Lv_le_L L _).trans le_sup_left) hS
  have he := H.weight_four_conjugate_normalizer_core D hTV E hE v hv g w hw
    (X.map c) hlow (le_inf hhigh hn')
  have hc : (X.pCoreIn 2).map c ≤ X.pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup c
      (by rw [MonoidHom.ker_eq_bot _ (MulAut.conj a).injective]; exact IsPGroup.of_bot),he,hR]
    exact inf_le_right
  apply Subgroup.eq_of_le_of_card_ge hc
  exact (Nat.card_congr ((X.pCoreIn 2).equivMapOfInjective c
    (MulAut.conj a).injective).toEquiv).le

/-- The core-preservation step in 12.6.19 forces the corrected conjugator into M. -/
theorem SourceHypothesis.weight_four_corrected_conjugator_mem
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (a : G) (hA : (Lv L (w : G)).map (MulAut.conj a).toMonoidHom = Lv L (w : G))
    (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L) : a ∈ M L := by
  have hR := H.weight_four_conjugate_intermediate_core D hTV E hE v hv g w hw
    (Lv L (w : G) ⊔ Tv T (w : G))
    (sup_le ((Q_le_Tv H.chosen w).trans le_sup_right) le_sup_left)
    (sup_le (le_inf ((Lv_le_L L _).trans le_sup_left) (Lv_le_Gv L _))
      (inf_le_inf le_sup_right le_rfl))
  have ha := mem_normalizer_iff_map_conj_eq.mpr
    (H.weight_four_core_preserved D hTV E hE v hv g w hw a hA hS)
  rw [hR] at ha
  have hn : normalizer ((fourBlockPreimage (sup_le H.chosen.normalizes hTV) E).map
      (MulAut.conj (g : G)).toMonoidHom : Set G) ≤ M L := by
    rw [←map_normalizer_eq_of_bijective _ (MulAut.conj (g : G)).bijective]
    have hm : (M L).map (MulAut.conj (g : G)).toMonoidHom = M L :=
      mem_normalizer_iff_map_conj_eq.mp ((M L).le_normalizer
        (sup_le L.le_normalizer H.chosen.sylow_normalizes_component g.property))
    exact (map_mono (H.fourBlockPreimage_thompson hTV E).2.2.2.2).trans_eq hm
  exact hn ha

/-- Correcting the transported residual by an actual element of L is enough:
the same correction keeps the transported T₄ inside LT, so the original
fusion conjugator lies in M. This removes the source's subsequent R₁ premise. -/
theorem SourceHypothesis.weight_four_conjugator_mem_of_residual_conjugate
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (a : G) (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L)
    (hconj : ∃ l : L, ((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (l : G)).toMonoidHom = Lv L (w : G)) : a ∈ M L := by
  obtain ⟨l,hl⟩ := hconj
  have hc : (MulAut.conj ((l : G)*a)).toMonoidHom =
      (MulAut.conj (l : G)).toMonoidHom.comp (MulAut.conj a).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  have hJ : (LT T L).map (MulAut.conj (l : G)).toMonoidHom = LT T L :=
    mem_normalizer_iff_map_conj_eq.mp ((LT T L).le_normalizer (mem_sup_left l.property))
  have hh := H.weight_four_corrected_conjugator_mem D hTV E hE v hv g w hw
    ((l : G)*a) (by rw [hc,←map_map]; exact hl)
    (by rw [hc,←map_map]; exact (map_mono hS).trans_eq hJ)
  exact (M L).mul_mem_cancel_left (L.le_normalizer l.property) |>.mp hh

/-- The genuine E₉ quotient and two-perfectness make the original weight-four
residual its own prime-to-three residual, before any fusion is assumed. -/
theorem SourceHypothesis.weight_four_residual_primeTo
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point) :
    (primeToResidual 3 (Lv L (v : G))).map (Lv L (v : G)).subtype = Lv L (v : G) := by
  let e := H.fourBlockPointQuotientEquiv D E hE v hv
  have hquot : IsPGroup 3 (Star (Lv L (v : G))) :=
    (IsElementaryAbelian.isPGroup 3 FourBlockResidual.E9).of_surjective
      e.symm.toMonoidHom e.symm.surjective
  have hr := primeToResidual_eq_top_of_pGroup_quotient 3 2
    (pCore 2 (Lv L (v : G))) pCore_isPGroup hquot
    (isPPerfect_embedded_pResidual 2 (CLv L (v : G)))
  rw [hr,←MonoidHom.range_eq_map,range_subtype]

/-- A weight-four residual fused into a controlled centralizer lies in the
original L. This discharges the first containment in the source contrary-fusion
argument using O^{3′}(M)=L, with the original point conjugator retained. -/
theorem SourceHypothesis.weight_four_fused_residual_le_component
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (a z : G) (ha : MulAut.conj a (w : G) = z) (hz : Gv z ≤ M L) :
    (Lv L (w : G)).map (MulAut.conj a).toMonoidHom ≤ L := by
  let c := (MulAut.conj (g : G)).toMonoidHom
  have hL : L.map c = L := mem_normalizer_iff_map_conj_eq.mp
    (sup_le L.le_normalizer H.chosen.sylow_normalizes_component g.property)
  have hp : (Gv (v : G)).map c = Gv (w : G) := by
    rw [hw]
    exact map_pointCentralizer (MulAut.conj (g : G)) (v : G)
  have hC : (CLv L (v : G)).map c = CLv L (w : G) := by
    rw [CLv,map_inf _ _ _ (MulAut.conj (g : G)).injective,hL,hp]
    rfl
  have hB : (Lv L (v : G)).map c = Lv L (w : G) := by
    rw [Lv,map_embedded_pResidual,hC]
    rfl
  have hr := congrArg (map c) (H.weight_four_residual_primeTo D E hE v hv)
  rw [map_embedded_primeToResidual_of_hom,hB] at hr
  have hr' := congrArg (map (MulAut.conj a).toMonoidHom) hr
  rw [map_embedded_primeToResidual_of_hom] at hr'
  have hBM : (Lv L (w : G)).map (MulAut.conj a).toMonoidHom ≤ M L := by
    have hh := map_mono (f := (MulAut.conj a).toMonoidHom) (Lv_le_Gv L (w : G))
    rw [Gv,map_pointCentralizer,ha] at hh
    exact hh.trans hz
  rw [←hr']
  exact (embedded_primeToResidual_mono 3 hBM).trans_eq (H.normalizer_primeToResidual D)

omit [Finite G] in
/-- Every transported weight-four point is still moved by the original L. -/
theorem OrthogonalMarking.weight_four_conjugate_not_centralized
    (chosen : Section02.ChosenModule T L V)
    (D : OrthogonalMarking L V chosen.normalizes)
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹) :
    (w : G) ∉ centralizer (L : Set G) := by
  intro hwc
  have hn := normalizer_le_normalizer_centralizer L
    (sup_le L.le_normalizer chosen.sylow_normalizes_component g.property)
  have hvc : (v : G) ∈ centralizer (L : Set G) := (hn (v : G)).mpr (hw ▸ hwc)
  have hle : L ≤ Gv (v : G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (hvc x hx)
  have hi := D.weight_four_point_index chosen E hE v hv
  rw [relIndex_eq_one.mpr hle] at hi
  exact (by decide : (1 : ℕ) ≠ 70) hi

/-- The source contrary-fusion contradiction after its L₁-conjugacy step.
Core preservation and the exclusion of fusion into C_G(L) are proved here. -/
theorem SourceHypothesis.weight_four_no_central_fusion_of_residual_conjugate
    (H : SourceHypothesis KnownSimple.IsKnownSimple T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (E : Additive V ≃ₗ[ZMod 2] core (Fin 8))
    (hE : ∀ l w, E (seedRepresentation L V H.chosen.normalizes l w) =
      alternatingCoreRepresentation (Fin 8) (D.actorMap l) (E w))
    (v : V) (hv : E (Additive.ofMul v) = FourBlockPoint.point)
    (g : LT T L) (w : V) (hw : (w : G) = (g : G) * (v : G) * (g : G)⁻¹)
    (a : G) (hS : (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L)
    (hconj : ∃ l : L, ((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).map
      (MulAut.conj (l : G)).toMonoidHom = Lv L (w : G)) :
    MulAut.conj a (w : G) ∉ centralizer (L : Set G) := by
  intro hc
  have ha := H.weight_four_conjugator_mem_of_residual_conjugate D hTV E hE v hv g w hw a hS hconj
  have hn := normalizer_le_normalizer_centralizer L ha
  exact D.weight_four_conjugate_not_centralized H.chosen E hE v hv g w hw
    ((hn (w : G)).mpr hc)

/-- Construct the original selected source point and both ends of the
contrary-fusion argument. The E₉ quotient places its fused residual in L;
if that residual is L-conjugate to L₁, the fused point cannot centralize L.
The remaining L-conjugacy assertion is deliberately not assumed as a source fact. -/
theorem SourceHypothesis.exists_selected_weight_four_fusion_reduction
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
        Chapter1.IsSylowIn 2 (Tv T (w : G)) (Mv L (w : G)) ∧
        (Tv T (w : G)).relIndex (T : Subgroup G) = 2 ∧
        (∀ (a z : G), MulAut.conj a (w : G) = z → Gv z ≤ M L →
          (Lv L (w : G)).map (MulAut.conj a).toMonoidHom ≤ L) ∧
        (∀ a : G, (Tv T (w : G)).map (MulAut.conj a).toMonoidHom ≤ LT T L →
          (∃ k : L, ((Lv L (w : G)).map (MulAut.conj a).toMonoidHom).map
            (MulAut.conj (k : G)).toMonoidHom = Lv L (w : G)) →
          a ∈ M L ∧ MulAut.conj a (w : G) ∉ centralizer (L : Set G)) := by
  obtain ⟨E,v,hE,hproj,hv,l,hs,hi,_⟩ := H.exists_selected_weight_four_core D hTV hTI hz
  let w := conjugation L V H.chosen.normalizes l v
  let g : LT T L := inclusion le_sup_left l
  refine ⟨E,v,hE,hproj,hv,l,hs,hi,?_,?_⟩
  · intro a z ha hc
    exact H.weight_four_fused_residual_le_component D E hE v hv g w rfl a z ha hc
  · intro a hS hc
    exact ⟨H.weight_four_conjugator_mem_of_residual_conjugate D hTV E hE v hv g w rfl a hS hc,
      H.weight_four_no_central_fusion_of_residual_conjugate D hTV E hE v hv g w rfl a hS hc⟩

end CFSG.Quasithin.Chapter12.Section06
