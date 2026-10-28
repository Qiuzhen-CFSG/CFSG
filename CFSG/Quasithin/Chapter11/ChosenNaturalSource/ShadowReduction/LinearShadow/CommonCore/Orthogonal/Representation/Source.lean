module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Components.Product
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Orthogonal.Representation.Commutant

/-!
# The original second factor on the common two-core

Transpose the two given natural K-summands into matrix columns. Commutation
modulo the abelian P makes the original L₂-action commute with all left SL₂
matrices. The additive commutant calculation constructs its right SL₂ map.
The original action on V₂=P∩V identifies the kernel as O₂(L₂)=P; the actual
quotient model and equal field orders prove surjectivity. No compatibility
between the separate coefficient fields is assumed.

The final theorem applies this construction to the original source factors.
Their C-component recognition remains with the common-core orthogonal owner,
which must discharge both premises before completing the source paragraph.
Source: Aschbacher--Smith, combined manuscript, printed p.774. The section
used here is the literal V₂, correcting the printed V, which is not in P.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Matrix
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open scoped MatrixGroups commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore

def transposeCoordinates {F : Type*} [Field F] :
    Multiplicative (Fin 2 → Fin 2 → F) ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F) where
  toFun v := Multiplicative.ofAdd (fun i j => v.toAdd j i)
  invFun M := Multiplicative.ofAdd (fun j i => M.toAdd i j)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {G : Type*} [Group G] {V H : Subgroup G} {h : G} {F : BinaryField}

def PairNaturalMarking.matrixCoordinates (c : PairNaturalMarking V H h F)
    (hn : c.multiplicity = 2) :
    pairCore V H h ≃* Multiplicative (Matrix (Fin 2) (Fin 2) F.Carrier) :=
  (hn ▸ c.coordinates).trans transposeCoordinates

theorem PairNaturalMarking.matrixCoordinates_intertwines
    (c : PairNaturalMarking V H h F) (hn : c.multiplicity = 2)
    (k : outsideResidual H) (p : pairCore V H h) :
    (c.matrixCoordinates hn (pairResidualAction V H h c.normalizes k p)).toAdd =
      (c.quotientEquiv (QuotientGroup.mk' _ k)).val * (c.matrixCoordinates hn p).toAdd := by
  cases c with
  | mk n hp hnorm q e he =>
    dsimp only at hn
    subst n
    ext i j
    exact congrFun (he k p j) i

variable [Finite G] {T : Sylow 2 G} {L X A : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3)}
    {f : InvariantFlag (.sl3 m)}
    (d : OrthogonalInput D S m f H X A h)

include d

theorem source_factor_commutator_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h := by
  obtain ⟨a⟩ := source_product_quotient_of_components d hK hL
  apply commutator_le.mpr
  intro k hk l hl
  let k' : orthogonalJoin (f.Li 1) V h := ⟨k, a.first_le hk⟩
  let l' : orthogonalJoin (f.Li 1) V h := ⟨l, a.second_le hl⟩
  have hk0 : (a.projection k').2 = 1 := by
    have hh := mem_map_of_mem a.projection (show k' ∈ (outsideResidual H).subgroupOf _ from hk)
    rw [a.first_factor] at hh
    exact hh
  have hl0 : (a.projection l').1 = 1 := by
    have hh := mem_map_of_mem a.projection (show l' ∈ (f.Li 1).subgroupOf _ from hl)
    rw [a.second_factor] at hh
    exact hh
  have he : a.projection ⁅k',l'⁆ = 1 := by
    rw [map_commutatorElement]
    apply Prod.ext <;> simp [commutatorElement_def, hk0, hl0]
  have hh : ⁅k',l'⁆ ∈ a.projection.ker := he
  rw [a.kernel] at hh
  exact hh


def source_localPairAction : f.Li 1 →* MulAut (pairCore V H h) :=
  (pairCore V H h).normalizerMonoidHom.comp
    (inclusion (le_sup_left.trans (orthogonalJoin_le_coreNormalizer
      d.source d.conjugator_mem (f.Li 1) d.local_core)))

def source_localMatrixAction : f.Li 1 →*
    Multiplicative (AddAut (Matrix (Fin 2) (Fin 2) d.pair_field.Carrier)) :=
  OrthogonalRepresentation.inCoordinates
    (d.pair_natural.matrixCoordinates d.pair_multiplicity) (source_localPairAction d)

theorem source_localMatrixAction_commutes
    (hc : ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h)
    (l : f.Li 1) (g : SL(2,d.pair_field.Carrier))
    (M : Matrix (Fin 2) (Fin 2) d.pair_field.Carrier) :
    (source_localMatrixAction d l).toAdd (g.val * M) =
      g.val * (source_localMatrixAction d l).toAdd M := by
  let P := pairCore V H h
  let e := d.pair_natural.matrixCoordinates d.pair_multiplicity
  let r := pairResidualAction V H h d.pair_natural.normalizes
  obtain ⟨k,hk⟩ := (d.pair_natural.quotientEquiv.surjective.comp
    (QuotientGroup.mk'_surjective _)) g
  change d.pair_natural.quotientEquiv (QuotientGroup.mk' _ k) = g at hk
  let l' : normalizer (P : Set G) :=
    inclusion (le_sup_left.trans (orthogonalJoin_le_coreNormalizer
      d.source d.conjugator_mem (f.Li 1) d.local_core)) l
  let k' : normalizer (P : Set G) := inclusion d.pair_natural.normalizes k
  have hcomm : Commute ((P.normalizerMonoidHom) k') ((P.normalizerMonoidHom) l') := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← map_commutatorElement]
    apply MonoidHom.mem_ker.mp
    rw [normalizerMonoidHom_ker]
    have hp : (⁅k',l'⁆ : normalizer (P : Set G)).val ∈ P :=
      hc (commutator_mem_commutator k.property l.property)
    let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
    exact (le_centralizer_iff_isMulCommutative.mpr inferInstance : P ≤ centralizer (P : Set G)) hp
  have he (p : P) : (e (r k p)).toAdd = g.val * (e p).toAdd := by
    exact (d.pair_natural.matrixCoordinates_intertwines d.pair_multiplicity k p).trans
      (by rw [hk])
  let p := e.symm (Multiplicative.ofAdd M)
  have hp : (e p).toAdd = M := congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  have heq : e.symm (Multiplicative.ofAdd (g.val * M)) = r k p := by
    apply e.injective
    rw [e.apply_symm_apply]
    apply Multiplicative.toAdd.injective
    simpa only [hp, toAdd_ofAdd] using (he p).symm
  change (OrthogonalRepresentation.inCoordinates e (source_localPairAction d) l).toAdd _ = _
  rw [OrthogonalRepresentation.inCoordinates_apply, heq]
  have hact : source_localPairAction d l (r k p) = r k (source_localPairAction d l p) :=
    (MulEquiv.congr_fun hcomm.eq p).symm
  rw [hact, he]
  exact congrArg (fun N => g.val * N)
    (OrthogonalRepresentation.inCoordinates_apply e (source_localPairAction d) l M).symm


omit d in
private theorem canonical_local_plane_centralizer :
    (SL3.flag D S m).Li 1 ⊓ centralizer ((SL3.flag D S m).Vi 1 : Set G) =
      ((SL3.flag D S m).Li 1).pCoreIn 2 := by
  let := D.centralQuotientPreimage_elementary
    ((Coordinates.sl3 m).binarySubspace ((SL3.flag D S m).space 1))
  apply le_antisymm
  · rintro x ⟨hx,hc⟩
    let l : (SL3.flag D S m).Li 1 := ⟨x,hx⟩
    have hq : SL3.PlaneAction.planeProjection D S m l = 1 := by
      apply Subtype.ext
      apply Matrix.mulVec_injective
      funext w
      let v := (SL3.PlaneAction.planeEquiv D S m).symm w
      have hf : Components.flagAction (SL3.flag D S m) 1
          ⟨l,(localResidual_le _ l.property).2⟩ v = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hc v.toMul v.toMul.property).symm
      have he := SL3.PlaneAction.planeEquiv_intertwines D S m l v
      rw [hf] at he
      dsimp only [v] at he
      rw [LinearEquiv.apply_symm_apply] at he
      exact he.symm.trans (Matrix.one_mulVec w).symm
    exact mem_map_of_mem ((SL3.flag D S m).Li 1).subtype
      ((SL3.PlaneAction.planeProjection_ker D S m) ▸
        (show l ∈ (SL3.PlaneAction.planeProjection D S m).ker from hq))
  · exact le_inf (pCoreIn_le _ _) (SL3.PlaneAction.plane_core_centralizes D S m)

theorem source_local_plane_centralizer :
    f.Li 1 ⊓ centralizer (f.Vi 1 : Set G) = pairCore V H h := by
  have he := canonical_local_plane_centralizer (D := D) (S := S) (m := m)
  rw [← source_flag_eq d] at he
  exact he.trans d.local_core

theorem source_localPairAction_ker :
    (source_localPairAction d).ker = pCore 2 (f.Li 1) := by
  have hP : pairCore V H h ≤ f.Li 1 := (source_pairCore_le_factors d).2
  have he : (pairCore V H h).subgroupOf (f.Li 1) = pCore 2 (f.Li 1) := by
    rw [← d.local_core]
    exact comap_map_eq_self_of_injective (f.Li 1).subtype_injective _
  rw [← he]
  ext l
  constructor
  · intro hl
    have hfix (p : pairCore V H h) : source_localPairAction d l p = p :=
      MulEquiv.congr_fun (show source_localPairAction d l = 1 from hl) p
    apply (source_local_plane_centralizer d).le
    refine ⟨l.property, ?_⟩
    intro v hv
    have hvP : v ∈ pairCore V H h :=
      (d.intersection_eq_plane.symm ▸ hv : v ∈ pairCore V H h ⊓ V).1
    have hh := congrArg Subtype.val (hfix ⟨v,hvP⟩)
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hl
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro p
    apply Subtype.ext
    let := pairCore_elementary d.source d.conjugator_mem d.conjugates_disjoint
    have hh := (le_centralizer_iff_isMulCommutative.mpr inferInstance :
      pairCore V H h ≤ centralizer (pairCore V H h : Set G)) hl p p.property
    exact mul_inv_eq_iff_eq_mul.mpr hh.symm

/-- The second factor is reconstructed over the first factor's coefficient field. -/
def source_localRightProjection
    (hc : ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h) :
    f.Li 1 →* SL(2,d.pair_field.Carrier) := by
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  exact OrthogonalRepresentation.rightSL (source_localMatrixAction d)
    (source_localMatrixAction_commutes d hc)

theorem source_localRightProjection_action
    (hc : ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h)
    (l : f.Li 1) (p : pairCore V H h) :
    (d.pair_natural.matrixCoordinates d.pair_multiplicity
      (source_localPairAction d l p)).toAdd =
    (d.pair_natural.matrixCoordinates d.pair_multiplicity p).toAdd *
      (source_localRightProjection d hc l)⁻¹.val := by
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  have hh := OrthogonalRepresentation.rightSL_action (source_localMatrixAction d)
    (source_localMatrixAction_commutes d hc) l
    (d.pair_natural.matrixCoordinates d.pair_multiplicity p).toAdd
  change (OrthogonalRepresentation.inCoordinates
    (d.pair_natural.matrixCoordinates d.pair_multiplicity) (source_localPairAction d) l).toAdd
    (d.pair_natural.matrixCoordinates d.pair_multiplicity p).toAdd = _ at hh
  rw [OrthogonalRepresentation.inCoordinates_apply, ofAdd_toAdd,
    MulEquiv.symm_apply_apply] at hh
  exact hh


theorem source_localRightProjection_ker
    (hc : ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h) :
    (source_localRightProjection d hc).ker = pCore 2 (f.Li 1) := by
  let : Group.IsPerfect (f.Li 1) := localResidual_perfect _
  exact (OrthogonalRepresentation.rightSL_ker (source_localMatrixAction d)
    (source_localMatrixAction_commutes d hc)).trans
      ((OrthogonalRepresentation.inCoordinates_ker _ _).trans (source_localPairAction_ker d))

theorem source_localRightProjection_surjective
    (hc : ⁅outsideResidual H, f.Li 1⁆ ≤ pairCore V H h) :
    Function.Surjective (source_localRightProjection d hc) := by
  let q := source_localRightProjection d hc
  let : Fintype d.pair_field.Carrier := Fintype.ofFinite _
  let : Fintype S.field.Carrier := Fintype.ofFinite _
  let ef : S.field.Carrier ≃+* d.pair_field.Carrier := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      d.pair_field.card_eq, S.field.card_eq, d.pair_degree])
  let e := ((SL3.flagLocalCoreEquiv S m f 1).trans
    (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := S.field.Carrier)).symm).trans
      (GorensteinWalter.sl2RingEquiv ef)
  have hcard : Nat.card q.range = Nat.card SL(2,d.pair_field.Carrier) := by
    calc
      Nat.card q.range = Nat.card ((f.Li 1) ⧸ q.ker) :=
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv).symm
      _ = Nat.card ((f.Li 1) ⧸ pCore 2 (f.Li 1)) :=
        Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
          (source_localRightProjection_ker d hc)).toEquiv
      _ = Nat.card SL(2,d.pair_field.Carrier) := Nat.card_congr e.toEquiv
  exact MonoidHom.range_eq_top.mp (q.range.eq_top_of_card_eq hcard)

/-- The actual right matrix action of L₂ over the K-field.
Its kernel is exactly P, and its image is the whole second SL₂. -/
theorem source_second_matrix_factor_of_components
    (hK : Source.ComponentIn (coreNormalizer V H h) (outsideResidual H))
    (hL : Source.ComponentIn (coreNormalizer V H h) (f.Li 1)) :
    ∃ q : f.Li 1 →* SL(2,d.pair_field.Carrier), Function.Surjective q ∧
      q.ker = pCore 2 (f.Li 1) ∧
      ∀ (l : f.Li 1) (p : pairCore V H h),
        (d.pair_natural.matrixCoordinates d.pair_multiplicity
          (source_localPairAction d l p)).toAdd =
        (d.pair_natural.matrixCoordinates d.pair_multiplicity p).toAdd * (q l)⁻¹.val := by
  let hc := source_factor_commutator_of_components d hK hL
  exact ⟨source_localRightProjection d hc, source_localRightProjection_surjective d hc,
    source_localRightProjection_ker d hc, source_localRightProjection_action d hc⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
