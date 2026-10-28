module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSplitting
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceFullAction
public import Theory.GroupTheory.SplitExtensionCoordinates.Marked

/-!
# Marked isomorphisms between the source local normalizers

The full row quotient action and both rectangle tensor actions, together
with their proved splittings, determine the corresponding local groups up
to isomorphism. The constructed maps retain the original marked kernel
elements. Faithfulness of the quotient actions then forces the exact
prescribed quotient maps. The plane map also preserves the actual
row–plane normalizer intersection, using source 39.6(4).

These are the local-group isomorphisms used in the linear branch of
Aschbacher, *Sporadic Groups* (1994), 41.4, printed p.222. The final
similarity still requires alignment on the row–three-space intersection,
source generation and the edge-fixer rigidity argument. No ambient group
isomorphism or simplicity of the normalizer-generated subgroup is assumed.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
namespace Theory.GroupTheory.TransvectionFive.UniquenessLinear
private theorem split_normalizer_equiv
    {G G' : Type*} [Group G] [Group G'] (A : Subgroup G) (B : Subgroup G')
    (eA : A ≃* B)
    (eQ : (normalizer (A : Set G) ⧸ A.subgroupOf (normalizer (A : Set G))) ≃*
      (normalizer (B : Set G') ⧸ B.subgroupOf (normalizer (B : Set G'))))
    (ρ : (normalizer (B : Set G') ⧸ B.subgroupOf (normalizer (B : Set G'))) →* MulAut B)
    (hρ : ∀ (n : normalizer (B : Set G')) (b : B),
      ρ (QuotientGroup.mk n) b = B.normalizerMonoidHom n b)
    (ha : ∀ (n : normalizer (A : Set G)) (a : A),
      eA (A.normalizerMonoidHom n a) = ρ (eQ (QuotientGroup.mk n)) (eA a))
    (hfaith : Function.Injective ρ)
    (hs : ∃ K : Subgroup (normalizer (A : Set G)),
      (A.subgroupOf (normalizer (A : Set G))).IsComplement' K)
    (hs' : ∃ K : Subgroup (normalizer (B : Set G')),
      (B.subgroupOf (normalizer (B : Set G'))).IsComplement' K) :
    ∃ e : normalizer (A : Set G) ≃* normalizer (B : Set G'),
      (∀ a : A, e (inclusion A.le_normalizer a) = inclusion B.le_normalizer (eA a)) ∧
      ∀ n, (QuotientGroup.mk (e n) : normalizer (B : Set G') ⧸
        B.subgroupOf (normalizer (B : Set G'))) = eQ (QuotientGroup.mk n) := by
  let NA := A.subgroupOf (normalizer (A : Set G))
  let NB := B.subgroupOf (normalizer (B : Set G'))
  let α : NA ≃* B := (subgroupOfEquivOfLe A.le_normalizer).trans eA
  let β : NB ≃* B := subgroupOfEquivOfLe B.le_normalizer
  obtain ⟨K, hK⟩ := hs
  obtain ⟨K', hK'⟩ := hs'
  obtain ⟨f, hf, _⟩ := exists_marked_semidirect_equiv_of_split_coordinates NA K hK eQ α ρ
    (fun n a => ha n ((subgroupOfEquivOfLe A.le_normalizer) a))
  obtain ⟨f', hf', _⟩ := exists_marked_semidirect_equiv_of_split_coordinates NB K' hK'
    (MulEquiv.refl _) β ρ (fun n b => (hρ n (β b)).symm)
  let e := f.trans f'.symm
  have heA (a : A) : e (inclusion A.le_normalizer a) = inclusion B.le_normalizer (eA a) := by
    apply f'.injective
    change f' (f'.symm (f (inclusion A.le_normalizer a))) = _
    rw [f'.apply_symm_apply]
    exact (hf ((subgroupOfEquivOfLe A.le_normalizer).symm a)).trans
      (hf' ((subgroupOfEquivOfLe B.le_normalizer).symm (eA a))).symm
  refine ⟨e, heA, fun n => ?_⟩
  apply hfaith
  apply MulEquiv.ext
  intro b
  obtain ⟨a, rfl⟩ := eA.surjective b
  rw [hρ, ← ha]
  apply Subtype.ext
  have hh := congrArg e (show inclusion A.le_normalizer (A.normalizerMonoidHom n a) =
    n * inclusion A.le_normalizer a * n⁻¹ from rfl)
  rw [heA, map_mul, map_mul, map_inv, heA] at hh
  exact (congrArg Subtype.val hh).symm

variable {G G' : Type*} [Group G] [Group G'] {z : G} {z' : G'}
  (F : MarkedCentralizer z) (F' : MarkedCentralizer z')

/-- Comparison of the two plane kernels through their original full-centralizer markings. -/
def planeMarkingEquiv : F.plane ≃* F'.plane :=
  (F.pullbackEquiv Model.plane Model.plane_le_centralizer).trans
    (F'.pullbackEquiv Model.plane Model.plane_le_centralizer).symm

private theorem planeMarkingEquiv_element (x : PlaneCensus.Code) :
    planeMarkingEquiv F F' (PlaneTensor.sourceEquiv F x) = PlaneTensor.sourceEquiv F' x := by
  apply (F'.pullbackEquiv Model.plane Model.plane_le_centralizer).injective
  change (F'.pullbackEquiv Model.plane Model.plane_le_centralizer)
    ((F'.pullbackEquiv Model.plane Model.plane_le_centralizer).symm
      ((F.pullbackEquiv Model.plane Model.plane_le_centralizer) (PlaneTensor.sourceEquiv F x))) = _
  rw [MulEquiv.apply_symm_apply]
  apply Subtype.ext
  exact (PlaneTensor.element_model F x).trans (PlaneTensor.element_model F' x).symm

/-- The plane restriction preserves every subgroup cut out by the same
full-centralizer marking. -/
theorem planeMarkingEquiv_mem_pullback (A : Subgroup SL) (a : F.plane) :
    (planeMarkingEquiv F F' a : G') ∈ F'.pullback A ↔ (a : G) ∈ F.pullback A := by
  rw [F'.mem_pullback_iff A ⟨planeMarkingEquiv F F' a,
    F'.pullback_le Model.plane (planeMarkingEquiv F F' a).property⟩,
    F.mem_pullback_iff A ⟨a, F.pullback_le Model.plane a.property⟩]
  have he : F'.pullbackEquiv Model.plane Model.plane_le_centralizer
      (planeMarkingEquiv F F' a) = F.pullbackEquiv Model.plane Model.plane_le_centralizer a :=
    (F'.pullbackEquiv Model.plane Model.plane_le_centralizer).apply_symm_apply _
  change (F'.pullbackEquiv Model.plane Model.plane_le_centralizer
    (planeMarkingEquiv F F' a) : SL) ∈ A ↔
      (F.pullbackEquiv Model.plane Model.plane_le_centralizer a : SL) ∈ A
  rw [he]

variable [Finite G] [Finite G']

/-- Plane normalizers have isomorphisms with the prescribed kernel and quotient markings. -/
theorem exists_plane_normalizer_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F',
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      ∀ n, (QuotientGroup.mk (e n) : sourcePlaneQuotient F') =
        ((PlaneTensor.quotientRankOneEquiv F h).trans
          (PlaneTensor.quotientRankOneEquiv F' h').symm) (QuotientGroup.mk n) := by
  let q := (PlaneTensor.quotientRankOneEquiv F h).trans
    (PlaneTensor.quotientRankOneEquiv F' h').symm
  apply split_normalizer_equiv F.plane F'.plane (planeMarkingEquiv F F') q
    (sourcePlaneQuotientAction F')
  · intro n b
    apply Subtype.ext
    exact sourcePlaneQuotientAction_mk F' n b
  · intro n a
    obtain ⟨x, rfl⟩ := (PlaneTensor.sourceEquiv F).surjective a
    let f := PlaneTensor.quotientRankOneEquiv F h (QuotientGroup.mk n)
    have he : F.plane.normalizerMonoidHom n (PlaneTensor.sourceEquiv F x) =
        PlaneTensor.sourceEquiv F (f.val x) := by
      apply Subtype.ext
      exact (PlaneTensor.quotientRankOneEquiv_action F h n x).symm
    rw [he, planeMarkingEquiv_element, planeMarkingEquiv_element]
    obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective
      (F'.plane.subgroupOf (sourcePlaneNormalizer F')) (q (QuotientGroup.mk n))
    rw [← hn']
    have hq : PlaneTensor.quotientRankOneEquiv F' h' (QuotientGroup.mk n') = f := by
      change PlaneTensor.quotientRankOneEquiv F' h' ((QuotientGroup.mk' _) n') = f
      rw [hn']
      exact (PlaneTensor.quotientRankOneEquiv F' h').apply_symm_apply _
    apply Subtype.ext
    change PlaneTensor.element F' (f.val x) =
      (sourcePlaneQuotientAction F' (QuotientGroup.mk n') (PlaneTensor.sourceEquiv F' x) : G')
    rw [sourcePlaneQuotientAction_mk]
    exact (congrArg (fun p : PlaneCensus.rankOneGroup => PlaneTensor.element F' (p.val x)) hq).symm.trans
      (PlaneTensor.quotientRankOneEquiv_action F' h' n' x)
  · exact sourcePlaneQuotientAction_injective F'
  · exact linear_plane_normalizer_splits F h
  · exact linear_plane_normalizer_splits F' h'

/-- Comparison of the original row coordinates. -/
def rowMarkingEquiv : F.row ≃* F'.row :=
  (rowCoordinates F).trans (rowCoordinates F').symm

omit [Finite G] [Finite G'] in
private theorem rowMarkingEquiv_coordinates (a : F.row) :
    rowCoordinates F' (rowMarkingEquiv F F' a) = rowCoordinates F a :=
  (rowCoordinates F').apply_symm_apply _

/-- The row comparison retains its original four-space and literal quotient map. -/
theorem exists_row_normalizer_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : rowNormalizer F ≃* rowNormalizer F',
      (∀ a : F.row, e (inclusion F.row.le_normalizer a) =
        inclusion F'.row.le_normalizer (rowMarkingEquiv F F' a)) ∧
      ∀ n, (QuotientGroup.mk (e n) : rowQuotient F') =
        ((linearRowQuotientEquiv F h).trans (linearRowQuotientEquiv F' h').symm)
          (QuotientGroup.mk n) := by
  let q := (linearRowQuotientEquiv F h).trans (linearRowQuotientEquiv F' h').symm
  apply split_normalizer_equiv F.row F'.row (rowMarkingEquiv F F') q (rowQuotientAction F')
  · intro n a
    apply Subtype.ext
    exact rowQuotientAction_mk_apply F' n a
  · intro n a
    obtain ⟨n', hn'⟩ := QuotientGroup.mk'_surjective
      (F'.row.subgroupOf (rowNormalizer F')) (q (QuotientGroup.mk n))
    rw [← hn']
    have hq : linearRowQuotientEquiv F' h' (QuotientGroup.mk n') =
        linearRowQuotientEquiv F h (QuotientGroup.mk n) := by
      change linearRowQuotientEquiv F' h' ((QuotientGroup.mk' _) n') = _
      rw [hn']
      exact (linearRowQuotientEquiv F' h').apply_symm_apply _
    have he : rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a) =
        F'.row.normalizerMonoidHom n' (rowMarkingEquiv F F' a) :=
      Subtype.ext (rowQuotientAction_mk_apply F' n' _)
    change rowMarkingEquiv F F' (F.row.normalizerMonoidHom n a) =
      rowQuotientAction F' (QuotientGroup.mk n') (rowMarkingEquiv F F' a)
    rw [he]
    apply (rowCoordinates F').injective
    apply Multiplicative.toAdd.injective
    rw [rowMarkingEquiv_coordinates, ← linearRowQuotientEquiv_action F h,
      ← linearRowQuotientEquiv_action F' h', hq, rowMarkingEquiv_coordinates]
  · exact rowQuotientAction_injective F'
  · exact row_normalizer_splits F
  · exact row_normalizer_splits F'


omit [Finite G] [Finite G'] in
private theorem normalizerCongr_inclusion {H : Type*} [Group H] (A B : Subgroup H) (h : A = B)
    (a : A) :
    MulEquiv.subgroupCongr (congrArg (fun P : Subgroup H => normalizer (P : Set H)) h)
      (inclusion A.le_normalizer a) = inclusion B.le_normalizer (MulEquiv.subgroupCongr h a) := by
  subst B
  rfl

/-- The original three-space marking, expressed through the fixed opposite
model coordinates used by its quotient action. -/
def threeSpaceMarkingEquiv : F.threeSpace ≃* F'.threeSpace :=
  (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm).trans
    ((planeMarkingEquiv (oppositeMarking F) (oppositeMarking F')).trans
      (MulEquiv.subgroupCongr (oppositeMarking_plane F')))

/-- The second rectangle normalizers are isomorphic by a map with the exact
three-space restriction. This uses the original subgroups in G and G'. -/
theorem exists_threeSpace_normalizer_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourceThreeSpaceNormalizer F ≃* sourceThreeSpaceNormalizer F',
      ∀ a : F.threeSpace, e (inclusion F.threeSpace.le_normalizer a) =
        inclusion F'.threeSpace.le_normalizer (threeSpaceMarkingEquiv F F' a) := by
  obtain ⟨e, he, _⟩ := exists_plane_normalizer_equiv (oppositeMarking F) (oppositeMarking F')
    (oppositeMarking_linearFusion F h) (oppositeMarking_linearFusion F' h')
  let c := MulEquiv.subgroupCongr
    (congrArg (fun P : Subgroup G => normalizer (P : Set G)) (oppositeMarking_plane F).symm)
  let c' := MulEquiv.subgroupCongr
    (congrArg (fun P : Subgroup G' => normalizer (P : Set G')) (oppositeMarking_plane F'))
  refine ⟨c.trans (e.trans c'), fun a => ?_⟩
  change c' (e (c (inclusion F.threeSpace.le_normalizer a))) = _
  rw [show c (inclusion F.threeSpace.le_normalizer a) =
    inclusion (oppositeMarking F).plane.le_normalizer
      (MulEquiv.subgroupCongr (oppositeMarking_plane F).symm a) from
        normalizerCongr_inclusion _ _ _ a, he]
  exact normalizerCongr_inclusion _ _ (oppositeMarking_plane F') _

/-- An extension of the original plane marking carries the literal row–plane
normalizer intersection to its corresponding target intersection. -/
theorem plane_normalizer_equiv_intersection
    (e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F')
    (he : ∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
      inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) :
    ((rowNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
      (rowNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
  let D := (F.row ⊓ F.plane).subgroupOf (sourcePlaneNormalizer F)
  let D' := (F'.row ⊓ F'.plane).subgroupOf (sourcePlaneNormalizer F')
  have hD : D.map e.toMonoidHom = D' := by
    apply le_antisymm
    · rintro y ⟨x, hx, rfl⟩
      have hx' : (x : G) ∈ F.row ∧ (x : G) ∈ F.plane := hx
      have hh := he ⟨x, hx'.2⟩
      change e x = _ at hh
      change e x ∈ D'
      rw [hh]
      exact ⟨(planeMarkingEquiv_mem_pullback F F' Model.row _).mpr hx'.1,
        (planeMarkingEquiv F F' ⟨x, hx'.2⟩).property⟩
    · intro y hy
      have hy' : (y : G') ∈ F'.row ∧ (y : G') ∈ F'.plane := hy
      let a := (planeMarkingEquiv F F').symm ⟨y, hy'.2⟩
      have ha : (a : G) ∈ F.row := (planeMarkingEquiv_mem_pullback F F' Model.row a).mp
        (by rw [(planeMarkingEquiv F F').apply_symm_apply]; exact hy'.1)
      refine ⟨inclusion F.plane.le_normalizer a, ⟨ha, a.property⟩, ?_⟩
      change e (inclusion F.plane.le_normalizer a) = y
      rw [he]
      exact congrArg (inclusion F'.plane.le_normalizer)
        ((planeMarkingEquiv F F').apply_symm_apply ⟨y, hy'.2⟩)
  have hN (P : MarkedCentralizer z) :
      normalizer (((P.row ⊓ P.plane).subgroupOf (sourcePlaneNormalizer P)) :
        Set (sourcePlaneNormalizer P)) = (rowNormalizer P).subgroupOf (sourcePlaneNormalizer P) := by
    rw [← subgroupOf_normalizer_eq (show P.row ⊓ P.plane ≤ sourcePlaneNormalizer P from
      inf_le_right.trans P.plane.le_normalizer), source_row_plane_normalizer]
    ext x
    exact and_iff_left x.property
  have hN' : normalizer (D' : Set (sourcePlaneNormalizer F')) =
      (rowNormalizer F').subgroupOf (sourcePlaneNormalizer F') := by
    rw [← subgroupOf_normalizer_eq (show F'.row ⊓ F'.plane ≤ sourcePlaneNormalizer F' from
      inf_le_right.trans F'.plane.le_normalizer), source_row_plane_normalizer]
    ext x
    exact and_iff_left x.property
  rw [← hN F, map_equiv_normalizer_eq, hD, hN']

/-- The plane comparison preserves both the literal row–plane intersection
and the prescribed map on the normalizer quotient. -/
theorem exists_plane_normalizer_flag_equiv (h : F.LinearFusion) (h' : F'.LinearFusion) :
    ∃ e : sourcePlaneNormalizer F ≃* sourcePlaneNormalizer F',
      (∀ a : F.plane, e (inclusion F.plane.le_normalizer a) =
        inclusion F'.plane.le_normalizer (planeMarkingEquiv F F' a)) ∧
      ((rowNormalizer F).subgroupOf (sourcePlaneNormalizer F)).map e.toMonoidHom =
        (rowNormalizer F').subgroupOf (sourcePlaneNormalizer F') ∧
      ∀ n, (QuotientGroup.mk (e n) : sourcePlaneQuotient F') =
        ((PlaneTensor.quotientRankOneEquiv F h).trans
          (PlaneTensor.quotientRankOneEquiv F' h').symm) (QuotientGroup.mk n) := by
  obtain ⟨e, he, hq⟩ := exists_plane_normalizer_equiv F F' h h'
  exact ⟨e, he, plane_normalizer_equiv_intersection F F' e he, hq⟩

/-- The local comparison construction also applies to the 41.1 induction
overgroup. All of its fusion and splitting premises are discharged here. -/
theorem normalizerSpan_local_isomorphisms (h : F.LinearFusion) (h' : F'.LinearFusion) :
    Nonempty (rowNormalizer (normalizerSpanMarking F) ≃* rowNormalizer F') ∧
    Nonempty (sourcePlaneNormalizer (normalizerSpanMarking F) ≃* sourcePlaneNormalizer F') ∧
    Nonempty (sourceThreeSpaceNormalizer (normalizerSpanMarking F) ≃* sourceThreeSpaceNormalizer F') := by
  have hL := normalizerSpan_linearFusion F h
  obtain ⟨e₁, _⟩ := exists_row_normalizer_equiv (normalizerSpanMarking F) F' hL h'
  obtain ⟨e₂, _⟩ := exists_plane_normalizer_flag_equiv (normalizerSpanMarking F) F' hL h'
  obtain ⟨e₃, _⟩ := exists_threeSpace_normalizer_equiv (normalizerSpanMarking F) F' hL h'
  exact ⟨⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩

end Theory.GroupTheory.TransvectionFive.UniquenessLinear
