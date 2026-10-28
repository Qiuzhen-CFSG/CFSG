module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictCrossing
public import Theory.GroupTheory.SpecificGroups.KleinFourPointStabilizer

/-!
# Crossing normality in the literal dotted actor

The four-group point stabilizer factors as C_G(Z_S)U. Since U acts
trivially on its central quotient, its dotted image equals the image
of C_G(Z_S). That centralizer normalizes both X and Z(U)^d, proving
6.2.18(1). The elementary image of X, normalized by the original
Sylow image, is contained in that Sylow image by maximality. This
establishes G.11.1(4) without an extra two-core identification.

The same ambient normalization gives [C_U(Z_S),X] ≤ U ∩ U^d, and X
fixes the source quotient line pointwise. All normality is relative
and all dotted images use the original H-action kernel.

Source: Aschbacher--Smith, 6.2.17(3), 6.2.18(1) and G.11.1(4),
printed pp.689--690 and 364. Remaining G.10 inputs and the strict
contradiction stay with qt-d-1222-recognition-strict-elimination;
LocalAnalysis is discharged by qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

@[expose] def strictCrossingCenter (T L R : Subgroup G) (z d : G) : Subgroup G :=
  ((center (sourceClosure T L R z)).map (sourceClosure T L R z).subtype).map
    (MulAut.conj d⁻¹).toMonoidHom

@[expose] def strictCrossingCenterImage (T L R : Subgroup G) (z d : G) :
    Subgroup (StrictActor T L R z) :=
  ((strictCrossingCenter T L R z d).subgroupOf (centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (strictQuotientAction T L R z).ker)

omit [Finite G] in
private theorem plane_centralizer_le_H (T L R : Subgroup G) (z : G)
    (hz : z ∈ ZS T L R) :
    centralizer (ZS T L R : Set G) ≤ centralizer ({z} : Set G) := by
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hx z hz).symm

omit [Finite G] in
private theorem plane_centralizer_normalizes_conjugate
    (T L R : Subgroup G) (z : G) (hz : z ∈ ZS T L R)
    {d : G} (hd : d ∈ normalizer (ZS T L R : Set G)) :
    centralizer (ZS T L R : Set G) ≤
      normalizer ((sourceClosure T L R z).map (MulAut.conj d⁻¹).toMonoidHom : Set G) := by
  let C := centralizer (ZS T L R : Set G)
  have hn : C ≤ normalizer (sourceClosure T L R z : Set G) :=
    (plane_centralizer_le_H T L R z hz).trans (sourceClosure_normalized T L R z)
  have he : C.map (MulAut.conj d⁻¹).toMonoidHom = C :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (C : Set G)).inv_mem
      (normalizer_le_normalizer_centralizer (ZS T L R) hd))
  change C ≤ _
  rw [← map_equiv_normalizer_eq, ← he]
  exact map_mono hn

/-- The plane centralizer normalizes both literal crossed actors. -/
theorem strict_plane_centralizer_normalizes_crossing
    (_h611 : Hypothesis611 κ T L M R n) (hz : z ∈ ZS (T : Subgroup G) L R)
    {d : G} (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    centralizer (ZS (T : Subgroup G) L R : Set G) ≤
      normalizer (strictCrossingGroup (T : Subgroup G) L R z d : Set G) ∧
    centralizer (ZS (T : Subgroup G) L R : Set G) ≤
      normalizer (strictCrossingCenter (T : Subgroup G) L R z d : Set G) := by
  have hn := plane_centralizer_normalizes_conjugate (T : Subgroup G) L R z hz hd
  constructor
  · exact (le_inf hn (centralizer (ZS (T : Subgroup G) L R : Set G)).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  · have hh := hn.trans (normalizer_le_normalizer_characteristic_image _ (center _))
    rw [← map_embeddedCenter _ _ (MulAut.conj d⁻¹).injective] at hh
    exact hh

/-- The conjugate center lies in X, with its original embedding. -/
theorem strictCrossingCenter_le_group
    (h611 : Hypothesis611 κ T L M R n) (hz : z ∈ ZS (T : Subgroup G) L R)
    {d : G} (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    strictCrossingCenter (T : Subgroup G) L R z d ≤
      strictCrossingGroup (T : Subgroup G) L R z d := by
  let U := sourceClosure (T : Subgroup G) L R z
  have hS : ZS (T : Subgroup G) L R ≤ U.map (MulAut.conj d⁻¹).toMonoidHom :=
    (strict_plane_le_crossing h611 hz hd).trans inf_le_right
  rw [strictCrossingCenter, map_embeddedCenter _ _ (MulAut.conj d⁻¹).injective]
  refine le_inf (map_subtype_le _) ?_
  rintro x ⟨c, hc, rfl⟩ s hs
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨s, hS hs⟩)

/-- Source 6.2.17(3): [C_U(Z_S),X] lies in the actual crossed intersection. -/
theorem strict_crossing_commutator_le_intersection
    (_h611 : Hypothesis611 κ T L M R n) (hz : z ∈ ZS (T : Subgroup G) L R)
    {d : G} (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    ⁅sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G),
      strictCrossingGroup (T : Subgroup G) L R z d⁆ ≤
      strictCrossingIntersection (T : Subgroup G) L R z d := by
  let U := sourceClosure (T : Subgroup G) L R z
  let C := centralizer (ZS (T : Subgroup G) L R : Set G)
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  have hCU : C ≤ normalizer (U : Set G) :=
    (plane_centralizer_le_H (T : Subgroup G) L R z hz).trans
      (sourceClosure_normalized (T : Subgroup G) L R z)
  have hCW := plane_centralizer_normalizes_conjugate (T : Subgroup G) L R z hz hd
  refine le_inf ?_ ?_
  · exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((show X ≤ C from inf_le_right).trans hCU))
  · exact (commutator_mono le_rfl (show X ≤ U.map _ from inf_le_left)).trans
      (le_normalizer_iff_commutator_le_right.mp (inf_le_right.trans hCW))

/-- The point-plane stabilizer has the source factorization C_G(Z_S)U. -/
theorem LocalAnalysis.strict_plane_stabilizer_factorization
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    centralizer ({z} : Set G) ⊓ M =
      centralizer (ZS (T : Subgroup G) L R : Set G) ⊔ sourceClosure (T : Subgroup G) L R z := by
  let U := sourceClosure (T : Subgroup G) L R z
  let S := ZS (T : Subgroup G) L R
  let := h611.ZS_elementary
  have hcard : Nat.card S = 4 := (h611.natural_ZS_geometry hnatural).2.1
  let : Nontrivial S := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour S := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  have hSU : S ≤ U := hstrict.le.trans inf_le_left
  have hUS : U ≤ normalizer (S : Set G) := by
    apply le_normalizer_iff_commutator_le_right.mpr
    exact ((commutator_mono le_rfl (hSU.trans A.closure_le_core)).trans
      A.closure_core_commutator).trans (zpowers_le.mpr hz)
  have hUH : U ≤ centralizer ({z} : Set G) := map_subtype_le _
  have hn : ¬ U ≤ centralizer (S : Set G) := by
    intro hh
    have hSC : S ≤ (center U).map U.subtype := by
      intro s hs
      refine ⟨⟨s, hSU hs⟩, mem_center_iff.mpr ?_, rfl⟩
      intro u
      exact Subtype.ext (hh u.property s hs).symm
    have hSZ : S ≤ zpowers z := by
      rw [← A.strict_layer_center_intersection h611 hnatural hz horder hstrict]
      exact le_inf hSC inf_le_left
    have hc := card_le_of_le hSZ
    rw [hcard, Nat.card_zpowers, horder] at hc
    omega
  have hz0 : (⟨z, hz⟩ : S) ≠ 1 := by
    intro he
    have hh : z = 1 := congrArg Subtype.val he
    rw [hh, orderOf_one] at horder
    contradiction
  rw [← A.plane_normalizer, inf_comm]
  exact kleinFour_point_stabilizer_eq_centralizer_sup S U ⟨z, hz⟩ hz0 hUS hUH hn

/-- The dotted image of H∩M is precisely the image of the plane centralizer. -/
theorem LocalAnalysis.strict_stabilizer_image_eq
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R) :
    let H := centralizer ({z} : Set G)
    let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
    (M.subgroupOf H).map q = ((centralizer (ZS (T : Subgroup G) L R : Set G)).subgroupOf H).map q := by
  let H := centralizer ({z} : Set G)
  let U := sourceClosure (T : Subgroup G) L R z
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  have hC := plane_centralizer_le_H (T : Subgroup G) L R z hz
  have he : M.subgroupOf H = (H ⊓ M).subgroupOf H := by ext x; exact ⟨fun h => ⟨x.property,h⟩, And.right⟩
  change (M.subgroupOf H).map q = _
  rw [he, A.strict_plane_stabilizer_factorization h611 hnatural hz horder hstrict,
    subgroupOf_sup hC (show U ≤ H from map_subtype_le _), Subgroup.map_sup]
  have hker : (U.subgroupOf H).map q = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (by
      rw [QuotientGroup.ker_mk']
      exact A.strict_closure_le_dotted_kernel h611 hnatural hz horder hstrict)
  rw [hker, sup_bot_eq]

/-- Source 6.2.18(1), retaining both actual actors and relative normality. -/
theorem LocalAnalysis.strict_crossing_normal_in_layer_centralizer
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    let C := centralizer (strictLayerImage (T : Subgroup G) L R z : Set (StrictActor (T : Subgroup G) L R z))
    strictCrossingImage (T : Subgroup G) L R z d ≤ C ∧
    ((strictCrossingImage (T : Subgroup G) L R z d).subgroupOf C).Normal ∧
    strictCrossingCenterImage (T : Subgroup G) L R z d ≤ strictCrossingImage (T : Subgroup G) L R z d ∧
    ((strictCrossingCenterImage (T : Subgroup G) L R z d).subgroupOf C).Normal := by
  let H := centralizer ({z} : Set G)
  let C := centralizer (ZS (T : Subgroup G) L R : Set G)
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  have hC := plane_centralizer_le_H (T : Subgroup G) L R z hz
  have he : centralizer (strictLayerImage (T : Subgroup G) L R z : Set (StrictActor (T : Subgroup G) L R z)) =
      (C.subgroupOf H).map q := by
    rw [← A.strict_stabilizer_image_eq h611 hnatural hz horder hstrict,
      ← A.strict_layerImage_centralizer_preimage h611 hnatural hz horder hstrict,
      Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]; exact le_top)]
  have hXC : strictCrossingGroup (T : Subgroup G) L R z d ≤ C := inf_le_right
  have hZX := strictCrossingCenter_le_group h611 hz hd
  have hZn := (strict_plane_centralizer_normalizes_crossing h611 hz hd).2
  have hXn := (strict_plane_centralizer_normalizes_crossing h611 hz hd).1
  have hn (D : Subgroup G) (hDC : D ≤ C) (hCD : C ≤ normalizer (D : Set G)) :
      ((D.subgroupOf H).map q).subgroupOf ((C.subgroupOf H).map q) |>.Normal := by
    apply (normal_subgroupOf_iff_le_normalizer (map_mono (comap_mono hDC))).mpr
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    change C.subgroupOf H ≤ normalizer (D.subgroupOf H : Set H)
    rw [← subgroupOf_normalizer_eq (show D ≤ H from hDC.trans hC)]
    exact comap_mono hCD
  rw [he]
  exact ⟨map_mono (comap_mono hXC), hn _ hXC hXn,
    map_mono (comap_mono hZX), hn _ (hZX.trans hXC) hZn⟩


/-- G.11.1(4): X-dot is normal in the image of the original Sylow subgroup.
Its containment follows from maximality of that Sylow image and elementarity. -/
theorem LocalAnalysis.strict_crossing_normal_in_sylow
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hd : d ∈ normalizer (ZS (T : Subgroup G) L R : Set G)) :
    let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
    let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
    strictCrossingImage (T : Subgroup G) L R z d ≤ (S : Subgroup (StrictActor (T : Subgroup G) L R z)) ∧
    ((strictCrossingImage (T : Subgroup G) L R z d).subgroupOf (S : Subgroup (StrictActor (T : Subgroup G) L R z))).Normal := by
  let q := QuotientGroup.mk' (strictQuotientAction (T : Subgroup G) L R z).ker
  let S := (T.subtype hTH).mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  let X := strictCrossingImage (T : Subgroup G) L R z d
  let C := centralizer (strictLayerImage (T : Subgroup G) L R z : Set (StrictActor (T : Subgroup G) L R z))
  obtain ⟨hXC, hn, _, _⟩ := A.strict_crossing_normal_in_layer_centralizer h611 hnatural hz horder hstrict hd
  have hSC : (S : Subgroup (StrictActor (T : Subgroup G) L R z)) ≤ C := by
    rintro _ ⟨t, ht, rfl⟩
    have hm : t ∈ M.subgroupOf (centralizer ({z} : Set G)) := h611.sylow_le ht
    rw [← A.strict_layerImage_centralizer_preimage h611 hnatural hz horder hstrict] at hm
    exact hm
  have hSX := hSC.trans ((normal_subgroupOf_iff_le_normalizer hXC).mp hn)
  let := A.strict_crossingImage_elementary h611 hnatural hz horder hstrict hd
  have hXS : X ≤ (S : Subgroup (StrictActor (T : Subgroup G) L R z)) :=
    sup_eq_right.mp (S.is_maximal'
      ((IsElementaryAbelian.isPGroup 2 X).to_sup_of_normal_left' S.isPGroup' hSX) le_sup_right)
  exact ⟨hXS, (normal_subgroupOf_iff_le_normalizer hXS).mpr hSX⟩

/-- The actual crossing image fixes the entire marked source line pointwise. -/
theorem strict_crossingImage_fixes_sourceLine
    (_h611 : Hypothesis611 κ T L M R n) (_hz : z ∈ ZS (T : Subgroup G) L R)
    [IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L R z)]
    (d : G) {a : StrictActor (T : Subgroup G) L R z}
    (ha : a ∈ strictCrossingImage (T : Subgroup G) L R z d)
    {v : Additive (StrictVectorQuotient (T : Subgroup G) L R z)}
    (hv : v ∈ strictSourceLine (T : Subgroup G) L R z) :
    strictRepresentation (T : Subgroup G) L R z a v = v := by
  obtain ⟨h, hh, rfl⟩ := ha
  obtain ⟨s, hs, he⟩ := hv
  have he' : v = Additive.ofMul (QuotientGroup.mk' (center (sourceClosure (T : Subgroup G) L R z)) s) :=
    (congrArg Additive.ofMul he).symm
  rw [he', strictRepresentation_mk, toMul_ofMul, strictQuotientAction_mk]
  congr 2
  apply Subtype.ext
  change (h : G) * (s : G) * (h : G)⁻¹ = s
  exact mul_inv_eq_iff_eq_mul.mpr (hh.2 s hs).symm

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
