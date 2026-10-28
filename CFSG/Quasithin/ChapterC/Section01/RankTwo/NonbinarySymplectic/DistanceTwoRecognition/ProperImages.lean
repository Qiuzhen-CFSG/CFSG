module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NormalizerComparison
public import Theory.SpecificGroups.SymplecticFour.Sylow.NonsolvableOvergroups
public import Theory.SpecificGroups.SymplecticFour.SylowFixedCubic
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane.NoNaturalSubmodule

/-!
# Proper replacement images in the original parabolic radicals

The original odd-index witness supplies a full Sylow subgroup in the
normalizer of the replacement image D. If its two-core B is not Sylow,
the normalizer is nonsolvable and contains the determinant-one factor of
the parabolic normalizing B. The invariant subgroup lattice then puts D
either equal to B or inside its central root.

The literal edge index in the holomorph amalgam bounds each critical image
by D. Reciprocal critical action gives |D| ≥ q, so at distance two the
proper alternatives are the full long or short root, with their original
symplectic coordinates. If the original radical image is not Sylow, the
replacement has the same full normalizer as that original image. Lifting
through the constructed projection proves that the normalizer two-core is
exactly the original radical restricted to the replacement overgroup.

The proper root alternatives and the original Sylow alternative remain;
this module does not identify D with B or assert the field restriction.
Source: Meierfrankenfeld--Stellmacher (1993), (3.7), printed pp.872--877;
Aschbacher--Smith C.1.31--32, printed pp.135--136. The concrete invariant
lattices are the point and plane calculations of F.1.12.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

omit [CharP F 2] in
private theorem sylow_le_of_odd_index (A : Subgroup (Sp F)) (ho : Odd A.index) :
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) ≤ A := by
  let P : Sylow 2 A := Classical.choice inferInstance
  have hi : ¬ 2 ∣ ((P : Subgroup A).map A.subtype).index := by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index ho.not_two_dvd_nat
  exact ⟨(P.isPGroup'.map A.subtype).toSylow hi,map_subtype_le _⟩

include h in
omit [Finite H] in
private theorem solvable_odd_index_core_sylow (A : Subgroup (Sp F))
    (ho : Odd A.index) (hs : Group.IsSolvable A) :
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = A.pCoreIn 2 := by
  obtain ⟨S,hS⟩ := sylow_le_of_odd_index A ho
  have hlarge : 2 < Nat.card F := by
    rw [h.field_card]
    exact (show (2 : ℕ)^1 < 2^n from Nat.pow_lt_pow_right (by decide) h.nonbinary)
  have hn := solvable_sylow_overgroup_normalizes hlarge S A hs hS
  exact ⟨S,le_antisymm (le_pCoreIn_of_normalizes S.isPGroup' hS hn)
    (by
      have hh := pCoreIn_le_sylow A (S.subtype hS)
      rw [Sylow.coe_subtype,subgroupOf_map_subtype] at hh
      exact hh.trans inf_le_left)⟩

include h in
omit [Finite H] in
private theorem plane_center_le_root :
    (center (planeLocal (F := F))).map planeLocal.subtype ≤ RootSubgroup.group 4 := by
  rintro _ ⟨x,hx,rfl⟩
  have hxr : x ∈ Plane.radical :=
    (center_le_centralizer _).trans (planeNaturalExtension h.field_card h.nonbinary).centralizer_eq.le hx
  let q : Plane.radical (F := F) := ⟨x,hxr⟩
  obtain ⟨z,hz⟩ := (Plane.mem_center_subgroupOf_iff_alternating q).mp hx
  apply (RootSubgroup.mem_group_iff 4 x.val).mpr
  refine ⟨z,?_⟩
  apply Subtype.ext
  have he := Plane.radical_matrix q
  change x.val.val = _ at he
  change q.val.val.val.toBlocks₁₂ = _ at hz
  rw [he,hz]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rootElement,rootMatrix,Matrix.fromBlocks,Matrix.single]

include h in
omit [Finite H] in
private theorem point_invariant_radical_small_or_full
    (D : Subgroup (Sp F)) (hD : D ≤ pointRadicalAmbient)
    (hn : pointLocal ≤ normalizer (D : Set (Sp F))) :
    D ≤ RootSubgroup.group 0 ∨ D = pointRadicalAmbient := by
  have hDL : D ≤ pointLocal := hD.trans (map_subtype_le _)
  let W := D.subgroupOf (pointLocal (F := F))
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  have hW : W ≤ pointRadical := by
    intro x hx
    exact (mem_map_iff_mem pointLocal.subtype_injective).mp (hD hx)
  have hm : W.map pointLocal.subtype = D := map_subgroupOf_eq_of_le hDL
  rcases PointRadicalAction.normal_radical_dichotomy h.field_card h.nonbinary W hW with hc | he
  · left
    rw [←PointRadicalAction.center_eq_root h.field_card h.nonbinary,←hm]
    exact map_mono hc
  · right
    rw [←hm,he]

include h in
omit [Finite H] in
private theorem plane_invariant_radical_small_or_full
    (D : Subgroup (Sp F)) (hD : D ≤ planeRadicalAmbient)
    (hn : planeLocal ≤ normalizer (D : Set (Sp F))) :
    D ≤ RootSubgroup.group 4 ∨ D = planeRadicalAmbient := by
  have hDL : D ≤ planeLocal := hD.trans (map_subtype_le _)
  let W := D.subgroupOf (planeLocal (F := F))
  let : W.Normal := (normal_subgroupOf_iff_le_normalizer hDL).mpr hn
  have hW : W ≤ Plane.radical := by
    intro x hx
    exact (mem_map_iff_mem planeLocal.subtype_injective).mp (hD hx)
  have hm : W.map planeLocal.subtype = D := map_subgroupOf_eq_of_le hDL
  rcases Plane.normal_radical_le_center_or_eq h.field_card h.nonbinary W hW with hc | he
  · left
    rw [←hm]
    exact (map_mono hc).trans (plane_center_le_root h)
  · right
    rw [←hm,he]

include h d

/-- A solvable replacement normalizer has a full ambient Sylow as its two-core. -/
theorem replacement_normalizer_solvable_core_sylow
    (hs : Group.IsSolvable (normalizer
      ((d.ambient.subgroupOf K).map (componentProjection h) : Set (Sp F)))) :
    ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Sp F))).pCoreIn 2 :=
  solvable_odd_index_core_sylow h _ (replacement_marked_normalizer_odd h d) hs

/-- Outside the Sylow-normalizer-core case, a proper replacement image lies
in a central root, in the same coordinates as its full normalizer core. -/
theorem replacement_marked_radical_root_or_full
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Sp F))).pCoreIn 2) :
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    let B := (normalizer (D : Set (Sp F))).pCoreIn 2
    D = B ∨ ∃ u : Sp F,
      (B.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom ≤ RootSubgroup.group 0) ∨
      (B.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom ≤ RootSubgroup.group 4) := by
  let D := (d.ambient.subgroupOf K).map (componentProjection h)
  let N := normalizer (D : Set (Sp F))
  let B := N.pCoreIn 2
  have hnsol : ¬ Group.IsSolvable N := fun hs =>
    hnsyl (replacement_normalizer_solvable_core_sylow h d hs)
  obtain ⟨S,hSN⟩ := sylow_le_of_odd_index N (replacement_marked_normalizer_odd h d)
  have hNB : N ≤ normalizer (B : Set (Sp F)) :=
    N.le_normalizer.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hDB : D ≤ B := (replacement_marked_normalizer_core_bounds h d).1
  rcases replacement_marked_normalizer_core_alternatives h d g hb with ⟨u,hu⟩ | hs
  swap
  · exact (hnsyl hs).elim
  let e := MulAut.conj u
  let N' := N.map e.toMonoidHom
  let D' := D.map e.toMonoidHom
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hS' : (S' : Subgroup (Sp F)) ≤ N' := map_mono hSN
  have hnsol' : ¬ Group.IsSolvable N' := by
    intro hs
    let := hs
    exact hnsol (Group.isSolvable_of_isSolvable_injective
      (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
      (N.equivMapOfInjective e.toMonoidHom e.injective).injective)
  have hn' : N' ≤ normalizer (D' : Set (Sp F)) := by
    change (normalizer (D : Set (Sp F))).map e.toMonoidHom ≤ _
    rw [map_equiv_normalizer_eq]
  have hsmall (r : Fin 8) (P : Subgroup (Sp F))
      (hBP : B.map e.toMonoidHom = P) (hDP : D' ≤ RootSubgroup.group r ∨ D' = P) :
      D = B ∨ D' ≤ RootSubgroup.group r := by
    rcases hDP with hh | hh
    · exact Or.inr hh
    · left
      apply map_injective (f := e.toMonoidHom) e.injective
      exact hh.trans hBP.symm
  rcases hu with ⟨hB,hN⟩ | ⟨hB,hN⟩
  · have hNP : N' ≤ pointParabolic := hN ▸ map_mono hNB
    have hlocal := nonsolvable_point_overgroup_contains_local S' N' hS' hNP hnsol'
    have hDP : D' ≤ pointRadicalAmbient := hB ▸ map_mono hDB
    rcases hsmall 0 _ hB
      (point_invariant_radical_small_or_full h D' hDP (hlocal.trans hn')) with he | he
    · exact Or.inl he
    · exact Or.inr ⟨u,Or.inl ⟨hB,he⟩⟩
  · have hNP : N' ≤ planeParabolic := hN ▸ map_mono hNB
    have hlocal := nonsolvable_plane_overgroup_contains_local S' N' hS' hNP hnsol'
    have hDP : D' ≤ planeRadicalAmbient := hB ▸ map_mono hDB
    rcases hsmall 4 _ hB
      (plane_invariant_radical_small_or_full h D' hDP (hlocal.trans hn')) with he | he
    · exact Or.inl he
    · exact Or.inr ⟨u,Or.inr ⟨hB,he⟩⟩

open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

omit [Finite F] [CharP F 2] in
/-- The radical quotient index is unchanged on every incident edge, using
the literal core and radical embeddings into the holomorph amalgam. -/
theorem replacement_edge_index {a t : Vertex d.radical}
    (ha : color d.radical a = false) (hat : Adjacent d.radical a t) :
    (Q d.radical a).relIndex (Q d.radical t) =
      (pCore 2 d.overgroup).relIndex d.radical := by
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ :=
    (adjacent_iff_exists_common d.radical a t).mp hat
  · have hma := Q_act d.radical u (alpha d.radical)
    have hmb := Q_act d.radical u (beta d.radical)
    simp only [alpha,beta,act_mVertex,act_hVertex,one_mul] at hma hmb
    rw [hma,hmb,relIndex_map_map_of_injective _ _ (MulAut.conj u⁻¹).injective]
    change (Q d.radical (alpha d.radical)).relIndex (Q d.radical (beta d.radical)) = _
    rw [Q_alpha d.radical (replacement_isPGroup h d) (replacement_core_le h d),
      Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective d.radical)]
  · change true = false at ha
    cases ha

/-- Every distance-two critical image is bounded by the actual replacement
radical image in the supplied symplectic quotient. -/
theorem replacement_critical_index_le_radical_card
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2) :
    (Q d.radical a).relIndex (Z d.radical z) ≤
      Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) := by
  have hd : (cosetGraph d.radical).dist a z = 2 :=
    path.critical.1.trans ((g.distance_constant _ path.start_color).trans hb)
  obtain ⟨t,hat,hzt⟩ := exists_common_neighbor_of_dist_two d.radical a z hd
  have hZt : Z d.radical z ≤ Q d.radical t :=
    Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
        g.distance_constant z path.end_color]
      change 1 < g.b d.radical
      omega)
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  have hi := relIndex_le_of_le_right (H := Q d.radical a) hZt index_ne_zero_of_finite
  rw [replacement_edge_index h d path.start_color hat] at hi
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g (by omega)
  rw [←hk,relIndex_ker,he] at hi
  exact hi

/-- At distance two the full replacement image has order at least the
original field size. -/
theorem replacement_marked_radical_card_ge_field
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    Nat.card F ≤ Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) := by
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := g)
    (a := alpha d.radical) rfl
  rw [h.field_card]
  exact (replacement_critical_indices_ge_field h d path (by omega)).2.trans
    (replacement_critical_index_le_radical_card h d path hb)

/-- At distance two the small alternative is a full root subgroup, rather
than an unspecified binary subgroup of a root. -/
theorem replacement_marked_radical_eq_core_or_root
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Sp F))).pCoreIn 2) :
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    let B := (normalizer (D : Set (Sp F))).pCoreIn 2
    D = B ∨ ∃ u : Sp F,
      (B.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom = RootSubgroup.group 0) ∨
      (B.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom = RootSubgroup.group 4) := by
  rcases replacement_marked_radical_root_or_full h d g (by omega) hnsyl with he | ⟨u,hu⟩
  · exact Or.inl he
  right
  refine ⟨u,?_⟩
  have hcard := replacement_marked_radical_card_ge_field h d g hb
  have hfull (r : Fin 8)
      (hl : ((d.ambient.subgroupOf K).map (componentProjection h)).map
        (MulAut.conj u).toMonoidHom ≤ RootSubgroup.group r) :
      ((d.ambient.subgroupOf K).map (componentProjection h)).map
        (MulAut.conj u).toMonoidHom = RootSubgroup.group r := by
    apply eq_of_le_of_card_ge hl
    rw [RootSubgroup.card,card_map_of_injective (MulAut.conj u).injective]
    exact hcard
  rcases hu with ⟨hB,hD⟩ | ⟨hB,hD⟩
  · exact Or.inl ⟨hB,hfull 0 hD⟩
  · exact Or.inr ⟨hB,hfull 4 hD⟩

/-- Relative to the original odd-index radical, the only proper nonsylow
replacement images are the two central roots in their respective radicals. -/
theorem replacement_original_radical_or_root_or_sylow
    (g : Geometry d.radical) (hb : g.b d.radical = 2) :
    let D := (d.ambient.subgroupOf K).map (componentProjection h)
    let R₀ := (R.subgroupOf K).map (componentProjection h)
    D = R₀ ∨ (∃ u : Sp F,
      (R₀.map (MulAut.conj u).toMonoidHom = pointRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom = RootSubgroup.group 0) ∨
      (R₀.map (MulAut.conj u).toMonoidHom = planeRadicalAmbient ∧
        D.map (MulAut.conj u).toMonoidHom = RootSubgroup.group 4)) ∨
      ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) = R₀ := by
  classical
  dsimp only
  by_cases hs : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)
  · exact Or.inr (Or.inr hs)
  have he := (replacement_marked_normalizer_core_eq_original_or_sylow h d g (by omega)).resolve_right hs
  have hns : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (normalizer ((d.ambient.subgroupOf K).map (componentProjection h) :
        Set (Sp F))).pCoreIn 2 := by rwa [he]
  have hh := replacement_marked_radical_eq_core_or_root h d g hb hns
  dsimp only at hh
  rw [he] at hh
  exact hh.elim Or.inl (Or.inr ∘ Or.inl)


/-- When the original image is not Sylow, the replacement has exactly the
same full parabolic normalizer, even in the proper central-root case. -/
theorem replacement_marked_normalizer_eq_original
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    normalizer ((d.ambient.subgroupOf K).map (componentProjection h) : Set (Sp F)) =
      normalizer ((R.subgroupOf K).map (componentProjection h) : Set (Sp F)) := by
  rcases replacement_original_radical_or_root_or_sylow h d g hb with he | ⟨u,hu⟩ | hs
  · rw [he]
  · apply map_injective (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq]
    rcases hu with ⟨hR,hD⟩ | ⟨hR,hD⟩
    · rw [hD,hR,RootNormalizerResidual.normalizer_zero_eq,
        pointRadicalAmbient_normalizer h.field_card h.nonbinary]
    · rw [hD,hR,RootNormalizerResidual.normalizer_four_eq,
        planeRadicalAmbient_normalizer h.field_card h.nonbinary]
  · exact (hnsyl hs).elim

/-- The original radical restricted to the replacement has its original
image under every compatible replacement projection with the exact kernel. -/
theorem replacement_original_radical_map
    (g : Geometry d.radical) (hb : 0 < g.b d.radical)
    (f : d.overgroup →* Sp F) (hk : f.ker = pCore 2 d.overgroup)
    (hm : ∀ k : K.subgroupOf d.overgroup,
      f k = componentProjection h (subgroupOfEquivOfLe le_sup_left k)) :
    (R.subgroupOf d.overgroup).map f = (R.subgroupOf K).map (componentProjection h) := by
  have hQR : pCore 2 d.overgroup ≤ R.subgroupOf d.overgroup :=
    (replacement_core_le h d).trans (by
      obtain ⟨A,hA,ho,hc,hA',ho',hc',hle,hN⟩ := original_witness_restricted h d
      exact hle)
  apply le_antisymm
  · rintro _ ⟨x,hx,rfl⟩
    have hx' : x ∈ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup :=
      (replacement_inner_of_positive h d g hb).symm ▸ mem_top x
    obtain ⟨k,hkK,q,hq,he⟩ := mem_sup_of_normal_right.mp hx'
    have hkR : k ∈ R.subgroupOf d.overgroup := by
      have hh := (R.subgroupOf d.overgroup).mul_mem hx
        ((R.subgroupOf d.overgroup).inv_mem (hQR hq))
      simpa only [←he,mul_inv_cancel_right] using hh
    refine ⟨⟨k.val,hkK⟩,hkR,?_⟩
    have hqf : f q = 1 := by
      change q ∈ f.ker
      rwa [hk]
    rw [←he,map_mul,hqf,mul_one]
    exact (hm ⟨k,hkK⟩).symm
  · rintro _ ⟨k,hkR,rfl⟩
    let k' : K.subgroupOf d.overgroup := ⟨⟨k.val,mem_sup_left k.property⟩,k.property⟩
    exact ⟨k'.val,hkR,hm k'⟩

/-- The normalizer comparison holds before quotienting, on the two literal
radicals inside the replacement overgroup. It does not identify those radicals. -/
theorem replacement_normalizer_eq_original_restriction
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    normalizer (d.radical : Set d.overgroup) =
      normalizer (R.subgroupOf d.overgroup : Set d.overgroup) := by
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g (by omega)
  have hR := replacement_original_radical_map h d g (by omega) f hk hm
  have hn := replacement_marked_normalizer_eq_original h d g hb hnsyl
  rw [←he,←hR] at hn
  have hc := congrArg (fun A : Subgroup (Sp F) => A.comap f) hn
  rw [comap_normalizer_eq_of_surjective _ hf,
    comap_map_eq_self (hk.trans_le (replacement_core_le h d)),
    comap_normalizer_eq_of_surjective _ hf] at hc
  have hkR : f.ker ≤ R.subgroupOf d.overgroup :=
    (hk.trans_le (replacement_core_le h d)).trans (by
      obtain ⟨A,hA,ho,hc,hA',ho',hc',hle,hN⟩ := original_witness_restricted h d
      exact hle)
  rwa [comap_map_eq_self hkR] at hc

/-- Thus the two-core of the actual replacement normalizer is the original
radical restricted to it, throughout the nonsylow original branch. -/
theorem replacement_normalizer_core_eq_original_restriction
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h)) :
    (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 =
      R.subgroupOf d.overgroup := by
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g (by omega)
  have hR := replacement_original_radical_map h d g (by omega) f hk hm
  have hB := (replacement_marked_normalizer_core_eq_original_or_sylow h d g
    (by omega)).resolve_right hnsyl
  have hmap : ((normalizer (d.radical : Set d.overgroup)).pCoreIn 2).map f =
      (R.subgroupOf d.overgroup).map f := by
    rw [replacement_normalizer_core_map h d f hf hk,he,hR]
    exact hB
  have hc := congrArg (fun A : Subgroup (Sp F) => A.comap f) hmap
  have hkB : f.ker ≤ (normalizer (d.radical : Set d.overgroup)).pCoreIn 2 :=
    (hk.trans_le (replacement_core_le h d)).trans (replacement_normalizer_core_bounds h d).1
  have hkR : f.ker ≤ R.subgroupOf d.overgroup :=
    hkB.trans (replacement_normalizer_core_bounds h d).2
  rwa [comap_map_eq_self hkB,comap_map_eq_self hkR] at hc

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
