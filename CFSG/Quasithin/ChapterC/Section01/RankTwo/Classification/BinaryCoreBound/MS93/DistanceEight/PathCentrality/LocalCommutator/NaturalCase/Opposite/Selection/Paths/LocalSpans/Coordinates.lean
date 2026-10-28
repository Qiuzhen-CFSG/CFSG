module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.Paths.Source

/-!
# Coordinates and the exact moving kernel for the local conjugate spans

Put W = localZSpan R a c and J = Z_c[W,G_c]. The supplied edge identity
first proves [W,Q_c] ≤ Z_c: each original displacement lies in the central
edge, and conjugation preserves Z_c. Consequently the radical of the frame
is exactly Z_c. Its splitting, with the actual residual-fixed denominator,
then gives J ∩ B_c = Z_c.

The opposite coordinates on W retain the frame's projection and natural
marking. Surjectivity of the image of K ∩ J now lifts to J ≤ K whenever
Z_c ≤ K. One good orbit member supplies the remaining fixed summand. This
avoids identifying W with the full radius group, or lifting a quotient
surjectivity without controlling its kernel.

The bad-image and good-image calculations are not asserted here. The parent
module applies these lifting results to their precise remaining coordinate
premises and to the existing geometric path assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1)(1), pp.890–891.
The fixed/radical comparison reuses the generic section-coordinate proof
from FirstPairing/Orientation/QuotientApplication/Verification/NaturalGeneration.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
open RankOnePairing
open Escape.PairingControl.FirstPairing.Orientation.QuotientApplication.NaturalGeneration
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
variable {geometry : Geometry R} {a c : Vertex R}

/-- Dual coordinates on the actual W, with the original frame marking. -/
noncomputable def coordinates (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) :
    localZSpan R a c →* Multiplicative (Fin 3 → ZMod 2) :=
  (spanDual source hc hd hb f hop).coordinates.comp
    (subgroupOfEquivOfLe f.sectionData.local_group).symm.toMonoidHom

/-- These are coordinates on the full three-dimensional quotient. -/
theorem coordinates_surjective (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) :
    Function.Surjective (coordinates source hc hd hb f hop) :=
  (spanDual source hc hd hb f hop).surjective.comp
    (subgroupOfEquivOfLe f.sectionData.local_group).symm.surjective

/-- The kernel is W ∩ B_c, not a substitute denominator. -/
theorem coordinates_kernel (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation) :
    (coordinates source hc hd hb f hop).ker =
      (B R c (geometry.Z_normal c)).subgroupOf (localZSpan R a c) := by
  ext x
  change (spanDual source hc hd hb f hop).coordinates _ = 1 ↔ _
  rw [← MonoidHom.mem_ker, (spanDual source hc hd hb f hop).kernel]
  rfl

/-- Image of H ∩ W in the marked dual three-space. -/
noncomputable def coordinateImage (source : LocalSource L R) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) (hb : 2 < geometry.b R)
    (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (H : Subgroup (FreeAmalgam R)) : Subgroup (Multiplicative (Fin 3 → ZMod 2)) :=
  (H.subgroupOf (localZSpan R a c)).map (coordinates source hc hd hb f hop)

/-- The moving preimage after the edge identities kill the Q_c radical. -/
noncomputable def movingSpan (a c : Vertex R) : Subgroup (FreeAmalgam R) :=
  Z R c ⊔ ⁅localZSpan R a c, stabilizer R c⁆

theorem movingSpan_le (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2) : movingSpan a c ≤ localZSpan R a c :=
  sup_le (center_Z_le_span hc hd)
    (le_normalizer_iff_commutator_le_left.mp (localZSpan_normalized R a c))

/-- The supplied edge identity propagates to every generator of W. -/
theorem edgeData_span_commutator_le_Z
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (s : EdgeData a c) :
    ⁅localZSpan R a c, Q R c⁆ ≤ Z R c := by
  have ht : color R s.neighbor = true := by
    have hn := adjacent_color_ne R s.adjacent_center
    cases h : color R s.neighbor <;> simp_all
  have hseed : ⁅Z R a, Q R c⁆ ≤ Z R c := by
    apply (commutator_mono le_rfl (Q_le_adjacent_h R ht s.adjacent_center)).trans
    change edgeCommutator R a s.neighbor ≤ Z R c
    rw [s.edge_eq]
    exact le_normalizer_iff_commutator_le_left.mp
      ((show Q R s.neighbor ≤ stabilizer R c from
        fun _ hx => hx.2 c (adjacent_symm R s.adjacent_center)).trans (Z_normalized R c))
  rw [span_commutator_eq_conjugates hc hd.le hb]
  apply iSup_le
  intro g
  exact (map_mono hseed).trans
    (mem_normalizer_iff_map_conj_eq.mp
      (Z_normalized R c ((stabilizer R c).inv_mem g.property))).le

private theorem local_generation (source : LocalSource L R) (hc : color R c = false) :
    pResidual 2 (stabilizer R c) ⊔ (Q R c).subgroupOf (stabilizer R c) = ⊤ := by
  apply map_injective (stabilizer R c).subtype_injective
  rw [Subgroup.map_sup, map_subgroupOf_eq_of_le
    (show Q R c ≤ stabilizer R c from fun _ hx => hx.1),
    ← MonoidHom.range_eq_map, range_subtype]
  exact source.local_generation c hc

/-- The exact kernel required when lifting products of conjugate differences. -/
theorem movingSpan_inf_fixed (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (s : EdgeData a c) :
    movingSpan a c ⊓ B R c (geometry.Z_normal c) = Z R c := by
  let S := stabilizer R c
  let W := (localZSpan R a c).subgroupOf S
  let Qc := (Q R c).subgroupOf S
  let Zc := (Z R c).subgroupOf S
  let := finite_stabilizer R c
  let := geometry.Z_normal c
  have hW : localZSpan R a c ≤ S := f.sectionData.local_group
  have hQc : Q R c ≤ S := fun _ hx => hx.1
  have hrad : Escape.radicalPreimage Qc W Zc = Zc := by
    apply sup_eq_left.mpr
    apply (map_le_iff_le_comap).mp
    rw [map_commutator, map_subgroupOf_eq_of_le hW,
      map_subgroupOf_eq_of_le hQc]
    exact edgeData_span_commutator_le_Z hc hd hb s
  have hfixed := fixed_eq_radical_fixed f.sectionData.module_section
    (isPPerfect_pResidual 2)
    (((source.V_isPGroup geometry hb c hc).to_le (localZSpan_le_V R hd.le)).comap_subtype)
    (local_generation source hc)
  have hinter := f.sectionData.module_section.intersection
  rw [← hfixed, span_fixed_eq (geometry := geometry) hd] at hinter
  change (Escape.radicalPreimage Qc W Zc ⊔ ⁅W, (⊤ : Subgroup S)⁆) ⊓
    (localZSpan R a c ⊓ B R c (geometry.Z_normal c)).subgroupOf S = _ at hinter
  rw [hrad] at hinter
  have hm : (Zc ⊔ ⁅W, (⊤ : Subgroup S)⁆).map S.subtype = movingSpan a c := by
    rw [Subgroup.map_sup, map_commutator, map_subgroupOf_eq_of_le (Z_le_stabilizer R c),
      map_subgroupOf_eq_of_le hW, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have h := congrArg (Subgroup.map S.subtype) hinter
  rw [Subgroup.map_inf _ _ _ S.subtype_injective, hm,
    map_subgroupOf_eq_of_le (inf_le_left.trans hW),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R c)] at h
  rw [← inf_assoc, inf_eq_left.mpr (movingSpan_le hc hd)] at h
  exact h

omit [Finite M] in
/-- Killing the conjugation commutators makes the original seed generate W. -/
theorem span_le_of_seed_and_commutator {a c : Vertex R}
    (K : Subgroup (FreeAmalgam R)) (hseed : Z R a ≤ K)
    (hcomm : ⁅localZSpan R a c, stabilizer R c⁆ ≤ K) : localZSpan R a c ≤ K := by
  apply iSup_le
  intro g
  rw [Z_act]
  rintro _ ⟨x, hx, rfl⟩
  have h := K.mul_mem
    (hcomm (commutator_comm (stabilizer R c) (localZSpan R a c) ▸
      commutator_mem_commutator ((stabilizer R c).inv_mem g.property)
        (Z_le_localZSpan R a c hx))) (hseed hx)
  simpa only [commutatorElement_def, inv_inv, inv_mul_cancel_right,
    MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply] using h

omit [Finite M] in
/-- Any good member of the original orbit covers the fixed summand. -/
theorem span_le_moving_sup_good {a c t u : Vertex R}
    (hex : ∃ g : stabilizer R c, GoodConjugate a c t u g) :
    localZSpan R a c ≤ movingSpan a c ⊔ goodConjugateSpan a c t u := by
  obtain ⟨g, hg⟩ := hex
  have he := CriticalCase.span_eq_of_local_conjugator (a := a) g.property
  rw [← he]
  apply span_le_of_seed_and_commutator
  · apply le_trans (b := goodConjugateSpan a c t u) _ le_sup_right
    exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)
  · rw [he]
    exact le_sup_right.trans le_sup_left

/-- Restriction to W preserves this join because its first factor lies in W
and normalizes the incident radius group. -/
theorem coordinateImage_join_radius (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    {u : Vertex R} (hcu : Adjacent R c u)
    (K : Subgroup (FreeAmalgam R)) (hK : K ≤ localZSpan R a c) :
    coordinateImage source hc hd hb f hop (K ⊔ V R u) =
      coordinateImage source hc hd hb f hop K ⊔
        coordinateImage source hc hd hb f hop (V R u) := by
  have he : (K ⊔ V R u).subgroupOf (localZSpan R a c) =
      K.subgroupOf (localZSpan R a c) ⊔ (V R u).subgroupOf (localZSpan R a c) := by
    apply le_antisymm
    · intro x hx
      have hxmul : (x : FreeAmalgam R) ∈
          (K : Set (FreeAmalgam R)) * (V R u : Set (FreeAmalgam R)) := by
        rw [← span_join_radius_eq_mul hc hd hb hcu K hK]
        exact hx
      obtain ⟨y, hy, z, hz, heq⟩ := hxmul
      have hzW : z ∈ localZSpan R a c := by
        have h := (localZSpan R a c).mul_mem
          ((localZSpan R a c).inv_mem (hK hy)) x.property
        rwa [← heq, inv_mul_cancel_left] at h
      have heq' : (⟨y, hK hy⟩ : localZSpan R a c) * ⟨z, hzW⟩ = x := Subtype.ext heq
      rw [← heq']
      exact (K.subgroupOf (localZSpan R a c) ⊔
        (V R u).subgroupOf (localZSpan R a c)).mul_mem (mem_sup_left hy) (mem_sup_right hz)
    · exact sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)
  exact (congrArg (Subgroup.map (coordinates source hc hd hb f hop)) he).trans (map_sup _ _ _)

/-- Lift a full image of K ∩ J using J ∩ B_c = Z_c and Z_c ≤ K. -/
theorem movingSpan_le_of_coordinateImage (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (s : EdgeData a c) (K : Subgroup (FreeAmalgam R)) (hZ : Z R c ≤ K)
    (himage : coordinateImage source hc hd hb f hop (K ⊓ movingSpan a c) = ⊤) :
    movingSpan a c ≤ K := by
  intro x hx
  let x₀ : localZSpan R a c := ⟨x, movingSpan_le hc hd hx⟩
  obtain ⟨y, hy, he⟩ := (show coordinates source hc hd hb f hop x₀ ∈
      coordinateImage source hc hd hb f hop (K ⊓ movingSpan a c) from himage.symm ▸ mem_top _)
  have hker : x₀ * y⁻¹ ∈ (coordinates source hc hd hb f hop).ker := by
    change coordinates source hc hd hb f hop (x₀ * y⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  rw [coordinates_kernel] at hker
  have hZxy : x * (y : FreeAmalgam R)⁻¹ ∈ Z R c := by
    rw [← movingSpan_inf_fixed source hc hd hb f s]
    exact ⟨(movingSpan a c).mul_mem hx ((movingSpan a c).inv_mem hy.2), hker⟩
  have hprod := K.mul_mem (hZ hZxy) hy.1
  change x * (y : FreeAmalgam R)⁻¹ * (y : FreeAmalgam R) ∈ K at hprod
  simpa only [inv_mul_cancel_right] using hprod

/-- A proper coordinate image obstructs ambient containment. -/
theorem not_le_of_coordinateImage_ne_top (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (K : Subgroup (FreeAmalgam R))
    (himage : coordinateImage source hc hd hb f hop K ≠ ⊤) : ¬ localZSpan R a c ≤ K := by
  intro h
  apply himage
  unfold coordinateImage
  rw [subgroupOf_eq_top.mpr h]
  exact map_top_of_surjective _ (coordinates_surjective source hc hd hb f hop)

/-- The actual left-conjugation equation, with the original projection. -/
theorem coordinates_conjugation (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (g : stabilizer R c) (x y : localZSpan R a c)
    (hy : (y : FreeAmalgam R) = g * (x : FreeAmalgam R) * (g : FreeAmalgam R)⁻¹) :
    (coordinates source hc hd hb f hop y).toAdd =
      ((f.naturalU.marking (f.sectionData.projection g))⁻¹).val.transpose.mulVec
        (coordinates source hc hd hb f hop x).toAdd :=
  (spanDual source hc hd hb f hop).action g (mem_top _) _ _ (Subtype.ext hy)

/-- The inverse conjugation used by the right-coset action on vertices. -/
theorem coordinates_inverse_conjugation (source : LocalSource L R)
    (hc : color R c = false) (hd : (cosetGraph R).dist a c = 2)
    (hb : 2 < geometry.b R) (f : FrameAt a c) (hop : ¬ f.SameOrientation)
    (g : stabilizer R c) (x y : localZSpan R a c)
    (hy : (y : FreeAmalgam R) = (g : FreeAmalgam R)⁻¹ * (x : FreeAmalgam R) * g) :
    (coordinates source hc hd hb f hop y).toAdd =
      (f.naturalU.marking (f.sectionData.projection g)).val.transpose.mulVec
        (coordinates source hc hd hb f hop x).toAdd := by
  have h := coordinates_conjugation source hc hd hb f hop g⁻¹ x y (by
    simpa only [Subgroup.coe_inv, inv_inv] using hy)
  simpa only [map_inv, inv_inv] using h

omit [Finite M] in
/-- Every transported original seed is fixed modulo Z_c by its own edge kernel. -/
theorem conjugate_seed_fixed_mod_Z (s : EdgeData a c) (g : stabilizer R c) :
    ⁅Z R (act R g a), Q R (act R g s.neighbor)⁆ ≤ Z R c := by
  have h : ⁅Z R a, Q R s.neighbor⁆ ≤ Z R c := by
    change edgeCommutator R a s.neighbor ≤ _
    rw [s.edge_eq]
    exact le_normalizer_iff_commutator_le_left.mp
      ((show Q R s.neighbor ≤ stabilizer R c from
        fun _ hx => hx.2 c (adjacent_symm R s.adjacent_center)).trans (Z_normalized R c))
  rw [Z_act, Q_act, ← map_commutator]
  exact (map_mono h).trans (mem_normalizer_iff_map_conj_eq.mp
    (Z_normalized R c ((stabilizer R c).inv_mem g.property))).le

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.NaturalCase.Opposite.Selection.LocalSpans
