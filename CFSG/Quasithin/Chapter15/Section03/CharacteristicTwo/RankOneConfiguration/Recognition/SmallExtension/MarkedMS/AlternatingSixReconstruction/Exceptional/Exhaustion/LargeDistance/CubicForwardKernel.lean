module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicBackwardPaths
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The full cubic forward kernel and its selected orbit span

At a component vertex a fixed hyperplane of either entire moving cover
forces marked image order at most two and commutator order at most two.
For a two-subgroup the odd quotient E/Q does not affect the index, so this
bounds the literal Q-index without replacing the cubic initial kernel E.

The source forward kernel centralizes the full Baumann slice. The residual
fixes that slice modulo the central starting seed, and the incident edge
normalizes it. Together they prove normalization by the starting stabilizer.
The whole selected orbit span lies in this kernel. A small slice gives its
index bound at the actual second vertex and a commutator line inside the
common edge seed. Relative normal generation bounds the entire span's
commutator, including its action on both inner layers of the original path.
For a nonabelian selected span that line has order two and is noncentral at
the second vertex; the retained natural quotient detects its two-group actor.

The whole-core and literal C.1.32 applications retain the large-slice and
abelian-span alternatives. They discharge all cover, kernel-normalization,
relative-generation and odd-kernel index premises. The selected source
choices, strict slice inequality, R4/R6 noncentrality of (5.11), distance-four
exclusion (5.12), and final reconstruction remain with
qt-e-ms-small-a6-reconstruction. Independent natural exhaustion stays with
qt-e-ms-small-a6-exhaustion-large-distance. No distance bound is asserted.

Source: MS93 (3.3)(ii), pp.866--867; (5.9), pp.920--921; (5.12)(3),
pp.926--927. Adapts Natural.Exhaustion.LargeDistance.SectionFive.SelectedKernel
and ForwardKernelLine to the original cubic kernel and both full covers.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "W" => (⁅centralOmega L R,L.subgroupOf (L ⊔ R)⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local notation "Rg" => edge L R
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
private abbrev coverAction : Representation (ZMod 2) (Equiv.Perm (Fin 6)) (Additive W) := by
  let := h.relative_normal
  exact NormalElementaryQuotient.representation W π
    (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk)
private def coverMap : Additive W →ₗ[ZMod 2] natural (Fin 6) :=
  Classical.choose (CubicAction.moved_natural_projection h e hz hk)
private theorem coverMap_surjective : Function.Surjective (coverMap h e hz hk) :=
  (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).1
private theorem coverMap_equivariant (g : Equiv.Perm (Fin 6)) (v : Additive W) :
    coverMap h e hz hk (coverAction h e hz hk g v) =
      naturalRepresentation (Fin 6) g (coverMap h e hz hk v) := by
  let := h.relative_normal
  obtain ⟨a,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  have he : coverAction h e hz hk (π a) v = Additive.ofMul (MulAut.conjNormal a v.toMul) := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact NormalElementaryQuotient.representation_apply W π
      (CubicEven.projection_surjective h e hz hk) (CubicAction.moved_projection_kernel h e hz hk) a v
  rw [he]
  exact (Classical.choose_spec (CubicAction.moved_natural_projection h e hz hk)).2.2 a v

include h e hz hk in
/-- A fixed hyperplane of the full cover forces image order at most two. -/
theorem cover_small_fixed_index_image (A : Subgroup M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2) :
    Nat.card (A.map π) ≤ 2 := by
  let := h.relative_normal
  have hsmall : fixedCodim (coverAction h e hz hk) (A.map π) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      W π (CubicEven.projection_surjective h e hz hk)
      (CubicAction.moved_projection_kernel h e hz hk)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map π) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction h e hz hk) (naturalRepresentation (Fin 6))
      (coverMap h e hz hk)
      (coverMap_surjective h e hz hk)
      (coverMap_equivariant h e hz hk) (A.map π)).trans hsmall
  by_cases he : A.map π = ⊥
  · rw [he,card_bot]
    decide
  · obtain ⟨t,_,ht,he⟩ :=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map π) he hnat
    rw [he,Nat.card_zpowers,ht.orderOf]

include h e hz hk in
/-- A fixed hyperplane of the whole cover bounds its actual commutator by two. -/
theorem cover_small_fixed_commutator_card (A : Subgroup M)
    (hindex : (centralizer (A : Set M)).relIndex W ≤ 2) :
    Nat.card (⁅W,A⁆ : Subgroup M) ≤ 2 := by
  let U := W
  let B := U ⊔ A
  let := h.relative_normal

  have hUU : U ≤ centralizer (U : Set M) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hfix : U ⊓ centralizer (B : Set M) =
      U ⊓ centralizer (A : Set M) := by
    apply le_antisymm (fun x hx => ⟨hx.1,fun a ha => hx.2 a (mem_sup_right ha)⟩)
    intro x hx
    refine ⟨hx.1,?_⟩
    apply mem_centralizer_iff.mpr
    intro b hb
    have hs : B ≤ centralizer ({x} : Set M) := by
      apply sup_le
      · intro u hu
        rw [mem_centralizer_singleton_iff]
        exact hUU hx.1 u hu
      · intro a ha
        rw [mem_centralizer_singleton_iff]
        exact hx.2 a ha
    exact mem_centralizer_singleton_iff.mp (hs hb)
  have hBindex : (centralizer (B : Set M)).relIndex U ≤ 2 := by
    rw [←inf_relIndex_left, hfix, inf_relIndex_left]
    exact hindex
  have himage : (centralizer (U : Set M)).relIndex B ≤ 2 := by
    change (centralizer (W : Set M)).relIndex B ≤ 2
    rw [←CubicAction.moved_projection_kernel h e hz hk, relIndex_ker]
    exact cover_small_fixed_index_image h e hz hk B hBindex
  have hcard := commutator_card_le_two_of_mutual_centralizer_indices U B
    (by rw [normalizer_eq_top]; exact le_top)
    (le_sup_left.trans B.le_normalizer) himage hBindex
  exact (card_le_of_le (commutator_mono le_rfl (show A ≤ B from le_sup_right))).trans hcard

include h e hz hk in
/-- The full-cover bound in the literal coordinates of any component vertex. -/
theorem moving_small_fixed_commutator_card {c : Vertex Rg} (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg c)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    Nat.card (⁅U Rg c,A⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,hiC⟩ := graph_cover h e hz hk c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : (centralizer (A.comap i : Set M)).relIndex W ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := cover_small_fixed_commutator_card h e hz hk (A.comap i) hidx
  rw [←hiU,←hmA,←map_commutator,card_map_of_injective hi]
  exact hh

private theorem fixed_mod_central_normalizes_centralizer {G : Type*} [Group G]
    (A Q L : Subgroup G) (hLQ : L ≤ normalizer (Q : Set G))
    (hLA : ⁅L,A⁆ ≤ centralizer (Q : Set G)) :
    L ≤ normalizer ((Q ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro l hl q hq
  refine ⟨(mem_normalizer_iff.mp (hLQ hl) q).mp hq.1,?_⟩
  intro a ha
  have hh := hLA (commutator_mem_commutator (L.inv_mem hl) ha)
  have h1 : Commute ⁅l⁻¹,a⁆ q := (hh q hq.1).symm
  have h2 : Commute a q := hq.2 a ha
  have hc : Commute (l⁻¹*a*l) q := by
    have he : ⁅l⁻¹,a⁆*a=l⁻¹*a*l := by simp [commutatorElement_def,mul_assoc]
    exact he ▸ h1.mul_left h2
  have hm := hc.map (MulAut.conj l).toMonoidHom
  change Commute (l*(l⁻¹*a*l)*l⁻¹) (l*q*l⁻¹) at hm
  have he : l*(l⁻¹*a*l)*l⁻¹=a := by group
  rw [he] at hm
  exact hm.eq

include h in
/-- The forward slice kernel is normal relative to the starting stabilizer. -/
theorem selected_forward_kernel_normalized (hb : 2 < sourceDistance h) {a c t : Vertex Rg}
    (ha : color Rg a = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t) :
    stabilizer Rg a ≤ normalizer ((Q Rg a ⊓ centralizer
      (U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) :
        Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) := by
  let K := U Rg c ⊓ B Rg a ((sourceGeometry h).Z_normal _)
  have hb' : 2 < criticalDistance Rg a ((sourceGeometry h).exists_critical a ha) := by
    rw [(sourceGeometry h).distance_constant a ha]
    exact hb
  have hVL := (sourceGeometry h).V_local a ha hb'
  have hLK : ⁅Ltilde Rg a,K⁆ ≤ centralizer (Q Rg a : Set (FreeAmalgam Rg)) := by
    apply le_trans _ (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg a ha))
    apply commutator_le.mpr
    intro l hl k hk
    exact ((mem_B_iff Rg a _ hVL k).mp hk.2).2 l hl
  have hLN := fixed_mod_central_normalizes_centralizer K (Q Rg a) (Ltilde Rg a)
    ((Ltilde_le_stabilizer a).trans (Q_normalized Rg a)) hLK
  have htG : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have htC : Q Rg t ≤ stabilizer Rg c := fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have htK : Q Rg t ≤ normalizer (K : Set (FreeAmalgam Rg)) :=
    (le_inf (htC.trans (U_normalized c))
      (htG.trans (Escape.Propagation.Rigidity.B_normalized hb a ha))).trans
        inf_normalizer_le_normalizer_inf
  have htCK : Q Rg t ≤ normalizer (centralizer (K : Set (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
    htK.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
  have htN := (le_inf (htG.trans (Q_normalized Rg a)) htCK).trans
    inf_normalizer_le_normalizer_inf
  have hgen : pResidual 2 M ⊔ Rg = ⊤ := by
    rw [h.relative_residual]
    exact (codisjoint_subgroupOf_sup L R).eq_top
  rw [←CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation Rg hgen ha hat]
  exact sup_le hLN htN


include h in
/-- The actual selected orbit span is contained in the forward slice kernel. -/
theorem selected_span_le_forward_kernel
    (hb : 2 < sourceDistance h) {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a') :
    localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤
      Q Rg (alpha Rg) ⊓ centralizer
        (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
          ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have hZT : Z Rg c ≤ T := by
    apply le_inf
    · apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c hc)
      rw [(sourceGeometry h).distance_constant c hc,SimpleGraph.dist_comm,
        p.dist_start (by omega)]
      exact hb
    · let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hc
      exact (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans
        (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg c)))
  have hn := selected_forward_kernel_normalized (h := h) hb rfl hat hct
  rw [localZSpan_eq_conjugates]
  apply iSup_le
  intro g
  rintro _ ⟨z,hz,rfl⟩
  exact (mem_normalizer_iff.mp
    (hn ((stabilizer Rg (alpha Rg)).inv_mem g.property)) z).mp (hZT hz)

include h e hz hk in
/-- Small fixed index bounds the literal kernel index at every component
vertex for a two-subgroup. Its intersection with E lies in Q; no
point-core containment is required. -/
theorem moving_small_fixed_index_image {c : Vertex Rg} (hcol : color Rg c = false)
    (A : Subgroup (FreeAmalgam Rg)) (hA : A ≤ stabilizer Rg c) (hAtwo : IsPGroup 2 A)
    (hindex : (centralizer (A : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2) :
    (Q Rg c).relIndex A ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiE,hiU,hiC⟩ := graph_cover h e hz hk c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : (centralizer (A.comap i : Set M)).relIndex W ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := cover_small_fixed_index_image h e hz hk (A.comap i) hidx
  rw [CubicAction.permutation_image_card_of_two h e hz hk _
    (hAtwo.comap_of_injective i hi),←relIndex_map_map_of_injective _ _ hi,hiQ,hmA] at hh
  exact hh
include h e hz hk in
/-- Source (5.12)(3)'s small forward slice bounds both the whole slice
kernel and the selected span at the literal second vertex. -/
theorem selected_span_index_of_forward_slice
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    (Q Rg (p.walk.getVert 2)).relIndex T ≤ 2 ∧
      (Q Rg (p.walk.getVert 2)).relIndex
        (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≤ 2 := by
  let c := p.walk.getVert 2
  let K := U Rg c ⊓ B Rg (alpha Rg)
    ((sourceGeometry h).Z_normal _)
  let T := Q Rg (alpha Rg) ⊓ centralizer (K : Set (FreeAmalgam Rg))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg (p.walk.getVert 1) at hh
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hTG : T ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hfix : K ≤ centralizer (T : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp inf_le_right
  have hidx : (centralizer (T : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H := K.subgroupOf (U Rg c)))
    change (centralizer (T : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤
      K.relIndex (U Rg c) at hh
    exact hh.trans (by simpa only [K,inf_relIndex_left] using hslice)
  have hTidx := moving_small_fixed_index_image h e hz hk hcol T hTG
    ((Q_isPGroup (edge L R) h.relative_radical.isPGroup h.relative_radical.twoCore_le
      (alpha (edge L R)) rfl).to_le inf_le_left) hidx
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite T := Finite.of_injective
    (inclusion (inf_le_left.trans (show Q Rg (alpha Rg) ≤
      stabilizer Rg (alpha Rg) from fun _ hx => hx.1))) (inclusion_injective _)
  exact ⟨hTidx,(relIndex_le_of_le_right (selected_span_le_forward_kernel (h := h) hb p)
    index_ne_zero_of_finite).trans hTidx⟩

include h e hz hk in
/-- The forward slice kernel has a commutator of order at most two, in the
actual common edge seed, for either full central cover. -/
theorem selected_forward_kernel_line (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    Nat.card (⁅U Rg (p.walk.getVert 2),T⁆ : Subgroup (FreeAmalgam Rg)) ≤ 2 ∧
      ⁅U Rg (p.walk.getVert 2),T⁆ ≤ Z Rg (p.walk.getVert 1) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let K := U Rg c ⊓ B Rg (alpha Rg)
    ((sourceGeometry h).Z_normal _)
  let T := Q Rg (alpha Rg) ⊓ centralizer (K : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTG : T ≤ stabilizer Rg c :=
    (inf_le_left.trans (Q_le_adjacent_h Rg ht hat)).trans
      (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z Rg c)) (inclusion_injective _)
  have hfix : K ≤ centralizer (T : Set (FreeAmalgam Rg)) :=
    le_centralizer_iff.mp inf_le_right
  have hidx : (centralizer (T : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤ 2 := by
    have hh := relIndex_le_of_le_left hfix (index_ne_zero_of_finite (H := K.subgroupOf (U Rg c)))
    change (centralizer (T : Set (FreeAmalgam Rg))).relIndex (U Rg c) ≤
      K.relIndex (U Rg c) at hh
    exact hh.trans (by simpa only [K,inf_relIndex_left] using hslice)
  have hcard : Nat.card H ≤ 2 := moving_small_fixed_commutator_card h e hz hk hcol T hTG hidx
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  have htGa : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  have htGc : Q Rg t ≤ stabilizer Rg c :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hct)
  have hHN : Q Rg t ≤ normalizer (H : Set (FreeAmalgam Rg)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq]
    change H.map (MulAut.conj x).toMonoidHom = H
    dsimp only [H]
    have hUm : (U Rg c).map (MulAut.conj x).toMonoidHom = U Rg c :=
      mem_normalizer_iff_map_conj_eq.mp (U_normalized c (htGc hx))
    have hTm : T.map (MulAut.conj x).toMonoidHom = T :=
      mem_normalizer_iff_map_conj_eq.mp (hTN (htGa hx))
    rw [map_commutator,hUm,hTm]
  have hHU : H ≤ U Rg c :=
    le_normalizer_iff_commutator_le_left.mp (hTG.trans (U_normalized c))
  let : Finite H := Finite.of_injective (inclusion hHU) (inclusion_injective _)
  have hHC : H ≤ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    by_cases he : H = ⊥
    · rw [he]; exact bot_le
    · have hh := (one_lt_card_iff_ne_bot H).mpr he
      exact le_centralizer_iff.mp (hHN.trans
        (normalizer_le_centralizer_of_card_two H (by omega)))
  have hUQ : U Rg c ≤ Q Rg c :=
    (DistanceEight.U_le_Z Rg c).trans (by
      apply Z_le_Q_of_dist_lt Rg c ((sourceGeometry h).exists_critical c hcol)
      rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant c hcol]
      exact sourceDistance_pos h)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c hcol
  refine ⟨hcard,?_⟩
  intro x hx
  change x ∈ Z Rg t
  rw [Z,if_neg (by simp [ht])]
  exact mem_omegaCenter_iff.mpr
    ⟨(hHU.trans (hUQ.trans (Q_le_adjacent_h Rg ht hct))) hx,
      elemPow_eq_one_of_isElementaryAbelian x ((hHU.trans (DistanceEight.U_le_Z Rg c)) hx),
      hHC hx⟩

include h in
/-- The predecessor seed and full reverse critical kernel lie in the forward kernel. -/
theorem selected_forward_kernel_contains_inner_layers
    (hb : 2 < sourceDistance h) {e : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) e) :
    Z Rg (p.walk.getVert (p.walk.length-2)) ⊔ (Z Rg e ⊓ Q Rg (alpha Rg)) ≤
      Q Rg (alpha Rg) ⊓ centralizer
        (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :
          Set (FreeAmalgam Rg)) := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hb4 : 4 ≤ p.walk.length := by
    have he := (sourceGeometry h).even (alpha Rg) rfl
    change Even (sourceDistance h) at he
    rw [Nat.even_iff] at he
    omega
  have hc : color Rg (p.walk.getVert (p.walk.length-2)) = false := by
    apply (p.vertex_color (Nat.sub_le _ _)).mpr
    have he := (sourceGeometry h).even (alpha Rg) rfl
    change Even (sourceDistance h) at he
    rw [Nat.even_iff] at he ⊢
    omega
  have hd : color Rg (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega : 2 ≤ p.walk.length)).mpr (by decide)
  have hcd : (cosetGraph Rg).dist (p.walk.getVert 2)
      (p.walk.getVert (p.walk.length-2)) ≤ p.walk.length-4 := by
    have hh := SimpleGraph.dist_le ((p.walk.drop 2).take (p.walk.length-4))
    rw [SimpleGraph.Walk.take_length,SimpleGraph.Walk.drop_length,
      inf_eq_left.mpr (by omega : p.walk.length-4 ≤ p.walk.length-2),
      SimpleGraph.Walk.drop_getVert,show 2+(p.walk.length-4)=p.walk.length-2 by omega] at hh
    exact hh
  have hQc : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg (alpha Rg) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,SimpleGraph.dist_comm,
      p.dist_start (Nat.sub_le _ _)]
    change p.walk.length-2 < sourceDistance h
    omega
  have hdc : Z Rg (p.walk.getVert (p.walk.length-2)) ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ hc)
    rw [(sourceGeometry h).distance_constant _ hc,SimpleGraph.dist_comm]
    change (cosetGraph Rg).dist (p.walk.getVert 2) (p.walk.getVert (p.walk.length-2)) < sourceDistance h
    omega
  have hde : Z Rg e ≤ Q Rg (p.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt Rg e ((sourceGeometry h).exists_critical e p.end_color)
    rw [(sourceGeometry h).distance_constant e p.end_color,SimpleGraph.dist_comm,p.dist_end]
    change p.walk.length-2 < sourceDistance h
    omega
  have hcentral : Q Rg (p.walk.getVert 2) ≤ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :
        Set (FreeAmalgam Rg)) :=
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q Rg _ hd))).trans
      (centralizer_le (inf_le_left.trans (DistanceEight.U_le_Z Rg _)))
  exact le_inf (sup_le hQc inf_le_right)
    ((sup_le hdc (inf_le_left.trans hde)).trans hcentral)

omit hk in
include h e hz in
private theorem vertex_seed_eq_moving_sup_edge {c b : Vertex Rg}
    (hc : color Rg c = false) (hcb : Adjacent Rg c b) :
    Z Rg c = U Rg c ⊔ Z Rg b := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg c b).mp hcb
  · rcases hg with ⟨rfl,rfl⟩
    have hb := CubicAction.graph_Z_eq_moved_sup_edge h e hz (base_adjacent Rg)
    rw [graph_U_map h e hz] at hb
    have he := congrArg (fun A : Subgroup (FreeAmalgam Rg) =>
      A.map (MulAut.conj g⁻¹).toMonoidHom) hb
    rw [Subgroup.map_sup,←Z_act,←U_act,←Z_act] at he
    simpa [alpha,beta] using he
  · rw [hg.1] at hc
    cases hc

include h e hz hk in
/-- The small forward slice controls the commutator of the entire selected
span with its full kernel, and hence with the original reverse critical kernel. -/
theorem selected_span_kernel_commutator
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2) :
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),T⁆ ≤ Z Rg (alpha Rg) ∧
      ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
        Z Rg a' ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hseed : Z Rg t ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  have hZcG : Z Rg c ≤ stabilizer Rg (alpha Rg) :=
    ((Z_le_localZSpan Rg c (alpha Rg)).trans (localZSpan_le_V Rg (by
      rw [SimpleGraph.dist_comm,p.dist_start (by omega)]))).trans
      ((sourceGeometry h).V_local _ rfl hb)
  have hUc : ⁅U Rg c,T⁆ ≤ Z Rg (alpha Rg) :=
    (selected_forward_kernel_line h e hz hk hb p hslice).2.trans (adjacent_Z_le Rg rfl hat)
  have hZc : ⁅Z Rg c,T⁆ ≤ Z Rg (alpha Rg) := by
    rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
    apply commutator_sup_le_of_relative_normal (stabilizer Rg (alpha Rg))
      _ _ T _ (Z_normalized Rg _) ((DistanceEight.U_le_Z Rg c).trans hZcG)
      ((adjacent_Z_le Rg rfl hat).trans (Z_le_stabilizer Rg _)) hUc
    exact (commutator_eq_bot_iff_le_centralizer.mpr hseed).le.trans bot_le
  have hP : ⁅localZSpan Rg c (alpha Rg),T⁆ ≤ Z Rg (alpha Rg) := by
    rw [localZSpan_eq_conjugates]
    apply commutator_iSup_le_of_relative_normal (stabilizer Rg (alpha Rg)) T _ _
      (Z_normalized Rg _)
    · intro g
      have hgmap : (stabilizer Rg (alpha Rg)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = stabilizer Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp ((stabilizer Rg (alpha Rg)).le_normalizer
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      exact (map_mono hZcG).trans_eq hgmap
    · intro g
      have hm := map_mono (f := (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom) hZc
      have hTm : T.map (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = T :=
        mem_normalizer_iff_map_conj_eq.mp (hTN ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      have hZm : (Z Rg (alpha Rg)).map
          (MulAut.conj (g : FreeAmalgam Rg)⁻¹).toMonoidHom = Z Rg (alpha Rg) :=
        mem_normalizer_iff_map_conj_eq.mp (Z_normalized Rg _
          ((stabilizer Rg (alpha Rg)).inv_mem g.property))
      rwa [map_commutator,hTm,hZm] at hm
  exact ⟨hP,(commutator_mono le_rfl
    (le_sup_right.trans (selected_forward_kernel_contains_inner_layers (h := h) hb p))).trans hP⟩

include h e hz hk in
/-- If the selected span is nonabelian, its full forward kernel produces a
nonzero line in the common edge seed. The line is noncentral at the actual
second vertex, including for the cover of order thirty-two. -/
theorem selected_forward_kernel_noncentral_line
    (hb : 2 < sourceDistance h)
    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hslice : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
      (U Rg (p.walk.getVert 2)) ≤ 2)
    (hnonabelian : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
      localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ ≠ ⊥) :
    let T := Q Rg (alpha Rg) ⊓ centralizer
      (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg)
        ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
    let H := ⁅U Rg (p.walk.getVert 2),T⁆
    Nat.card H = 2 ∧ H ≤ Z Rg (p.walk.getVert 1) ∧
      ¬ H ≤ centralizer (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg)) := by
  let c := p.walk.getVert 2
  let t := p.walk.getVert 1
  let T := Q Rg (alpha Rg) ⊓ centralizer
    (U Rg c ⊓ B Rg (alpha Rg)
      ((sourceGeometry h).Z_normal _) : Set (FreeAmalgam Rg))
  let H := ⁅U Rg c,T⁆
  let P := localZSpan Rg c (alpha Rg)
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  have hcol : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have hct : Adjacent Rg c t :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hTQt : T ≤ Q Rg t := inf_le_left.trans (Q_le_adjacent_h Rg ht hat)
  have hTG : T ≤ stabilizer Rg c :=
    hTQt.trans (fun _ hx => hx.2 _ (adjacent_symm Rg hct))
  have hseed : Z Rg t ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
    intro z hz x hx
    rw [Z,if_neg (by simp [ht])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2 x (hTQt hx)
  have hTN : stabilizer Rg (alpha Rg) ≤ normalizer (T : Set (FreeAmalgam Rg)) :=
    selected_forward_kernel_normalized (h := h) hb rfl hat hct
  have hHne : H ≠ ⊥ := by
    intro he
    have hZc : Z Rg c ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
      rw [vertex_seed_eq_moving_sup_edge h e hz hcol hct]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp he) hseed
    have hNC : stabilizer Rg (alpha Rg) ≤ normalizer
        (centralizer (T : Set (FreeAmalgam Rg)) : Set (FreeAmalgam Rg)) :=
      hTN.trans (le_normalizer_of_normal_subgroupOf (Subgroup.centralizer_le_normalizer _))
    have hPC : P ≤ centralizer (T : Set (FreeAmalgam Rg)) := by
      dsimp only [P]
      rw [localZSpan_eq_conjugates]
      apply iSup_le
      intro g
      rintro _ ⟨z,hz,rfl⟩
      exact (mem_normalizer_iff.mp
        (hNC ((stabilizer Rg (alpha Rg)).inv_mem g.property)) z).mp (hZc hz)
    exact hnonabelian (commutator_eq_bot_iff_le_centralizer.mpr
      (hPC.trans (centralizer_le (selected_span_le_forward_kernel (h := h) hb p))))
  have hline := selected_forward_kernel_line h e hz hk hb p hslice
  let := finite_Z Rg t
  let : Finite H := Finite.of_injective (inclusion hline.2) (inclusion_injective _)
  have hpos : 1 < Nat.card H := (one_lt_card_iff_ne_bot H).mpr hHne
  refine ⟨?_,hline.2,?_⟩
  · change Nat.card H = 2
    have hh := hline.1
    change Nat.card H ≤ 2 at hh
    omega
  · intro hcentral
    obtain ⟨i,hi,hir,hiQ,hiE,hiU,hiC⟩ := graph_cover h e hz hk c hcol
    let A := T.comap i
    have hmA : A.map i = T := map_comap_eq_self (hTG.trans_eq hir.symm)
    have hcA : ⁅W,A⁆ ≤ center M := by
      intro x hx
      apply mem_center_iff.mpr
      intro m
      apply hi
      simp only [map_mul]
      apply hcentral
      · have hh := mem_map_of_mem i hx
        rw [map_commutator,hmA,hiU] at hh
        exact hh
      · rw [←hir]
        exact ⟨m,rfl⟩
    have hle := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk A
      (((Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le
        (alpha Rg) rfl).to_le (show T ≤ Q Rg (alpha Rg) from inf_le_left)).comap_of_injective i hi) hcA)
    rw [hmA,hiQ] at hle
    exact hHne (le_bot_iff.mp ((commutator_mono
      (DistanceEight.U_le_Z Rg c) hle).trans_eq (Z_centralizes_Q Rg c hcol)))
omit hk in
include h e hz in
/-- The actual whole-core alternative now supplies the full forward kernel
and its noncentral line in the small-slice, nonabelian-span branch. The other
slice and span cases are retained as explicit alternatives. The source
choices and terminal exclusions remain with this reconstruction owner. -/
theorem coreExhaustion_or_cubic_forward_kernel :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ c : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) c,
        let F := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :
            Set (FreeAmalgam Rg))
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ∨
        (Q Rg (p.walk.getVert 2)).relIndex F ≤ 2 ∧
        P ≤ F ∧ ⁅P,F⁆ ≤ Z Rg (alpha Rg) ∧
        ⁅P,Z Rg c ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) ∧
        (⁅P,P⁆ = ⊥ ∨
          Nat.card (⁅U Rg (p.walk.getVert 2),F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅U Rg (p.walk.getVert 2),F⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          ¬ ⁅U Rg (p.walk.getVert 2),F⁆ ≤ centralizer
            (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · refine Or.inr ⟨hk,hs,hb,?_⟩
    intro c p
    dsimp only
    by_cases hslice : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert 2))
    · exact Or.inl hslice
    · right
      have hslice' : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ≤ 2 := by omega
      have hc := selected_span_kernel_commutator h e hz hk hb p hslice'
      refine ⟨(selected_span_index_of_forward_slice h e hz hk hb p hslice').1,
        selected_span_le_forward_kernel (h := h) hb p,hc.1,hc.2,?_⟩
      by_cases hn : ⁅localZSpan Rg (p.walk.getVert 2) (alpha Rg),
          localZSpan Rg (p.walk.getVert 2) (alpha Rg)⁆ = ⊥
      · exact Or.inl hn
      · exact Or.inr (selected_forward_kernel_noncentral_line h e hz hk hb p hslice' hn)

omit hk in
include h e hz in
/-- Literal C.1.32 consumer of the forward-kernel and selected-span bounds.
All kernel normalization, cover and odd-kernel index premises are discharged. -/
theorem rankTwo_or_cubic_forward_kernel :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ c : Vertex Rg, ∀ p : CriticalPath Rg (sourceGeometry h) (alpha Rg) c,
        let F := Q Rg (alpha Rg) ⊓ centralizer
          (U Rg (p.walk.getVert 2) ⊓ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :
            Set (FreeAmalgam Rg))
        let P := localZSpan Rg (p.walk.getVert 2) (alpha Rg)
        2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex
          (U Rg (p.walk.getVert 2)) ∨
        (Q Rg (p.walk.getVert 2)).relIndex F ≤ 2 ∧
        P ≤ F ∧ ⁅P,F⁆ ≤ Z Rg (alpha Rg) ∧
        ⁅P,Z Rg c ⊓ Q Rg (alpha Rg)⁆ ≤ Z Rg (alpha Rg) ∧
        (⁅P,P⁆ = ⊥ ∨
          Nat.card (⁅U Rg (p.walk.getVert 2),F⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
          ⁅U Rg (p.walk.getVert 2),F⁆ ≤ Z Rg (p.walk.getVert 1) ∧
          ¬ ⁅U Rg (p.walk.getVert 2),F⁆ ≤ centralizer
            (stabilizer Rg (p.walk.getVert 2) : Set (FreeAmalgam Rg))) :=
  (coreExhaustion_or_cubic_forward_kernel h e hz).imp (rankTwo_of_exhaustion h e hz) id


end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
