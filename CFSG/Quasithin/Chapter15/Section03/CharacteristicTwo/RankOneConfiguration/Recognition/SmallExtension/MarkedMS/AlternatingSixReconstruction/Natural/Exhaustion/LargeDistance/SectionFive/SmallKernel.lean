module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SmallCriticalLine
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.SmallImage
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Pointwise fixers of full small critical kernels

An actor with fixed index at most two on the original moved cover has
cyclic transposition image on its natural quotient. Its entire pointwise
fixed-subgroup centralizer has the same image: enlarging the actor to that
centralizer does not decrease its fixed space. This argument retains the
possible central line in the order-thirty-two cover.

At each actual critical endpoint this identifies the relative centralizer
of the full critical kernel with the two-core joined to the opposite seed.
Equal kernels therefore give equal seed images and commutator lines; the
kernel cannot be invariant under the whole vertex stabilizer. The same
calculation bounds predecessor commutators and supplies the small fixed-index
estimate for the selected forward kernel in `SelectedKernel`.

Source: MS93 (3.3)(ii), (5.7), and the small-image calculations in
(5.11)--(5.12), printed pp.866--867, 919, 923--927. This extends the
project's SymplecticSetup.SmallEdgeFixed argument to both central covers
and every radical image. The coordinated path selection and remaining
terminal premises stay with qt-e-ms-small-a6-exhaustion-large-distance;
qt-e-ms-small-a6-reconstruction retains unconditional reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

include s in
/-- The pointwise fixer of the actual cover's fixed hyperplane has no larger
image than the original nontrivial actor. Both central-cover orders remain. -/
theorem cover_small_fixed_centralizer (A : Subgroup d.overgroup)
    (hne : ¬ A ≤ pCore 2 d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    centralizer (replacementMoved d ⊓ centralizer (A : Set d.overgroup) : Set d.overgroup) ≤
      pCore 2 d.overgroup ⊔ A := by
  let := replacementMoved_normal h d
  let F := replacementMoved d ⊓ centralizer (A : Set d.overgroup)
  let B := centralizer (F : Set d.overgroup)
  have hAB : A ≤ B := le_centralizer_iff.mpr inf_le_right
  have hFB : F ≤ centralizer (B : Set d.overgroup) := le_centralizer_iff.mpr le_rfl
  have hfix : fixedSpace (coverAction s) (A.map s.projection) ≤
      fixedSpace (coverAction s) (B.map s.projection) := by
    intro v hv
    apply (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
      s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) B v).mpr
    exact hFB ⟨v.toMul.property,
      (NormalElementaryQuotient.mem_fixedSpace_image (replacementMoved d)
        s.projection s.surjective (s.projection_kernel.trans (moved_centralizer s).symm) A v).mp hv⟩
  have hsmallA : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hsmallB : fixedCodim (coverAction s) (B.map s.projection) ≤ 1 := by
    have ha := fixedCodim_add_finrank (coverAction s) (A.map s.projection)
    have hb := fixedCodim_add_finrank (coverAction s) (B.map s.projection)
    have hh := Submodule.finrank_mono hfix
    omega
  have hnB : B.map s.projection ≠ ⊥ := by
    intro he
    apply hne
    have hk := (map_eq_bot_iff B).mp he
    rw [s.projection_kernel] at hk
    exact hAB.trans hk
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (B.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (B.map s.projection)).trans hsmallB
  obtain ⟨t,ht,hswap,hB⟩ :=
    Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
      (B.map s.projection) hnB hnat
  have hnA : A.map s.projection ≠ ⊥ := by
    intro he
    exact hne (s.projection_kernel ▸ (map_eq_bot_iff A).mp he)
  have hcardA := (one_lt_card_iff_ne_bot (A.map s.projection)).mpr hnA
  have hcardB : Nat.card (B.map s.projection) = 2 := by
    rw [hB,Nat.card_zpowers,hswap.orderOf]
  have hBA : B.map s.projection = A.map s.projection :=
    (eq_of_le_of_card_ge (map_mono hAB) (by omega)).symm
  have hle : B ≤ (A.map s.projection).comap s.projection := by
    rw [←hBA]
    exact le_comap_map s.projection B
  rw [Subgroup.comap_map_eq,s.projection_kernel] at hle
  exact hle.trans_eq (sup_comm _ _)

include s in
/-- The fixed-hyperplane bound transported through the actual local embedding. -/
theorem embedded_cover_small_fixed_centralizer {H : Type*} [Group H]
    (i : d.overgroup →* H) (hi : Function.Injective i)
    (A : Subgroup H) (hA : A ≤ i.range)
    (hne : ¬ A ≤ (pCore 2 d.overgroup).map i)
    (hindex : (centralizer (A : Set H)).relIndex ((replacementMoved d).map i) ≤ 2) :
    i.range ⊓ centralizer ((replacementMoved d).map i ⊓ centralizer (A : Set H) : Set H) ≤
      (pCore 2 d.overgroup).map i ⊔ A := by
  let A₀ := A.comap i
  have hmA : A₀.map i = A := map_comap_eq_self hA
  have hnA : ¬ A₀ ≤ pCore 2 d.overgroup := by
    intro hh
    exact hne (hmA ▸ map_mono hh)
  have hidx : (centralizer (A₀ : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hf := cover_small_fixed_centralizer s A₀ hnA hidx
  rintro _ ⟨⟨m,rfl⟩,hm⟩
  have hmfix : m ∈ centralizer
      (replacementMoved d ⊓ centralizer (A₀ : Set d.overgroup) : Set d.overgroup) := by
    intro w hw
    apply hi
    simp only [map_mul]
    apply hm
    change i w ∈ ((replacementMoved d).map i ⊓ centralizer (A : Set H) : Subgroup H)
    rw [←hmA,map_inf_centralizer_of_injective i hi]
    exact mem_map_of_mem i hw
  have hh := mem_map_of_mem i (hf hmfix)
  rwa [Subgroup.map_sup,hmA] at hh

include s in
/-- In the small critical branch, the full critical kernel has no extra
pointwise fixers in its vertex stabilizer. This uses the whole cover. -/
theorem small_critical_kernel_centralizer (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    stabilizer d.radical a ⊓ centralizer
      (Z d.radical a ⊓ Q d.radical a' : Set (FreeAmalgam d.radical)) ≤
      Q d.radical a ⊔ Z d.radical a' := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hA : Z d.radical a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hZa : Z d.radical a ≤ stabilizer d.radical a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hfixed : U d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) ≤
      Z d.radical a ⊓ Q d.radical a' := by
    apply le_inf (inf_le_left.trans (DistanceEight.U_le_Z d.radical a))
    rw [←C_eq_Q s hc a' p.end_color]
    exact le_inf (inf_le_left.trans ((DistanceEight.U_le_Z d.radical a).trans hZa)) inf_le_right
  have hnA : ¬ Z d.radical a' ≤ (pCore 2 d.overgroup).map i := by
    rw [hiQ]
    exact (critical_reverse_pair s hc p).2
  have hC : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (DistanceEight.U_le_Z d.radical a)) (inclusion_injective _)
  have hidx : (centralizer (Z d.radical a' : Set (FreeAmalgam d.radical))).relIndex
      ((replacementMoved d).map i) ≤ 2 := by
    rw [hiU]
    exact ((relIndex_le_of_le_left hC index_ne_zero_of_finite).trans
      (relIndex_le_of_le_right (DistanceEight.U_le_Z d.radical a) index_ne_zero_of_finite)).trans_eq
      (small_critical_indices s hc p hsmall).1
  have hh := embedded_cover_small_fixed_centralizer s i hi (Z d.radical a') hA hnA hidx
  rw [hir,hiQ,hiU] at hh
  exact (inf_le_inf_left _ (centralizer_le hfixed)).trans hh

include s in
/-- Every subgroup of the opposite stabilizer fixing the literal critical
kernel has its entire endpoint commutator in the same critical line. -/
theorem small_critical_kernel_commutator (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hY : Y ≤ stabilizer d.radical a')
    (hfix : Y ≤ centralizer (Z d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅Y,Z d.radical a'⁆ ≤ ⁅Z d.radical a,Z d.radical a'⁆ := by
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    CriticalPath.ofPair p.end_color (critical_reverse_pair s hc p)
  have hs : (Q d.radical a).relIndex (Z d.radical a') < 4 := by
    rw [(small_critical_indices s hc p hsmall).2]
    decide
  have hjoin := (le_inf hY hfix).trans (small_critical_kernel_centralizer s hc q hs)
  have hZa : Z d.radical a ≤ stabilizer d.radical a' :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hQ : Q d.radical a' ≤ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))
  have he := commutator_eq_of_centralizing_sup
    (show Q d.radical a' ⊔ Z d.radical a = Q d.radical a' ⊔ Z d.radical a from rfl)
    hQ (hZa.trans (Z_normalized d.radical a'))
  rw [commutator_comm Y,commutator_comm (Z d.radical a)]
  exact (commutator_mono le_rfl hjoin).trans_eq he.symm

include s in
/-- Exact relative centralizer of the full critical kernel. The common
ambient stabilizer is retained, rather than replaced by an abstract image. -/
theorem small_critical_kernel_centralizer_eq (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    stabilizer d.radical a ⊓ centralizer
      (Z d.radical a ⊓ Q d.radical a' : Set (FreeAmalgam d.radical)) =
      Q d.radical a ⊔ Z d.radical a' := by
  apply le_antisymm (small_critical_kernel_centralizer s hc p hsmall)
  apply sup_le
  · apply le_inf (fun _ hx => hx.1)
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))).trans (centralizer_le inf_le_left)
  · apply le_inf
    · exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
        (by rw [(replacementGeometry h d).distance_constant a p.start_color]
            exact replacementDistance_pos h d) p.critical
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a' p.end_color)).trans (centralizer_le inf_le_right)

include s in
/-- Equal critical kernels through the same starting vertex determine the
same full seed image and the same actual commutator line. -/
theorem small_critical_equal_kernels (hc : DistanceTwo.CentralLayer d)
    {a a' b' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : CriticalPath d.radical (replacementGeometry h d) a b')
    (hp : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (hq : (Q d.radical b').relIndex (Z d.radical a) < 4)
    (hkernel : Z d.radical a ⊓ Q d.radical a' = Z d.radical a ⊓ Q d.radical b') :
    Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b' ∧
      ⁅Z d.radical a,Z d.radical a'⁆ = ⁅Z d.radical a,Z d.radical b'⁆ := by
  have hj : Q d.radical a ⊔ Z d.radical a' = Q d.radical a ⊔ Z d.radical b' := by
    rw [←small_critical_kernel_centralizer_eq s hc p hp,
      ←small_critical_kernel_centralizer_eq s hc q hq]
    exact congrArg (fun D : Subgroup (FreeAmalgam d.radical) =>
      stabilizer d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical))) hkernel
  refine ⟨hj,?_⟩
  have hQ : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a p.start_color))
  have hA := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
    (by rw [(replacementGeometry h d).distance_constant a p.start_color]
        exact replacementDistance_pos h d) p.critical
  have hB := critical_Z_le_stabilizer d.radical (replacementGeometry h d) a q.start_color
    (by rw [(replacementGeometry h d).distance_constant a q.start_color]
        exact replacementDistance_pos h d) q.critical
  exact (commutator_eq_of_centralizing_sup rfl hQ (hA.trans (Z_normalized d.radical a))).trans
    ((congrArg (fun E => ⁅Z d.radical a,E⁆) hj).trans
      (commutator_eq_of_centralizing_sup rfl hQ (hB.trans (Z_normalized d.radical a))).symm)

include s in
/-- Fixing the opposite critical kernel is enough for the source predecessor
commutator bound, independently of the radical image and cover order. -/
theorem small_critical_predecessor_commutator (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hY : Y ≤ Q d.radical (p.walk.getVert (p.walk.length-2)))
    (hfix : Y ≤ centralizer (Z d.radical a' ⊓ Q d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅Y,Z d.radical a'⁆ ≤ Z d.radical a := by
  have hl : 2 < p.walk.length := p.length_eq_b ▸ hb
  let t := p.walk.getVert (p.walk.length-1)
  have hat : Adjacent d.radical a' t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-1) (by omega)
    rw [show p.walk.length-1+1 = p.walk.length by omega,p.walk.getVert_length] at hh
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp hh)
  have hct : Adjacent d.radical (p.walk.getVert (p.walk.length-2)) t := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length-2) (by omega)
    rw [show p.walk.length-2+1 = p.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have ht : color d.radical t = true := by
    have hh := adjacent_color_ne d.radical hat
    rw [p.end_color] at hh
    cases he : color d.radical t <;> simp_all
  have hYt := hY.trans (Q_le_adjacent_h d.radical ht hct)
  have hYe : Y ≤ stabilizer d.radical a' := fun y hy =>
    (hYt hy).2 _ (adjacent_symm d.radical hat)
  exact (small_critical_kernel_commutator s hc p hsmall Y hYe hfix).trans
    (((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left).trans
      (DistanceEight.U_le_Z d.radical a))

include s in
/-- The exact critical kernel cannot be invariant under the whole starting
stabilizer: its small pointwise fixer would then give a normal transposition
image in S6. -/
theorem small_critical_kernel_not_normalized (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ¬ stabilizer d.radical a ≤ normalizer
      (Z d.radical a ⊓ Q d.radical a' : Set (FreeAmalgam d.radical)) := by
  intro hnorm
  let J := stabilizer d.radical a
  let K := Z d.radical a ⊓ Q d.radical a'
  let B := Q d.radical a ⊔ Z d.radical a'
  have hJB : J ≤ normalizer (B : Set (FreeAmalgam d.radical)) := by
    dsimp only [B]
    rw [←small_critical_kernel_centralizer_eq s hc p hsmall]
    exact (le_inf J.le_normalizer
      (hnorm.trans (le_normalizer_of_normal_subgroupOf
        (Subgroup.centralizer_le_normalizer _)))).trans inf_normalizer_le_normalizer_inf
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hA : Z d.radical a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color
      (by rw [(replacementGeometry h d).distance_constant a p.start_color]
          exact replacementDistance_pos h d) p.critical
  have hB : B ≤ i.range := sup_le (hiQ ▸ map_le_range i _) hA
  let B₀ := B.comap i
  let : B₀.Normal := by
    constructor
    intro x hx g
    change i (g*x*g⁻¹) ∈ B
    simpa only [map_mul,map_inv] using le_normalizer_iff.mp hJB (i g)
      (show i g ∈ stabilizer d.radical a from hir ▸ (show i g ∈ i.range from ⟨g,rfl⟩)) (i x) hx
  let : (B₀.map s.projection).Normal := Normal.map inferInstance _ s.surjective
  have hmA : ((Z d.radical a').comap i).map i = Z d.radical a' := map_comap_eq_self hA
  have hB₀ : B₀ = pCore 2 d.overgroup ⊔ (Z d.radical a').comap i := by
    apply map_injective hi
    rw [Subgroup.map_sup,hiQ,hmA,map_comap_eq_self hB]
  have hcB : Nat.card (B₀.map s.projection) = 2 := by
    have hk : (pCore 2 d.overgroup).map s.projection = ⊥ :=
      (Subgroup.map_eq_bot_iff _).mpr s.projection_kernel.symm.le
    rw [hB₀,Subgroup.map_sup,hk,bot_sup_eq,
      ←relIndex_ker,s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hmA,hiQ]
    exact (small_critical_indices s hc p hsmall).2
  have hne : B₀.map s.projection ≠ ⊥ := by
    intro he
    rw [he,card_bot] at hcB
    omega
  have hAlt : alternatingGroup (Fin 6) ≤ B₀.map s.projection :=
    Equiv.Perm.alternatingGroup_le_of_normal (by simp)
      ((nontrivial_iff_ne_bot _).mpr hne)
  have hcard := card_le_of_le hAlt
  rw [hcB] at hcard
  have h360 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup,Nat.card_fin]
    norm_num
  omega

include s in
/-- A fixed hyperplane of the full cover forces image order at most two. -/
theorem cover_small_fixed_index_image (A : Subgroup d.overgroup)
    (hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2) :
    Nat.card (A.map s.projection) ≤ 2 := by
  let := replacementMoved_normal h d
  have hsmall : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hnat : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hsmall
  by_cases he : A.map s.projection = ⊥
  · rw [he,card_bot]
    decide
  · obtain ⟨t,_,ht,he⟩ :=
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.PointCoreTranspositionFixed.small_image_eq_zpowers
        (A.map s.projection) he hnat
    rw [he,Nat.card_zpowers,ht.orderOf]

include s in
/-- Small fixed index bounds the literal kernel index at every component
vertex; no point-core containment is required. -/
theorem moving_small_fixed_index_image (hc : DistanceTwo.CentralLayer d)
    {c : Vertex d.radical} (hcol : color d.radical c = false)
    (A : Subgroup (FreeAmalgam d.radical)) (hA : A ≤ stabilizer d.radical c)
    (hindex : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical c) ≤ 2) :
    (Q d.radical c).relIndex A ≤ 2 := by
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc c hcol
  have hmA : (A.comap i).map i = A := map_comap_eq_self (hA.trans_eq hir.symm)
  have hidx : (centralizer (A.comap i : Set d.overgroup)).relIndex (replacementMoved d) ≤ 2 := by
    rw [←hiU,←hmA,←inf_relIndex_right,inf_comm,
      map_inf_centralizer_of_injective i hi,relIndex_map_map_of_injective _ _ hi,
      inf_relIndex_left] at hindex
    exact hindex
  have hh := cover_small_fixed_index_image s (A.comap i) hidx
  rwa [←relIndex_ker,s.projection_kernel,←relIndex_map_map_of_injective _ _ hi,hiQ,hmA] at hh

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
