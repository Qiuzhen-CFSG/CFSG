module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.ForwardStrict
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowFixedLine
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicCoordinatedPaths
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicSmallBackward

/-!
# Small critical images reached by original Borel shifts

A large two-subgroup of the six-letter quotient has a noncentral displacement
fixed by a containing Sylow two-subgroup on either full moving cover. Transport
through the original cubic projection puts this displacement in the intersection
of the critical commutator and its first edge seed. Two successive generating
edges would make that intersection central at its own critical start, a
contradiction. Thus the second of two generating backward shifts has both
critical images of order two; its commutator is an order-two line moved by the
whole first edge kernel.

The strict forward bound constructs generating shifts whenever the current
critical image is large. Starting from any critical path, a small critical
image is therefore reached within two such shifts. Conjugation gives a small
critical pair at every component vertex, with the full central attachments and
strict bounds on both ends retained. OriginalSylowExceptional applies this
conclusion to the literal original c.L,d.S pair.

Only the six-cover model calculation is imported from SylowFixedLine. All
amalgam embeddings, kernels and paths below belong to the original exceptional
graph. In particular, the projection kernel is still E, with odd quotient E/Q;
its image-cardinality formula is used only for genuine two-subgroups. No
identification with the natural replacement graph occurs.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (3.3) and the initial R4 reduction in (5.10), printed pp.866--867,922.
The full mover comparison, terminal exclusions (5.11)--(5.12), CoreExhaustion
and all five intrinsic block clauses remain necessary for reconstruction.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open scoped commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le (commutator_le_left _ _)
open scoped IsMulCommutative in
/-- A large image inside any two-subgroup gives a noncentral full-cover
commutator fixed by that two-subgroup, in the literal marking. -/
theorem large_two_image_fixed_commutator
    (A T : Subgroup M) (hAT : A ≤ T)
    (hT : IsPGroup 2 (T.map π))
    (hcard : 4 ≤ Nat.card (A.map π)) :
    ¬ ⁅W,A⁆ ⊓ centralizer (T : Set M) ≤ center M := by
  obtain ⟨a,ha,v,hfix,hnon⟩ := Natural.Exhaustion.LargeDistance.SectionFive.SylowFixedLine.cover_model_two_group_fixed_displacement
    (coverAction h e hz hk) (moved_subgroup_cover_model h e hz hk) (A.map π) (T.map π)
    (map_mono hAT) hT hcard
  obtain ⟨a,ha,rfl⟩ := ha
  let r := coverAction h e hz hk (π a) v-v
  have hr : (r.toMul : M) = a*v.toMul*a⁻¹*(v.toMul : M)⁻¹ := by
    dsimp only [r]
    rw [toMul_sub,Subgroup.coe_div,div_eq_mul_inv,coverAction_conjugate h e hz hk]
  have hrA : (r.toMul : M) ∈ ⁅W,A⁆ := by
    rw [hr,commutator_comm]
    exact commutator_mem_commutator ha v.toMul.property
  have hrT : (r.toMul : M) ∈ centralizer (T : Set M) := by
    intro t ht
    have hh := congrArg (fun z : Additive (W) => (z.toMul : M))
      (hfix (π t) (mem_map_of_mem _ ht))
    rw [coverAction_conjugate h e hz hk] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  intro hcentral
  have hc := hcentral ⟨hrA,hrT⟩
  apply hnon
  intro g
  obtain ⟨t,rfl⟩ := CubicEven.projection_surjective h e hz hk g
  change (coverAction h e hz hk (π t) r).toMul = r.toMul
  apply Subtype.ext
  rw [coverAction_conjugate h e hz hk]
  rw [(mem_center_iff.mp hc t),mul_inv_cancel_right]

include h e hz hk in
private theorem large_critical_first_seed_noncentral_base

    {a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg (alpha Rg))) :
    ¬ ⁅Z Rg (alpha Rg),Z Rg a'⁆ ⊓ Z Rg (p.walk.getVert 1) ≤
      centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) := by
  have hp := sourceDistance_pos h
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  let t := p.walk.getVert 1
  have hat : Adjacent Rg (alpha Rg) t := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (by omega)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hAt : Z Rg a' ≤ Q Rg t := by
    apply Z_le_Q_of_dist_lt Rg a' ((sourceGeometry h).exists_critical a' p.end_color)
    rw [SimpleGraph.dist_comm,p.dist_end,(sourceGeometry h).distance_constant _ p.end_color]
    change p.walk.length-1 < sourceDistance h
    omega
  have htG : Q Rg t ≤ stabilizer Rg (alpha Rg) :=
    fun _ hx => hx.2 _ (adjacent_symm Rg hat)
  let A := (Z Rg a').comap (embedM Rg)
  let T := (Q Rg t).comap (embedM Rg)
  have hmA : A.map (embedM Rg) = Z Rg a' :=
    map_comap_eq_self ((hAt.trans htG).trans_eq (stabilizer_m_base Rg))
  have hmT : T.map (embedM Rg) = Q Rg t :=
    map_comap_eq_self (htG.trans_eq (stabilizer_m_base Rg))
  have hcard : 4 ≤ Nat.card (A.map π) := by
    rw [CubicAction.permutation_image_card_of_two h e hz hk A
      (((sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color).isPGroup.comap_of_injective
        (embedM Rg) (embedM_injective Rg)),
      ←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hmA,
      ←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact reverse_critical_image_four_le h e hz hk hp p hlarge
  have hQt : IsPGroup 2 (Q Rg t) := by
    obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common Rg _ _).mp hat
    · rw [hg.2]
      have hh := Q_act Rg g (beta Rg)
      simp only [beta,act_hVertex,one_mul] at hh
      rw [hh]
      change IsPGroup 2 ((Q Rg (beta Rg)).map _)
      rw [Q_beta]
      exact (h.relative_radical.isPGroup.map _).map _
    · have hh : color Rg (alpha Rg) = true := by rw [hg.1]; rfl
      cases hh
  have hT : IsPGroup 2 (T.map π) :=
    (hQt.comap_of_injective (embedM Rg) (embedM_injective Rg)).map π
  have hn := large_two_image_fixed_commutator h e hz hk A T (comap_mono hAt) hT hcard
  intro hcentral
  apply hn
  rintro x ⟨hx,hxT⟩
  have hxD : embedM Rg x ∈ ⁅Z Rg (alpha Rg),Z Rg a'⁆ := by
    have hh := mem_map_of_mem (embedM Rg) hx
    rw [map_commutator,hmA,graph_U_map h e hz] at hh
    exact commutator_mono (DistanceEight.U_le_Z Rg _) le_rfl hh
  have hxZ : embedM Rg x ∈ Z Rg (alpha Rg) :=
    (critical_seed_commutator_le h p) hxD
  have hxQ : embedM Rg x ∈ Q Rg t := by
    apply Q_le_adjacent_h Rg ht hat
    apply Z_le_Q_of_dist_lt Rg _ ((sourceGeometry h).exists_critical _ rfl) _ hxZ
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant _ rfl]
    exact hp
  have hxC : embedM Rg x ∈ centralizer (Q Rg t : Set (FreeAmalgam Rg)) := by
    rw [←hmT]
    exact map_centralizer_le_centralizer_image (T : Set M) (embedM Rg)
      (mem_map_of_mem _ hxT)
  have hxseed : embedM Rg x ∈ Z Rg t := by
    rw [Z,if_neg (by simp [ht])]
    let := (sourceGeometry h).Z_elementary hp (alpha Rg) rfl
    exact mem_omegaCenter_iff.mpr ⟨hxQ,elemPow_eq_one_of_isElementaryAbelian _ hxZ,hxC⟩
  apply mem_center_iff.mpr
  intro m
  apply embedM_injective Rg
  simp only [map_mul]
  apply hcentral ⟨hxD,hxseed⟩
  change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
  rw [stabilizer_m_base]
  exact ⟨m,rfl⟩


include h e hz hk in
/-- A large critical image meets its first edge seed noncentrally, for either
cover and every radical image. -/
theorem large_critical_first_seed_noncentral

    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    ¬ ⁅Z Rg a,Z Rg a'⁆ ⊓ Z Rg (p.walk.getVert 1) ≤
      centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_critical_first_seed_noncentral_base h e hz hk
    (a' := act Rg g⁻¹ a')
  rw [←hbase] at base
  intro hcentral
  have hlarge₀ : 4 ≤ (Q Rg (act Rg g⁻¹ a')).relIndex
      (Z Rg (act Rg g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  apply base (p.act g⁻¹) hlarge₀
  have hh := (map_mono (f := (MulAut.conj g).toMonoidHom) hcentral).trans
    (map_centralizer_le_centralizer_image _ _)
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_commutator] at hh
  simpa only [CriticalPath.act,actWalk_getVert,Z_act,stabilizer_act,inv_inv,Subgroup.coe_map] using hh

private theorem terminal_central_fixed_map {F : Type*} [Group F] (H K : Subgroup F)
    (hHK : H ≤ centralizer (K : Set F)) {x : F} (hx : x ∈ K) :
    H.map (MulAut.conj x).toMonoidHom = H :=
  mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.centralizer_le_normalizer _ (le_centralizer_iff.mp hHK hx))

include h e hz hk in
/-- The same two generating edges and component transporter exclude the
critical configuration for both cover orders. -/
theorem large_critical_two_generating_edges_false
    {a endpoint : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a endpoint)
    (hlarge : 4 ≤ (Q Rg endpoint).relIndex (Z Rg a))
    (c v z f g : Vertex Rg)
    (hct : Adjacent Rg c (p.walk.getVert 1)) (hcv : Adjacent Rg c v)
    (hgenC : Q Rg (p.walk.getVert 1)⊔Z Rg f=stabilizer Rg c)
    (hgenD : Q Rg v⊔Z Rg g=stabilizer Rg z)
    (hRf : ⁅Z Rg a,Z Rg endpoint⁆≤centralizer (Z Rg f:Set (FreeAmalgam Rg)))
    (hRg : ⁅Z Rg a,Z Rg endpoint⁆≤centralizer (Z Rg g:Set (FreeAmalgam Rg)))
    (x : FreeAmalgam Rg) (hx : x∈stabilizer Rg c) (hxa : act Rg x z=a) : False := by
  let H := ⁅Z Rg a,Z Rg endpoint⁆⊓Z Rg (p.walk.getVert 1)
  have hnon := large_critical_first_seed_noncentral h e hz hk p hlarge
  have ht : color Rg (p.walk.getVert 1)=true := by
    have hcol := p.vertex_color (show 1≤p.walk.length by
      have hh : 0<p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
      omega)
    have hf : ¬color Rg (p.walk.getVert 1)=false := by
      intro hh
      have he := hcol.mp hh
      norm_num at he
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hseed (w : Vertex Rg) (hw : color Rg w=true) :
      Z Rg w≤centralizer (Q Rg w:Set (FreeAmalgam Rg)) := by
    intro z hz
    rw [Z,if_neg (by simp [hw])] at hz
    exact (mem_omegaCenter_iff.mp hz).2.2
  have hHC : H≤centralizer (stabilizer Rg c:Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgenC]
    exact sup_le (le_centralizer_iff.mp (inf_le_right.trans (hseed _ ht)))
      (le_centralizer_iff.mp (inf_le_left.trans hRf))
  have hHv : H≤Z Rg v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors Rg c hct hcv
    rw [←hyt,Z_act]
    rw [←terminal_central_fixed_map H (stabilizer Rg c) hHC ((stabilizer Rg c).inv_mem hy)]
    exact map_mono inf_le_right
  have hc0 : color Rg c=false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hv : color Rg v=true := by
    have hh := adjacent_color_ne Rg hcv
    rw [hc0] at hh
    cases he : color Rg v <;> simp_all
  have hHD : H≤centralizer (stabilizer Rg z:Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgenD]
    exact sup_le (le_centralizer_iff.mp (hHv.trans (hseed _ hv)))
      (le_centralizer_iff.mp (inf_le_left.trans hRg))
  have hHA : H≤centralizer (stabilizer Rg a:Set (FreeAmalgam Rg)) := by
    rw [←hxa,stabilizer_act]
    have hh := (map_mono (f:=(MulAut.conj x⁻¹).toMonoidHom) hHD).trans
      (map_centralizer_le_centralizer_image _ _)
    rwa [terminal_central_fixed_map H (stabilizer Rg c) hHC ((stabilizer Rg c).inv_mem hx)] at hh
  exact hnon hHA

include h e hz hk in
/-- In the actual three-position configuration the critical commutator is
noncentral at the middle vertex. The proof transports an edge seed through
the same middle stabilizer and uses the second generating edge; endpoint
noncentrality alone is not substituted for this assertion. -/
theorem critical_commutator_not_central_at_shift_vertex

    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (c v z k : Vertex Rg)
    (hct : Adjacent Rg c (p.walk.getVert 1)) (hcv : Adjacent Rg c v)
    (hgen : Q Rg v ⊔ Z Rg k = stabilizer Rg z)
    (hHk : ⁅Z Rg a,Z Rg a'⁆ ≤ centralizer (Z Rg k : Set (FreeAmalgam Rg)))
    (x : FreeAmalgam Rg) (hx : x ∈ stabilizer Rg c)
    (hxa : act Rg x z = a) :
    ¬ ⁅Z Rg a,Z Rg a'⁆ ≤
      centralizer (stabilizer Rg c : Set (FreeAmalgam Rg)) := by
  let H := ⁅Z Rg a,Z Rg a'⁆
  intro hHC
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ sourceDistance_pos h
  have hat : Adjacent Rg a (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) hpos
  have ht : color Rg (p.walk.getVert 1) = true := by
    have hh := adjacent_color_ne Rg hat
    rw [p.start_color] at hh
    cases he : color Rg (p.walk.getVert 1) <;> simp_all
  have hHZ : H ≤ Z Rg a :=
    critical_seed_commutator_le h p
  have hZaQ : Z Rg a ≤ Q Rg a := by
    apply Z_le_Q_of_dist_lt Rg a ((sourceGeometry h).exists_critical a p.start_color)
    rw [SimpleGraph.dist_self,(sourceGeometry h).distance_constant a p.start_color]
    exact sourceDistance_pos h
  have hHQt := (hHZ.trans hZaQ).trans (Q_le_adjacent_h Rg ht hat)
  have hQtC : Q Rg (p.walk.getVert 1) ≤ stabilizer Rg c :=
    fun _ he => he.2 _ (adjacent_symm Rg hct)
  have hHseed : H ≤ Z Rg (p.walk.getVert 1) := by
    intro z hz
    rw [Z,if_neg (by simp [ht])]
    let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
    exact mem_omegaCenter_iff.mpr ⟨hHQt hz,
      elemPow_eq_one_of_isElementaryAbelian z (hHZ hz),
      (hHC.trans (centralizer_le hQtC)) hz⟩
  have hHv : H ≤ Z Rg v := by
    obtain ⟨y,hy,hyt⟩ := stabilizer_transitive_neighbors Rg c hct hcv
    rw [←hyt,Z_act,←terminal_central_fixed_map H (stabilizer Rg c) hHC
      ((stabilizer Rg c).inv_mem hy)]
    exact map_mono hHseed
  have hc0 : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hv : color Rg v = true := by
    have hh := adjacent_color_ne Rg hcv
    rw [hc0] at hh
    cases he : color Rg v <;> simp_all
  have hHvQ : H ≤ centralizer (Q Rg v : Set (FreeAmalgam Rg)) := by
    intro z hz
    have hh := hHv hz
    rw [Z,if_neg (by simp [hv])] at hh
    exact (mem_omegaCenter_iff.mp hh).2.2
  have hHZ : H ≤ centralizer (stabilizer Rg z : Set (FreeAmalgam Rg)) := by
    apply le_centralizer_iff.mp
    rw [←hgen]
    exact sup_le (le_centralizer_iff.mp hHvQ) (le_centralizer_iff.mp hHk)
  apply critical_commutator_not_central h e hz hk p
  change H ≤ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))
  rw [←hxa,stabilizer_act]
  have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hHZ).trans
    (map_centralizer_le_centralizer_image _ _)
  rwa [terminal_central_fixed_map H (stabilizer Rg c) hHC
    ((stabilizer Rg c).inv_mem hx)] at hh


/-- A generating backward shift on the original graph. -/
structure BorelBackwardShift {a z : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a z) where
  start : Vertex Rg
  edge : Vertex Rg
  transporter : FreeAmalgam Rg
  transporter_mem : transporter ∈ stabilizer Rg a
  start_eq : act Rg transporter (p.walk.getVert 2) = start
  adjacent_start : Adjacent Rg a edge
  adjacent_shift : Adjacent Rg start edge
  generation : Q Rg edge ⊔ Z Rg z = stabilizer Rg a
  path : CriticalPath Rg (sourceGeometry h) start
    (p.walk.getVert (p.walk.length-2))
  first : path.walk.getVert 1 = edge
  overlap : ∀ i ≤ p.walk.length-2, path.walk.getVert (i+2) = p.walk.getVert i

include h e hz hk in
private theorem borel_large_backward_step_base
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg (alpha Rg))) :
    ∃ c t x, x ∈ stabilizer Rg (alpha Rg) ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg (alpha Rg) t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  have hl : p.walk.length = sourceDistance h := p.length_eq_b
  have hadj : Adjacent Rg (p.walk.getVert 2) (p.walk.getVert 1) :=
    adjacent_symm Rg ((cosetGraph_adj Rg _ _).mp
      (p.walk.adj_getVert_succ (i := 1) (by omega)))
  obtain ⟨t,hat,hgen,x,hx,hxt,q,hqt,hover,_⟩ :=
    large_remaining_backward_shift_of_two_lt_slice h e hz hk (by omega) u (Or.inr hR)
      p hlarge hadj (borel_forward_slice_strict h e hz hk hb u hR p)
  refine ⟨_,t,x,hx,hxt,rfl,hat,?_,hgen,q,hqt,hover⟩
  rw [←hxt]
  exact (adjacent_act_iff Rg x _ _).mpr hadj


/-- Above distance four a large critical image supplies a generating backward
shift. The chosen local conjugator and every shared vertex are retained. -/
theorem borel_large_backward_step_at
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (hlarge : 4 ≤ (Q Rg a').relIndex (Z Rg a)) :
    ∃ c t x, x ∈ stabilizer Rg a ∧
      act Rg x (p.walk.getVert 1) = t ∧
      act Rg x (p.walk.getVert 2) = c ∧
      Adjacent Rg a t ∧ Adjacent Rg c t ∧
      Q Rg t ⊔ Z Rg a' = stabilizer Rg a ∧
      ∃ q : CriticalPath Rg (sourceGeometry h) c
          (p.walk.getVert (p.walk.length-2)),
        q.walk.getVert 1 = t ∧
        (∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  have hbase : act Rg g⁻¹ a = alpha Rg := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := borel_large_backward_step_base h e hz hk hb u hR
    (z := act Rg g⁻¹ a')
  rw [←hbase] at base
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hover⟩ := base (p.act g⁻¹) (by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge)
  change act Rg x ((actWalk Rg g⁻¹ p.walk).getVert 2) = c at hxc
  rw [actWalk_getVert] at hxc
  let y := g⁻¹*x*g
  have hy (v : Vertex Rg) :
      act Rg y v = act Rg g (act Rg x (act Rg g⁻¹ v)) := by
    simp only [y,act_mul]
  have hcancel (v : Vertex Rg) : act Rg g (act Rg g⁻¹ v) = v := by
    rw [←act_mul,inv_mul_cancel,act_one]
  have hqc : ∃ r : CriticalPath Rg (sourceGeometry h)
      (act Rg g c)
      (act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2))),
      r.walk.getVert 1 = act Rg g t ∧
      ∀ i ≤ p.walk.length-2, r.walk.getVert (i+2) = p.walk.getVert i := by
    refine ⟨q.act g,?_,?_⟩
    · simpa only [CriticalPath.act,actWalk_getVert] using congrArg (act Rg g) hq1
    · intro i hi
      have he := congrArg (act Rg g) (hover i (by
        simpa only [CriticalPath.act,actWalk_length] using hi))
      simpa only [CriticalPath.act,actWalk_getVert,hcancel] using he
  have hend : act Rg g ((p.act g⁻¹).walk.getVert ((p.act g⁻¹).walk.length-2)) =
      p.walk.getVert (p.walk.length-2) := by
    change act Rg g ((actWalk Rg g⁻¹ p.walk).getVert
      ((actWalk Rg g⁻¹ p.walk).length-2)) = _
    rw [actWalk_length,actWalk_getVert,hcancel]
  rw [hend] at hqc
  obtain ⟨r,hr1,hrover⟩ := hqc
  refine ⟨act Rg g c,act Rg g t,y,?_,?_,?_,?_,?_,?_,r,hr1,hrover⟩
  · change act Rg y a = a
    rw [hy,show act Rg x (act Rg g⁻¹ a) = act Rg g⁻¹ a from hx,hcancel]
  · rw [hy]
    have hh := congrArg (act Rg g) hxt
    simpa only [CriticalPath.act,actWalk_getVert] using hh
  · rw [hy,hxc]
  · simpa only [hcancel] using (adjacent_act_iff Rg g _ _).mpr hat
  · exact (adjacent_act_iff Rg g _ _).mpr hct
  · have he := congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) hgen
    rw [Subgroup.map_sup,←Q_act,←Z_act,←stabilizer_act,hcancel,hcancel] at he
    exact he


include h e hz hk in
/-- A large critical path has a generating shift with its literal edge transporter. -/
theorem borel_large_backwardShift
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z)
    (hlarge : 4 ≤ (Q Rg z).relIndex (Z Rg a)) :
    ∃ q : BorelBackwardShift (h := h) p,
      act Rg q.transporter (p.walk.getVert 1) = q.edge := by
  obtain ⟨c,t,x,hx,hxt,hxc,hat,hct,hgen,q,hq1,hqo⟩ :=
    borel_large_backward_step_at h e hz hk hb u hR p hlarge
  exact ⟨⟨c,t,x,hx,hxc,hat,hct,hgen,q,hq1,hqo⟩,hxt⟩
include h e hz hk in
/-- Two generating backward shifts have small critical image and a
noncentral line at the intermediate vertex. -/
theorem two_borel_backward_shifts_small_moving
    (hb : 4 < sourceDistance h)
    {a a' : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) a a')
    (q : BorelBackwardShift (h := h) p) (r : BorelBackwardShift (h := h) q.path) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    (¬ ⁅Z Rg r.start,Z Rg z⁆ ≤
      centralizer (stabilizer Rg q.start : Set (FreeAmalgam Rg))) ∧
    (Q Rg z).relIndex (Z Rg r.start) = 2 ∧
    (Q Rg r.start).relIndex (Z Rg z) = 2 ∧
    Nat.card (⁅Z Rg r.start,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
    ¬ Q Rg (r.path.walk.getVert 1) ≤ centralizer
      ((⁅Z Rg r.start,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) : Set _) := by
  have hb2 : 2 < sourceDistance h := by omega
  have hq2 : q.path.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (Nat.zero_le _)
  have hyz : act Rg r.transporter a = r.start := by
    simpa only [hq2] using r.start_eq
  have hlenP : p.walk.length = sourceDistance h := p.length_eq_b
  have hlenQ : q.path.walk.length = sourceDistance h := q.path.length_eq_b
  have hdist1 : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2))
      (p.walk.getVert (p.walk.length-2)) = 2 := by
    rw [q.path.dist_end]
    omega
  have hdist2 : (cosetGraph Rg).dist (p.walk.getVert (p.walk.length-2)) a' = 2 := by
    rw [p.dist_end]
    omega
  have hdist : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2)) a' ≤ 4 := by
    have hh := (cosetGraph_connected Rg).dist_triangle
      (u := q.path.walk.getVert (q.path.walk.length-2)) (v := p.walk.getVert (p.walk.length-2)) (w := a')
    omega
  have hHe : ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
      Z Rg (q.path.walk.getVert (q.path.walk.length-2)) :=
    by
      rw [commutator_comm]
      exact le_normalizer_iff_commutator_le_left.mp
        ((Z_le_stabilizer_of_dist_le r.start _ r.path.critical.1.le).trans (Z_normalized Rg _))
  have hcent (w : Vertex Rg) (hw : color Rg w = false)
      (hdist : (cosetGraph Rg).dist (q.path.walk.getVert (q.path.walk.length-2)) w < sourceDistance h) :
      ⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ ≤
        centralizer (Z Rg w : Set (FreeAmalgam Rg)) := by
    apply (hHe.trans (Z_le_Q_of_dist_lt Rg _
      ((sourceGeometry h).exists_critical _ r.path.end_color) ?_)).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q Rg w hw)))
    rwa [(sourceGeometry h).distance_constant _ r.path.end_color]
  have hnc := critical_commutator_not_central_at_shift_vertex h e hz hk r.path
    q.start q.edge a a' (by rw [r.first]; exact r.adjacent_start)
    q.adjacent_shift q.generation (hcent _ p.end_color (by omega)) r.transporter r.transporter_mem hyz
  have hsmall : (Q Rg (q.path.walk.getVert (q.path.walk.length-2))).relIndex
      (Z Rg r.start) < 4 := by
    by_contra! hlarge
    exact large_critical_two_generating_edges_false h e hz hk r.path hlarge
      q.start q.edge a (p.walk.getVert (p.walk.length-2)) a'
      (by rw [r.first]; exact r.adjacent_start) q.adjacent_shift
      (by rw [r.first]; exact r.generation) q.generation
      (hcent _ q.path.end_color (by omega)) (hcent _ p.end_color (by omega))
      r.transporter r.transporter_mem hyz
  have hi := small_critical_indices h e hz hk r.path hsmall
  refine ⟨hnc,hi.1,hi.2,small_critical_commutator_card h e hz hk r.path hsmall,?_⟩
  intro hfixed
  apply hnc
  apply le_centralizer_iff.mp
  rw [←r.generation]
  exact sup_le (by simpa only [r.first] using hfixed)
    (le_centralizer_iff.mp (hcent _ q.path.end_color (by omega)))


include h e hz hk in
/-- A large critical image cannot persist through two successive generating
backward shifts. This constructs the small-image case rather than assuming it. -/
theorem borel_small_critical_reachable
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    (Q Rg z).relIndex (Z Rg a) = 2 ∨
    ∃ q : BorelBackwardShift (h := h) p,
      act Rg q.transporter (p.walk.getVert 1) = q.edge ∧
      ((Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) = 2 ∨
        ∃ r : BorelBackwardShift (h := h) q.path,
          act Rg r.transporter (q.path.walk.getVert 1) = r.edge ∧
          (Q Rg (q.path.walk.getVert (q.path.walk.length-2))).relIndex (Z Rg r.start) = 2 ∧
          (Q Rg r.start).relIndex (Z Rg (q.path.walk.getVert (q.path.walk.length-2))) = 2 ∧
          Nat.card (⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ :
            Subgroup (FreeAmalgam Rg)) = 2 ∧
          ¬ Q Rg r.edge ≤ centralizer
            ((⁅Z Rg r.start,Z Rg (q.path.walk.getVert (q.path.walk.length-2))⁆ :
              Subgroup (FreeAmalgam Rg)) : Set (FreeAmalgam Rg))) := by
  by_cases hp : (Q Rg z).relIndex (Z Rg a) < 4
  · exact Or.inl (small_critical_indices h e hz hk p hp).1
  obtain ⟨q,hq⟩ := borel_large_backwardShift h e hz hk hb u hR p (by omega)
  refine Or.inr ⟨q,hq,?_⟩
  by_cases hqsmall : (Q Rg (p.walk.getVert (p.walk.length-2))).relIndex (Z Rg q.start) < 4
  · exact Or.inl (small_critical_indices h e hz hk q.path hqsmall).1
  obtain ⟨r,hr⟩ := borel_large_backwardShift h e hz hk hb u hR q.path (by omega)
  have hd := two_borel_backward_shifts_small_moving h e hz hk hb p q r
  refine Or.inr ⟨r,hr,hd.2.1,hd.2.2.1,hd.2.2.2.1,?_⟩
  simpa only [r.first] using hd.2.2.2.2

include h e hz hk in
private theorem borel_exists_small_critical
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    ∃ a z, ∃ _p : CriticalPath Rg (sourceGeometry h) a z,
      (Q Rg z).relIndex (Z Rg a) = 2 := by
  obtain ⟨z,hzcrit⟩ := criticalPair_exists Rg (alpha Rg)
    ((sourceGeometry h).exists_critical (alpha Rg) rfl)
  let p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z := CriticalPath.ofPair rfl hzcrit
  rcases borel_small_critical_reachable h e hz hk hb u hR p with hp | ⟨q,_,hq | ⟨r,_,hr,_⟩⟩
  · exact ⟨_,_,p,hp⟩
  · exact ⟨_,_,q.path,hq⟩
  · exact ⟨_,_,r.path,hr⟩

include h e hz hk in
/-- At every original component vertex there is a critical pair with both
indices two and a noncentral commutator of order two. Both forward bounds
are strict; the odd cubic kernel and both full covers are retained. -/
theorem borel_small_critical_at
    (hb : 4 < sourceDistance h)
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    (a : Vertex Rg) (ha : color Rg a = false) :
    ∃ z, ∃ p : CriticalPath Rg (sourceGeometry h) a z,
      (Q Rg z).relIndex (Z Rg a) = 2 ∧
      (Q Rg a).relIndex (Z Rg z) = 2 ∧
      Nat.card (⁅Z Rg a,Z Rg z⁆ : Subgroup (FreeAmalgam Rg)) = 2 ∧
      (⁅Z Rg a,Z Rg z⁆ ⊓
        centralizer (stabilizer Rg a : Set (FreeAmalgam Rg)) = ⊥) ∧
      2 < (B Rg a ((sourceGeometry h).Z_normal _)).relIndex (U Rg (p.walk.getVert 2)) ∧
      2 < (B Rg z ((sourceGeometry h).Z_normal _)).relIndex
        (U Rg (p.walk.getVert (p.walk.length-2))) := by
  obtain ⟨c,w,p,hp⟩ := borel_exists_small_critical h e hz hk hb u hR
  obtain ⟨g,hg⟩ := exists_mVertex_of_color Rg p.start_color
  obtain ⟨k,hkvert⟩ := exists_mVertex_of_color Rg ha
  let x := g⁻¹*k
  have hxa : act Rg x c = a := by
    rw [hg,hkvert,act_mVertex]
    dsimp only [x]
    rw [mul_inv_cancel_left]
  have hsmall : (Q Rg (act Rg x w)).relIndex (Z Rg (act Rg x c)) = 2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hpath : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg x c) (act Rg x w),
      (Q Rg (act Rg x w)).relIndex (Z Rg (act Rg x c)) = 2 := ⟨p.act x,hsmall⟩
  rw [hxa] at hpath
  obtain ⟨q,hq⟩ := hpath
  have hlt : (Q Rg (act Rg x w)).relIndex (Z Rg a) < 4 := by rw [hq]; decide
  refine ⟨_,q,hq,(small_critical_indices h e hz hk q hlt).2,
    small_critical_commutator_card h e hz hk q hlt,
    small_critical_commutator_inf_centralizer h e hz hk q hlt,
    borel_forward_slice_strict_at h e hz hk hb u hR q,?_⟩
  let rev : CriticalPath Rg (sourceGeometry h) (act Rg x w) a :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        a q.start_color (by
          rw [(sourceGeometry h).distance_constant a q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hh := borel_forward_slice_strict_at h e hz hk hb u hR rev
  change 2 < (B Rg (act Rg x w) _).relIndex (U Rg (q.walk.reverse.getVert 2)) at hh
  rwa [SimpleGraph.Walk.getVert_reverse] at hh

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
