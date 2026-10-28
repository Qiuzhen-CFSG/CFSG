module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalExclusion

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalLargeMoverExclusion

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallerLargePaths

/-!
# Paired source paths and full kernel escape for MS93 (5.11)

The distance-greater-than-four mover agreement and maximizing-parabolic
bound discharge the branch assumptions in the original two-member source
selection. In either critical-image case, orient the pair so that its first
member gives the backward critical path. Both generating triples, both
exact B-relative moving indices and the common fixed subgroup on the whole
Z-layer use the same conjugator. Iteration preserves every path overlap.

The whole-Z decomposition also removes the root-size assumption from the
cubic neighboring-seed index bound. A selected kernel of index at most q,
joined with the starting seed, cannot be vertex-normal: its section has
order at most q cubed, so residual invariance would put it in B, contrary
to the strict moving index. At the actual backward critical path, the
literal smaller mover normalizes that full Q-kernel. Therefore one of the
two endpoint generators must fail to normalize its join with the seed.

This is the paired-selection and kernel-normalizer step of MS93 (5.11),
printed pp.923--924, in Pushing up weak BN-pairs of rank two (1993).
The strict radius-image bound, its kernel-containment and common-commutator
comparison, the remaining distance exclusions and the minimum-replacement
distance-two witness remain with this reduction. No original-radical
characteristic-control assertion is made.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- An oriented source pair: the first member is the one retained by the
backward critical path; the same conjugator gives both generating triples
and the fixed subgroup on the entire starting seed. -/
@[expose] def pairedRadiusChoice {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (q : ℕ) (p : CriticalSegment geometry) (v w : Vertex R) : Prop :=
  pathOrbitChoice geometry p v w ∧
    ∃ x ∈ Ltilde R p.first,
      let v' := act R x v
      let w' := act R x w
      let J := Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) (q^2)
      let J' := Subgroup.SmallMover.join (U R v') (Q R v') (Q R w') (q^2)
      Adjacent R p.first w' ∧ Adjacent R v' w' ∧
      (B R p.first (geometry.Z_normal p.first)).relIndex (U R v') = nextMovingIndex p ∧
      (J ⊔ Z R p.last) ⊔ (Z R p.last).map (MulAut.conj x).toMonoidHom = stabilizer R p.first ∧
      (J' ⊔ Z R p.last) ⊔ (Z R p.last).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer R p.first ∧
      ((Z R p.first ⊓ centralizer (J : Set (FreeAmalgam R))) ⊓
        centralizer (J' : Set (FreeAmalgam R))) =
          Z R p.first ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R))

private theorem fixed_index_of_split {G : Type*} [Group G]
    (X U C E : Subgroup G) [IsMulCommutative X]
    (hUX : U ≤ X) (hsplit : X = U ⊔ C)
    (hCE : C ≤ centralizer (E : Set G)) :
    (centralizer (E : Set G)).relIndex X =
      (centralizer (E : Set G)).relIndex U := by
  let Y := X ⊓ centralizer (E : Set G)
  have hCX : C ≤ X := le_sup_right.trans_eq hsplit.symm
  have hjoin : U ⊔ Y = X := by
    apply le_antisymm (sup_le hUX inf_le_left)
    exact hsplit.le.trans (sup_le le_sup_left
      ((show C ≤ Y from le_inf hCX hCE).trans le_sup_right))
  let : CommGroup X := IsMulCommutative.instCommGroup
  have hh := relIndex_sup_right (U.subgroupOf X) (Y.subgroupOf X)
  rw [←subgroupOf_sup hUX (show Y ≤ X from inf_le_left),hjoin,
    relIndex_subgroupOf le_rfl,relIndex_subgroupOf hUX] at hh
  have he (V : Subgroup G) (hv : V ≤ X) :
      Y.subgroupOf V = (centralizer (E : Set G)).subgroupOf V := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hv x.property,hx⟩⟩
  change (Y.subgroupOf X).index = (Y.subgroupOf U).index at hh
  rwa [he X le_rfl,he U hUX] at hh



variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Above distance four, every critical path has an actual backward source
pair. Both critical-image branches use the same literal smaller movers,
full kernels and whole-Z fixed subgroup, with no branch premise remaining. -/
theorem Input.replacement_paired_radius_step
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ v w, pairedRadiusChoice geometry (Nat.card F) p v w ∧
      Adjacent d.radical p.first w ∧ Adjacent d.radical v w ∧
      ¬ Z d.radical v ≤ Q d.radical (p.path.walk.getVert (geometry.b d.radical-2)) := by
  let a := p.first
  let z := p.last
  let t := p.path.walk.getVert 1
  let c := p.path.walk.getVert 2
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; omega : 0 < p.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; omega : 1 < p.path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d p hb
  have hJm := h.replacement_small_mover_index_le_square_of_four_lt d geometry hb p.path.start_color hat
  have hmove := h.replacement_path_moving_index_gt_field d p.path hb
  have finish (g : FreeAmalgam d.radical) (hg : g ∈ Ltilde d.radical a)
      (x : FreeAmalgam d.radical) (hx : x ∈ Ltilde d.radical a)
      (ha₁ : Adjacent d.radical a (act d.radical g⁻¹ t))
      (hc₁ : Adjacent d.radical (act d.radical g⁻¹ c) (act d.radical g⁻¹ t))
      (ha₂ : Adjacent d.radical a (act d.radical x (act d.radical g⁻¹ t)))
      (hc₂ : Adjacent d.radical (act d.radical x (act d.radical g⁻¹ c))
        (act d.radical x (act d.radical g⁻¹ t)))
      (hgen₁ : (Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
          (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) ⊔
          Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
      (hgen₂ : (Subgroup.SmallMover.join (U d.radical (act d.radical x (act d.radical g⁻¹ c)))
          (Q d.radical (act d.radical x (act d.radical g⁻¹ c)))
          (Q d.radical (act d.radical x (act d.radical g⁻¹ t))) (Nat.card F^2) ⊔
          Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer d.radical a)
      (hfixed : (Z d.radical a ⊓ centralizer (Subgroup.SmallMover.join
          (U d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ c))
          (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
          centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical x (act d.radical g⁻¹ c)))
            (Q d.radical (act d.radical x (act d.radical g⁻¹ c)))
            (Q d.radical (act d.radical x (act d.radical g⁻¹ t))) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
      (v w : Vertex d.radical)
      (hwhich : (v=act d.radical g⁻¹ c ∧ w=act d.radical g⁻¹ t) ∨
        (v=act d.radical x (act d.radical g⁻¹ c) ∧ w=act d.radical x (act d.radical g⁻¹ t)))
      (back : CriticalPath d.radical geometry v (p.path.walk.getVert (p.path.walk.length-2))) :
      ∃ v w, pairedRadiusChoice geometry (Nat.card F) p v w ∧
        Adjacent d.radical p.first w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical v ≤ Q d.radical (p.path.walk.getVert (geometry.b d.radical-2)) := by
    have hi₁ := movingIndex_act geometry (d := c) (by omega) p.path.start_color g⁻¹
      ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
    have hi₂ := (movingIndex_act geometry (d := act d.radical g⁻¹ c) (by omega)
      p.path.start_color x (Ltilde_le_stabilizer a hx)).trans hi₁
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · refine ⟨_,_,⟨⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,rfl,rfl,hi₁⟩,
        x,hx,ha₂,hc₂,hi₂,hgen₁,hgen₂,hfixed⟩,ha₁,hc₁,?_⟩
      simpa only [p.path.length_eq_b] using back.critical.2
    · have hv : act d.radical x⁻¹ (act d.radical x (act d.radical g⁻¹ c))=act d.radical g⁻¹ c := by
        rw [←act_mul,mul_inv_cancel,act_one]
      have hw : act d.radical x⁻¹ (act d.radical x (act d.radical g⁻¹ t))=act d.radical g⁻¹ t := by
        rw [←act_mul,mul_inv_cancel,act_one]
      refine ⟨_,_,⟨⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,
        by rw [act_mul],by rw [act_mul],hi₂⟩,x⁻¹,(Ltilde d.radical a).inv_mem hx,?_⟩,ha₂,hc₂,?_⟩
      · dsimp only
        rw [hv,hw,inv_inv]
        exact ⟨ha₁,hc₁,hi₁,hgen₂,hgen₁,(inf_right_comm _ _ _).trans hfixed⟩
      · simpa only [p.path.length_eq_b] using back.critical.2
  by_cases hs : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2
  · obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
      hi₁,hi₂,hcenter₁,hcenter₂,hcomm₁,hcomm₂,hcenters,hinter,
      hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,v,hv,w,hwhich,haw,hvw,back,hfirst,hover⟩ :=
        h.replacement_equal_root_backward_path d p.path hb.le hat rfl hct hmove hequal hs hJm
    exact finish g hg x hx ha₁ hc₁ ha₂ hc₂ hgen₁ hgen₂ hfixed v w hwhich back
  · obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
      hgen₁,hgen₂,hfixed,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,hi,back,hfirst,hover⟩ :=
        h.replacement_equal_small_index_large_backward_path d p.path hb.le hat rfl hct
          (h.replacement_path_neighbor_join_not_normal d p.path hb) hequal (Nat.le_of_not_gt hs) hJm
    exact finish g hg x hx ha₁ hc₁ ha₂ hc₂ hgen₁ hgen₂ hfixed v w hwhich back

/-- The original path has arbitrarily many backward shifts retaining the
complete paired generation and whole-Z fixed clauses used in (5.11). -/
theorem Input.replacement_paired_radius_paths
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, Nat.card F < nextMovingIndex (s i)) := by
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega)
    (pairedRadiusChoice geometry (Nat.card F))
    (fun q => h.replacement_paired_radius_step d q hb) p
  exact ⟨s,hs0,hs,hover,fun i => h.replacement_path_moving_index_gt_field d (s i).path hb⟩

open CentralRootGeometry.SmallMovers

/-- The full edge seed has index at most q cubed in each neighboring
seed at every nonbinary degree, including all central attachments. -/
theorem Input.replacement_neighbor_seed_index_le_cube
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t v : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t) :
    (Z d.radical t).relIndex (Z d.radical v) ≤ Nat.card F^3 := by
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [ha] at hh
    cases ht : color d.radical t <;> simp_all
  have hZX := geometry.omega_bound a ha (by
    rw [geometry.distance_constant a ha]
    exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hZQ : Z d.radical a ≤ Q d.radical t :=
    (hZX.trans (omegaCenter_le _)).trans (Q_le_adjacent_h d.radical ht hat)
  have hTS : Q d.radical t ≤ stabilizer d.radical a :=
    fun _ hx => hx.2 a (adjacent_symm _ hat)
  have hfix : Z d.radical a ⊓ centralizer (Q d.radical t : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Z d.radical t := by
    ext x
    constructor
    · rintro ⟨hx,hc⟩
      refine ⟨hx,?_⟩
      rw [Z,if_neg (by rw [ht]; decide)]
      exact mem_omegaCenter_iff.mpr ⟨hZQ hx,(mem_omegaCenter_iff.mp (hZX hx)).2.1,hc⟩
    · rintro ⟨hx,hz⟩
      rw [Z,if_neg (by rw [ht]; decide)] at hz
      exact ⟨hx,(mem_omegaCenter_iff.mp hz).2.2⟩
  have heidx : (Z d.radical t).relIndex (Z d.radical a) =
      (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) := by
    rw [←inf_relIndex_left,←hfix,inf_relIndex_left]
  let := geometry.Z_elementary (by omega) a ha
  have hidxZ := fixed_index_of_split (Z d.radical a) (U d.radical a)
    (Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (Q d.radical t) (U_le_Z a) (h.replacement_Z_eq_U_sup_fixed d geometry hb ha)
    (inf_le_right.trans (centralizer_le hTS))
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hUS : U d.radical a ≤ stabilizer d.radical a := (U_le_Z a).trans (Z_le_stabilizer _ a)
  have hi := hidx ((Q d.radical t).subgroupOf (stabilizer d.radical a)) le_rfl
  rw [←Subgroup.SmallMover.centralizer_index_map (stabilizer d.radical a).subtype
    (stabilizer d.radical a).subtype_injective,
    map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hTS] at hi
  have hbound : (centralizer (Q d.radical t : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^3 := by
    rw [hi,←hcard]
    let T := (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f).subgroupOf unipotent
    have hd := (fixed T).finrank_quotient_add_finrank
    have hlo := Submodule.finrank_mono (standardPoint_le_fixed T)
    rw [finrank_point] at hlo
    have hv : Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier))=4 := by
      simp [CentralRootGeometry.SmallMovers.Vector]
    rw [hv] at hd
    apply Nat.pow_le_pow_right Nat.card_pos
    change Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) ≤ 3
    change Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) +
      Module.finrank E.Carrier (fixed T) = 4 at hd
    have hle : Module.finrank E.Carrier (CentralRootGeometry.SmallMovers.Vector (F := E.Carrier) ⧸ fixed T) + 1 ≤ 3 + 1 :=
      (Nat.add_le_add_left hlo _).trans_eq hd
    exact Nat.le_of_add_le_add_right hle
  have hbase : (Z d.radical t).relIndex (Z d.radical a) ≤ Nat.card F^3 := by
    rw [heidx]
    exact hidxZ ▸ hbound
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm _ hat) (adjacent_symm _ hvt)
  have hgt : act d.radical g t=t := hg
  have htransport : (Z d.radical t).relIndex (Z d.radical v)=
      (Z d.radical t).relIndex (Z d.radical a) := by
    conv_lhs => rw [←hga,←hgt]
    rw [Z_act,Z_act]
    exact relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective
  rwa [htransport]

/-- A selected seed kernel of index at most q cannot become invariant under
its whole starting vertex. The cubic neighboring-seed bound retains the
full central attachment in the small-radius argument. -/
theorem Input.replacement_paired_radius_kernel_not_normal
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) {v w : Vertex d.radical}
    (hchoice : pairedRadiusChoice geometry (Nat.card F) p v w)
    (haw : Adjacent d.radical p.first w) (hvw : Adjacent d.radical v w)
    (A : Subgroup (FreeAmalgam d.radical))
    (hi : A.relIndex (Z d.radical v) ≤ Nat.card F) :
    ¬ stabilizer d.radical p.first ≤ normalizer
      (((Z d.radical v ⊓ A) ⊔ Z d.radical p.first : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  intro hn
  let D := (Z d.radical v ⊓ A) ⊔ Z d.radical p.first
  have hYV := neighbor_seed_join_le_radius haw hvw
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) p.first p.path.start_color)
  let := finite_stabilizer d.radical p.first
  let : Finite (Z d.radical v ⊔ Z d.radical p.first : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hYQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  have hidx := (neighbor_seed_join_index_le geometry (by omega) p.path.start_color haw hvw).trans
    (h.replacement_neighbor_seed_index_le_cube d geometry hb.le p.path.start_color haw hvw)
  have hDi : (Z d.radical p.first).relIndex D < Nat.card F^4 :=
    lt_of_le_of_lt ((relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl)
      index_ne_zero_of_finite).trans hidx)
      ((pow_lt_pow_iff_right₀ (show 1<Nat.card F from Finite.one_lt_card)).mpr (by decide))
  have hDB := h.replacement_small_radius_le_B d geometry (by omega) p.path.start_color D
    ((sup_le_sup inf_le_left le_rfl).trans hYV) ((Ltilde_le_stabilizer p.first).trans hn) hDi
  have hkernel : Z d.radical v ⊓ A ≤ B d.radical p.first (geometry.Z_normal p.first) :=
    le_sup_left.trans hDB
  let := finite_Z d.radical v
  have hZi : (B d.radical p.first (geometry.Z_normal p.first)).relIndex (Z d.radical v) ≤ Nat.card F := by
    apply le_trans (relIndex_le_of_le_left hkernel index_ne_zero_of_finite)
    simpa only [inf_relIndex_left] using hi
  have hUi := (relIndex_le_of_le_right (H := B d.radical p.first (geometry.Z_normal p.first))
    (U_le_Z v) index_ne_zero_of_finite).trans hZi
  obtain ⟨y,hy,hyv,hyw,hindex⟩ := hchoice.1
  rw [hindex] at hUi
  exact (not_lt_of_ge hUi) (h.replacement_path_moving_index_gt_field d p.path hb)

/-- The literal smaller mover at the chosen backward path normalizes its
whole field-index kernel. This uses the same Q-intersection as (5.11),
not a quotient of the moving layer. -/
theorem Input.replacement_backward_small_mover_normalizes_kernel
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p')
    (hi : (Q d.radical p'.last).relIndex (Z d.radical p'.first) ≤ Nat.card F) :
    Subgroup.SmallMover.join (U d.radical p'.first) (Q d.radical p'.first)
      (Q d.radical (p'.path.walk.getVert 1)) (Nat.card F^2) ≤
      normalizer (((Z d.radical p'.first ⊓ Q d.radical p'.last) ⊔
        Z d.radical p.first : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  obtain ⟨w,hchoice,haw,hvw,hfirst⟩ := hl.choice
  have hlen : 4 < p'.path.walk.length := by rwa [p'.path.length_eq_b]
  have hAT : Z d.radical p'.last ≤ Q d.radical w := by
    rw [←hfirst]
    apply Z_le_Q_of_dist_lt _ p'.last (geometry.exists_critical p'.last p'.path.end_color)
    rw [SimpleGraph.dist_comm,p'.path.dist_end,geometry.distance_constant p'.last p'.path.end_color]
    change p'.path.walk.length-1 < geometry.b d.radical
    rw [p'.path.length_eq_b]
    omega
  have hYS : Z d.radical p'.first ≤ stabilizer d.radical p'.last :=
    Z_le_stabilizer_of_dist_le p'.first (geometry.exists_critical p'.first p'.path.start_color)
      p'.path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) p'.last p'.path.end_color
  have hfixed : Z d.radical p'.first ⊓ centralizer (Z d.radical p'.last : Set (FreeAmalgam d.radical)) =
      Z d.radical p'.first ⊓ Q d.radical p'.last := by
    rw [←hC]
    ext x
    exact ⟨fun hx => ⟨hx.1,hYS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  let := finite_Z d.radical p'.first
  have hUi : (centralizer (Z d.radical p'.last : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical p'.first) ≤ Nat.card F := by
    apply (relIndex_le_of_le_right (U_le_Z p'.first) index_ne_zero_of_finite).trans
    rwa [←inf_relIndex_left,hfixed,inf_relIndex_left]
  have hJn := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb.le
    p'.path.start_color hvw (Z d.radical p'.last) hAT hUi
  rw [hfixed] at hJn
  have hJZa := (Subgroup.SmallMover.join_le (U d.radical p'.first) (Q d.radical p'.first)
    (Q d.radical w) (Nat.card F^2)).trans
    ((show Q d.radical w ≤ stabilizer d.radical p.first from
      fun _ hx => hx.2 p.first (adjacent_symm d.radical haw)).trans (Z_normalized d.radical p.first))
  rw [hfirst]
  exact (le_inf hJn hJZa).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)

/-- In the small shifted-image branch, the actual generating pair contains
an endpoint that fails to normalize the selected full kernel joined with
the original seed. The same conjugator and whole-Z fixed clause are retained. -/
theorem Input.replacement_paired_radius_kernel_escape
    {geometry : Geometry d.radical} (p p' : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical)
    (hl : BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F)) p p') :
    ∃ x ∈ Ltilde d.radical p.first,
      let v := p'.first
      let w := p'.path.walk.getVert 1
      let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2)
      let J' := Subgroup.SmallMover.join (U d.radical (act d.radical x v))
        (Q d.radical (act d.radical x v)) (Q d.radical (act d.radical x w)) (Nat.card F^2)
      let D := (Z d.radical v ⊓ Q d.radical p'.last) ⊔ Z d.radical p.first
      (J ⊔ Z d.radical p.last) ⊔ (Z d.radical p.last).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical p.first ∧
      ((Z d.radical p.first ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J' : Set (FreeAmalgam d.radical))) =
          Z d.radical p.first ⊓ centralizer (stabilizer d.radical p.first : Set (FreeAmalgam d.radical)) ∧
      ((Q d.radical p'.last).relIndex (Z d.radical v) ≤ Nat.card F →
        (¬ Z d.radical p.last ≤ normalizer (D : Set (FreeAmalgam d.radical)) ∨
          ¬ (Z d.radical p.last).map (MulAut.conj x).toMonoidHom ≤
            normalizer (D : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨w,hchoice,haw,hvw,hfirst⟩ := hl.choice
  obtain ⟨x,hx,hax,hvx,hix,hgen,hgen',hfixed⟩ := hchoice.2
  refine ⟨x,hx,?_⟩
  dsimp only
  rw [hfirst]
  refine ⟨hgen,hfixed,?_⟩
  intro hi
  by_contra! hn
  have hJn := h.replacement_backward_small_mover_normalizes_kernel d p p' hb hl hi
  rw [hfirst] at hJn
  exact h.replacement_paired_radius_kernel_not_normal d p hb hchoice haw hvw
    (Q d.radical p'.last) hi (hgen ▸ sup_le (sup_le hJn hn.1) hn.2)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
