module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ContainedEndpointAlignment
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NonplaneIndividualPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TerminalIndices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverKernels

/-!
# Unequal-mover terminal paths and full critical-kernel normalizers

The root, nonplane and contained endpoint selections give one uniform
backward choice at the literal two-step neighbor. The contained choice
retains normalization by the whole marked Sylow, allowing the nonplane
alternative to use the very same quotient map. Each choice preserves its
residual transporter, edge generation, original-vertex mover fixedness and
individual-residual or nonsplitting alternative.

Iterating these choices preserves unequal neighboring movers and every
geodesic overlap. Two successive edge generations place the critical
commutator's first-edge intersection in three full vertex centers, forcing
both critical images to have field order. The resulting whole-X splitting
transports to every original-color vertex and removes the nonsplitting
alternative. Thus the actual individual mover and endpoint generate the
required residual, without assuming full vertex generation by that mover.

On this same sequence, the full critical kernel escapes the preceding B.
If the preceding endpoint normalized that kernel joined with the preceding
seed, the residual would normalize a radius subgroup of index at most q³,
forcing its containment in B. The resulting contradiction also gives a
nonzero mutual critical-kernel commutator of order at least q, with identical
full Z-, X- and U-intersection commutators. All degrees and central
attachments are retained.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5), (5.7), (5.9)--(5.10), printed pp.915--923. The opposite
terminal normalizer comparison, the remaining distance exclusions and the
actual minimum characteristic-replacement distance-two witness remain
necessary. This makes no original-radical characteristic-control claim.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers

/-- The terminal unequal-mover choice retains the original mover's full-edge
fixed subgroup as well as the individual-residual/nonsplitting alternative. -/
@[expose] def unequalPathChoice {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (q : ℕ) (p : CriticalSegment geometry) (v w : Vertex R) : Prop :=
  pathOrbitChoice geometry p v w ∧
    Q R w ⊔ Z R p.last = stabilizer R p.first ∧
    Z R (p.path.walk.getVert 1) ⊓ centralizer
      (Subgroup.SmallMover.join (U R p.first) (Q R p.first) (Q R w) (q^2) : Set (FreeAmalgam R)) =
      Z R (p.path.walk.getVert 1) ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R)) ∧
    (Ltilde R p.first ≤ Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) (q^2) ⊔ Z R p.last ∨
      X R p.first ≠ U R p.first ⊔
        (X R p.first ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R))))

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit h [Finite H] in
private theorem first_adj {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 0 < geometry.b d.radical) :
    Adjacent d.radical p.first (p.path.walk.getVert 1) := by
  have hh := (cosetGraph_adj d.radical _ _).mp
    (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; exact hb : 0 < p.path.walk.length))
  simpa only [SimpleGraph.Walk.getVert_zero] using hh

/-- At the literal first two-step neighbor, all three critical-image branches
supply the same terminal choice. No marking or containment hypothesis remains. -/
theorem Input.replacement_unequal_terminal_step
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    ∃ v w, unequalPathChoice geometry (Nat.card F) p v w ∧
      Adjacent d.radical p.first w ∧ Adjacent d.radical v w ∧
      ¬ Z d.radical v ≤ Q d.radical (p.path.walk.getVert (geometry.b d.radical-2)) := by
  let a := p.first
  let z := p.last
  let t := p.path.walk.getVert 1
  let c := p.path.walk.getVert 2
  have hat := first_adj d p (by omega)
  have hct : Adjacent d.radical c t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp
      (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; omega : 1 < p.path.walk.length)))
  have hne' : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hne
  have hnormal := h.replacement_path_neighbor_join_not_normal d p.path hb
  have from_individual (g : FreeAmalgam d.radical) (hg : g∈Ltilde d.radical a)
      (haw : Adjacent d.radical a (act d.radical g⁻¹ t))
      (hvw : Adjacent d.radical (act d.radical g⁻¹ c) (act d.radical g⁻¹ t))
      (hi : (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical (act d.radical g⁻¹ c)) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
      (hgen : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ c))
          (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2)) ⊔ Z d.radical z = stabilizer d.radical a)
      (hres : Ltilde d.radical a ≤ Subgroup.SmallMover.join (U d.radical (act d.radical g⁻¹ c))
        (Q d.radical (act d.radical g⁻¹ c)) (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) ⊔ Z d.radical z)
      (hfixed : Z d.radical t ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (act d.radical g⁻¹ t)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
      (back : CriticalPath d.radical geometry (act d.radical g⁻¹ c) (p.path.walk.getVert (p.path.walk.length-2))) :
      ∃ v w, unequalPathChoice geometry (Nat.card F) p v w ∧
        Adjacent d.radical p.first w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical v ≤ Q d.radical (p.path.walk.getVert (geometry.b d.radical-2)) := by
    refine ⟨act d.radical g⁻¹ c,act d.radical g⁻¹ t,
      ⟨⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,rfl,rfl,hi⟩,?_,hfixed,Or.inl hres⟩,haw,hvw,?_⟩
    · apply le_antisymm
      · exact sup_le (fun _ hx => hx.2 a (adjacent_symm d.radical haw))
          (p.path.endpoint_Z_le_start_stabilizer (by omega))
      · rw [←hgen]
        exact sup_le_sup_right (sup_le (Subgroup.SmallMover.join_le _ _ _ _)
          (Subgroup.SmallMover.join_le _ _ _ _)) _
    · simpa only [p.path.length_eq_b] using back.critical.2
  by_cases hsmall : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2
  · obtain ⟨g,hg,haw,hvw,hi,htransport,hgen,hres,hfixed,hOriginal,
      hquadA,hquadC,hcube,hnot,hlarge,hn,back,hfirst,hover⟩ :=
      h.replacement_unequal_root_backward_path d p.path hb.le hat rfl hct hsmall
        (h.replacement_path_moving_index_gt_field d p.path hb) hne'
    rw [htransport] at hgen
    exact from_individual g hg haw hvw hi hgen hres hOriginal back
  have hlarge := Nat.le_of_not_gt hsmall
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_contained_terminal_paired_paths_original_fixed_normalized d p.path hb hat rfl hne' hlarge
  by_cases hc : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype
  · obtain ⟨hJplane,hZJ,u,v,hu,hv,hup,hun,hf',hker,hat₁,hct₁,hAP,x,hx,hxc,hxc₀,
      hat₂,hct₂,hwhole₁,hwhole₂,hi₁,hi₂,hn₁,hn₂,⟨back,hfirst,hover⟩,hback₂,
      hfix₁,hfix₂,hOriginal₁,hOriginal₂,hD⟩ := hall hc
    let w := act d.radical v.val⁻¹ t
    let c₁ := act d.radical v.val⁻¹ c
    refine ⟨c₁,w,⟨⟨v.val⁻¹,(Ltilde d.radical a).inv_mem hv,rfl,rfl,hi₁⟩,
      hwhole₁,hOriginal₁,?_⟩,hat₁,hct₁,?_⟩
    · rcases hD with ⟨hres,_⟩ | ⟨_,_,_,_,hsplit,_⟩
      · left
        have hTS₁ : Q d.radical w ≤ stabilizer d.radical a :=
          fun _ hy => hy.2 a (adjacent_symm d.radical hat₁)
        have hES : Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
            (Q d.radical w) (Nat.card F^2) ≤ stabilizer d.radical a :=
          (Subgroup.SmallMover.join_le _ _ _ _).trans hTS₁
        have hh := map_mono (f := (stabilizer d.radical a).subtype) hres
        rw [Subgroup.map_sup,map_subgroupOf_eq_of_le
          (p.path.endpoint_Z_le_start_stabilizer (by omega)),map_subgroupOf_eq_of_le hES] at hh
        exact hh.trans_eq (sup_comm _ _)
      · exact Or.inr hsplit
    · simpa only [p.path.length_eq_b] using back.critical.2
  · obtain ⟨g,hg,hres,haw,hvw,hi,htransport,hgen,hfixed,hOriginal,
      hquadA,hquadC,hcube,hbranch,hn,back,hfirst,hover⟩ :=
      h.replacement_unequal_nonplane_individual_backward_path d p.path hb.le hat rfl hct
        hnormal hne' B hB f hf hfQ hTf hTn hindex hc
    rw [htransport] at hgen
    exact from_individual g hg haw hvw hi hgen hres hOriginal back

omit h in
private theorem terminal_backward_mover_agreement {M : Type*} [Group M] [Finite M]
    {R : Subgroup M} {geometry : Geometry R} (q : ℕ) (hb : 2 ≤ geometry.b R)
    {p p' : CriticalSegment geometry} (hl : BackwardLink geometry (pathOrbitChoice geometry) p p') :
    pathMoverAgreement q p' 0 ↔ pathMoverAgreement q p 0 := by
  obtain ⟨t,⟨g,hg,hd,ht,_⟩,_,_,hqt⟩ := hl.choice
  have hga : act R g p.first=p.first := Ltilde_le_stabilizer _ hg
  have htwo : p'.path.walk.getVert 2=p.first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hl.overlap 0 hb
  have hmap (a t : Vertex R) :
      Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
        (Q R (act R g t)) (q^2) =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) (q^2)).map
        (MulAut.conj g⁻¹).toMonoidHom := by
    rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]
  have hJa := hmap p.first (p.path.walk.getVert 1)
  rw [hga] at hJa
  simp only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
  rw [htwo,hqt,ht,hd,hJa,hmap]
  exact ⟨fun he => (Subgroup.map_injective (MulAut.conj g⁻¹).injective he).symm,
    fun he => congrArg (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom) he.symm⟩

/-- The unequal branch has an actual infinite source sequence, preserving
its residual choices, original-mover fixedness and generation alternatives. -/
theorem Input.replacement_unequal_terminal_paths
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i, ¬ pathMoverAgreement (Nat.card F) (s i) 0) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) := by
  let P := {r : CriticalSegment geometry // ¬ pathMoverAgreement (Nat.card F) r 0}
  have hstep (r : P) : ∃ q : P,
      BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) r.val q.val := by
    obtain ⟨q,hq⟩ := exists_backward_link (by omega) (unequalPathChoice geometry (Nat.card F)) r.val
      (h.replacement_unequal_terminal_step d r.val hb r.property)
    have hqo : BackwardLink geometry (pathOrbitChoice geometry) r.val q := by
      obtain ⟨w,hw,ha,hc,hfirst⟩ := hq.choice
      exact ⟨⟨w,hw.1,ha,hc,hfirst⟩,hq.last_eq,hq.overlap⟩
    exact ⟨⟨q,fun he => r.property ((terminal_backward_mover_agreement (Nat.card F) (by omega) hqo).mp he)⟩,hq⟩
  let next (r : P) : P := Classical.choose (hstep r)
  have hn (r : P) := Classical.choose_spec (hstep r)
  let seq : ℕ → P := Nat.rec ⟨p,hne⟩ (fun _ r => next r)
  let s : ℕ → CriticalSegment geometry := fun i => (seq i).val
  have hs (i : ℕ) : BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1)) := hn (seq i)
  exact ⟨s,rfl,hs,fun i => (seq i).property,
    fun i k j hj => iterated_overlap (unequalPathChoice geometry (Nat.card F)) s hs i k j hj⟩

/-- The literal unequal sequence gives the full three-center comparison of
MS93 (5.10), and hence both critical images have order q after two shifts. -/
theorem Input.replacement_unequal_terminal_indices
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i, ¬ pathMoverAgreement (Nat.card F) (s i) 0) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F ∧
        ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ⊓
          Z d.radical ((s (i+2)).path.walk.getVert 1) ≤
        (stabilizer d.radical (s (i+1)).first ⊓
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ⊓
        (stabilizer d.radical (s i).first ⊓
          centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) ⊓
        (stabilizer d.radical (s (i+2)).first ⊓
          centralizer (stabilizer d.radical (s (i+2)).first : Set (FreeAmalgam d.radical)))) := by
  obtain ⟨s,hs0,hs,hne,hover⟩ := h.replacement_unequal_terminal_paths d p hb hne
  refine ⟨s,hs0,hs,hne,hover,?_⟩
  intro i
  have hcent : ⁅Z d.radical (s (i+2)).first,Z d.radical (s (i+2)).last⁆ ⊓
      Z d.radical ((s (i+2)).path.walk.getVert 1) ≤
      (stabilizer d.radical (s (i+1)).first ⊓
        centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical))) ⊓
      (stabilizer d.radical (s i).first ⊓
        centralizer (stabilizer d.radical (s i).first : Set (FreeAmalgam d.radical))) ⊓
      (stabilizer d.radical (s (i+2)).first ⊓
        centralizer (stabilizer d.radical (s (i+2)).first : Set (FreeAmalgam d.radical))) := by
    obtain ⟨v,hv,hav,hcv,hfirst₁⟩ := (hs i).choice
    obtain ⟨t,ht,hct,hat,hfirst₂⟩ := (hs (i+1)).choice
    obtain ⟨y,hy,hyv,hyt,hidx⟩ := ht.1
    have he := (hs i).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at he
    rw [he] at hyv
    have htcol : color d.radical t=true := by
      have hn := adjacent_color_ne d.radical hct
      rw [(s (i+1)).path.start_color] at hn
      cases hh : color d.radical t <;> simp_all
    rw [show i+2=i+1+1 by omega,hfirst₂]
    exact fourth_shift_intersection_le_full_centers hb (unequalPathChoice geometry (Nat.card F))
      (fun j => s (i+j)) (fun j => by simpa only [Nat.add_assoc] using hs (i+j))
      hct hcv htcol ht.2.1.ge hv.2.1.ge y (Ltilde_le_stabilizer _ hy) hyv.symm
  obtain ⟨hia,hiz⟩ := h.replacement_critical_indices_eq_field_of_central_edge_intersection d
    (s (i+2)).path hb.le (first_adj d (s (i+2)) (by omega)) rfl
    (hcent.trans (inf_le_right.trans inf_le_right))
  exact ⟨hia,hiz,hcent⟩

omit h d in
private theorem X_split_transport {M : Type*} [Group M] {R : Subgroup M}
    {a c : Vertex R} (ha : color R a=false) (hc : color R c=false)
    (hs : X R a=U R a ⊔ (X R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)))) :
    X R c=U R c ⊔ (X R c ⊓ centralizer (stabilizer R c : Set (FreeAmalgam R))) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R ha
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R hc
  have hy : act R (g⁻¹*j) a=c := by
    rw [hg,act_mVertex,mul_inv_cancel_left,←hj]
  have hm := congrArg (Subgroup.map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom) hs
  rw [Subgroup.map_sup,map_inf _ _ _ (MulAut.conj (g⁻¹*j)⁻¹).injective,
    Theory.GroupTheory.map_centralizer_equiv] at hm
  change (X R a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom =
    (U R a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom ⊔
    (X R a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom ⊓
      centralizer (((stabilizer R a).map (MulAut.conj (g⁻¹*j)⁻¹).toMonoidHom :
        Subgroup (FreeAmalgam R)) : Set _) at hm
  rwa [←X_act,←U_act,←stabilizer_act,hy] at hm

/-- The actual unequal terminal sequence forces the full X decomposition
at every original-color vertex. All central fixed subgroups are retained. -/
theorem Input.replacement_unequal_terminal_X_decomposition
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0)
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  obtain ⟨s,hs0,hs,hne,hover,hdata⟩ := h.replacement_unequal_terminal_indices d p hb hne
  have hsmall : (Q d.radical (s 2).first).relIndex (Z d.radical (s 2).last)<Nat.card F^2 := by
    rw [(hdata 0).2.1]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  exact X_split_transport (s 2).path.start_color ha
    (h.replacement_root_X_decomposition_center d (s 2).path hb.le hsmall)

private theorem unequal_first_mover_normalizes_critical_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) ≤
        normalizer ((Z d.radical a ⊓ Q d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  have hn := h.replacement_root_small_movers_normalize_intersection d rev.path hb hi
  change Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical (path.walk.reverse.getVert (path.walk.reverse.length-1))) (Nat.card F^2) ≤
      normalizer ((Z d.radical a ⊓ Q d.radical z : Subgroup (FreeAmalgam d.radical)) : Set _) at hn
  rwa [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,
    show path.walk.length-(path.walk.length-1)=1 by rw [path.length_eq_b]; omega] at hn


/-- On the same unequal terminal paths, the preceding critical endpoint
cannot normalize the full critical kernel joined with the preceding seed.
This is the normalizer comparison entering MS93 (5.10), with the
individual-residual premise discharged and no discarded central kernel. -/
theorem Input.replacement_unequal_terminal_normalizer_escape
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) (hne : ¬ pathMoverAgreement (Nat.card F) p 0) :
    ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
      (∀ i, BackwardLink geometry (unequalPathChoice geometry (Nat.card F)) (s i) (s (i+1))) ∧
      (∀ i, ¬ pathMoverAgreement (Nat.card F) (s i) 0) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k) = (s i).path.walk.getVert j) ∧
      (∀ i, (Q d.radical (s (i+2)).last).relIndex (Z d.radical (s (i+2)).first)=Nat.card F ∧
        (Q d.radical (s (i+2)).first).relIndex (Z d.radical (s (i+2)).last)=Nat.card F) ∧
      (∀ i, let a := (s (i+3)).first
        let z := (s (i+3)).last
        let c := (s (i+2)).first
        ¬ Z d.radical a ⊓ Q d.radical z ≤ B d.radical c (geometry.Z_normal c)) ∧
      (∀ i, let a := (s (i+3)).first
        let z := (s (i+3)).last
        let c := (s (i+2)).first
        let e := (s (i+2)).last
        let E := Z d.radical a ⊓ Q d.radical z
        let D := ⁅E,Z d.radical e ⊓ Q d.radical c⁆
        (¬ Z d.radical e ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _)) ∧
        D ≠ ⊥ ∧ Nat.card F ≤ Nat.card D ∧
        ⁅E,X d.radical e ⊓ Q d.radical c⁆ = D ∧
        D = ⁅E,U d.radical e ⊓ Q d.radical c⁆) := by
  have hsplit (a : Vertex d.radical) (ha : color d.radical a=false) :=
    h.replacement_unequal_terminal_X_decomposition d p hb hne ha
  obtain ⟨s,hs0,hs,hne,hover,hdata⟩ := h.replacement_unequal_terminal_indices d p hb hne
  have hnotB (i : ℕ) : ¬ Z d.radical (s (i+3)).first ⊓ Q d.radical (s (i+3)).last ≤
      B d.radical (s (i+2)).first (geometry.Z_normal (s (i+2)).first) := by
    obtain ⟨w,hw,_,_,_⟩ := (hs (i+2)).choice
    obtain ⟨_,_,_,_,hidx⟩ := hw.1
    have hmove := h.replacement_path_moving_index_gt_field d (s (i+2)).path hb
    have hi := (hdata (i+1)).1
    simp only [show i+1+2=i+3 by omega] at hi
    simp only [show i+2+1=i+3 by omega] at hidx
    intro hle
    let := finite_Z d.radical (s (i+3)).first
    let : Finite (U d.radical (s (i+3)).first) := Finite.of_injective
      (inclusion (U_le_Z (s (i+3)).first)) (inclusion_injective _)
    have hZ := relIndex_le_of_le_left hle (L := Z d.radical (s (i+3)).first) index_ne_zero_of_finite
    simp only [inf_relIndex_left,hi] at hZ
    have hU := (B d.radical (s (i+2)).first (geometry.Z_normal (s (i+2)).first)).relIndex_le_of_le_right
      (U_le_Z (s (i+3)).first) index_ne_zero_of_finite
    rw [hidx] at hU
    exact hmove.not_ge (hU.trans hZ)
  refine ⟨s,hs0,hs,hne,hover,fun i => ⟨(hdata i).1,(hdata i).2.1⟩,hnotB,?_⟩
  intro i
  dsimp only
  let a := (s (i+3)).first
  let z := (s (i+3)).last
  let c := (s (i+2)).first
  let e := (s (i+2)).last
  let E := Z d.radical a ⊓ Q d.radical z
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical ((s (i+3)).path.walk.getVert 1)) (Nat.card F^2)
  obtain ⟨w,hw,hcw,haw,hfirst⟩ := (hs (i+2)).choice
  have hfirst' : (s (i+3)).path.walk.getVert 1=w := by simpa only [show i+2+1=i+3 by omega] using hfirst
  have hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F := by
    simpa only [show i+1+2=i+3 by omega] using (hdata (i+1)).1
  have hJN : J ≤ normalizer (E : Set (FreeAmalgam d.radical)) :=
    unequal_first_mover_normalizes_critical_kernel h d (s (i+3)).path hb.le hi
  have hJS : J ≤ stabilizer d.radical c := by
    dsimp only [J]
    rw [hfirst']
    exact (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 c (adjacent_symm d.radical hcw))
  have hres : Ltilde d.radical c ≤ J ⊔ Z d.radical e := by
    rcases hw.2.2.2 with hres | hbad
    · simpa only [J,hfirst',show i+2+1=i+3 by omega] using hres
    · exact False.elim (hbad (hsplit _ (s (i+2)).path.start_color))
  have hnormbad : ¬ Z d.radical e ≤ normalizer
      ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hnorm
    have hJY : J ≤ normalizer ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (le_inf hJN (hJS.trans (Z_normalized d.radical c))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
    have hLN : Ltilde d.radical c ≤ normalizer
        ((E ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      hres.trans (sup_le hJY hnorm)
    have hSV : Z d.radical a ⊔ Z d.radical c ≤ V d.radical c :=
      neighbor_seed_join_le_radius hcw haw
    let := finite_stabilizer d.radical c
    let : Finite (Z d.radical a ⊔ Z d.radical c : Subgroup (FreeAmalgam d.radical)) :=
      Finite.of_injective (inclusion (hSV.trans
        ((geometry.V_le_Q (by omega) c (s (i+2)).path.start_color).trans (fun _ hx => hx.1))))
        (inclusion_injective _)
    have hsmall : (Q d.radical c).relIndex (Z d.radical e)<Nat.card F^2 := by
      rw [(hdata i).2.1]
      have hq : 1<Nat.card F := Finite.one_lt_card
      nlinarith
    have hbound := h.replacement_root_neighbor_seed_index_le_cube d (s (i+2)).path hb.le hcw haw hsmall
    have hiY : (Z d.radical c).relIndex (E ⊔ Z d.radical c) ≤ Nat.card F^3 :=
      (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
        ((neighbor_seed_join_index_le geometry (by omega) (s (i+2)).path.start_color hcw haw).trans hbound)
    have hlt : Nat.card F^3 < Nat.card F^4 := Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide)
    exact hnotB i (le_sup_left.trans (h.replacement_small_radius_le_B d geometry (by omega)
      (s (i+2)).path.start_color (E ⊔ Z d.radical c)
      ((sup_le_sup inf_le_left le_rfl).trans hSV) hLN (hiY.trans_lt hlt)))
  have hEV : E ≤ V d.radical c := inf_le_left.trans
    (le_sup_left.trans (neighbor_seed_join_le_radius hcw haw))
  have hYQ := hEV.trans (geometry.V_le_Q (by omega) c (s (i+2)).path.start_color)
  have hdist : (cosetGraph d.radical).dist z e=2 := by
    simpa only [show i+2+1=i+3 by omega] using
      shifted_last_distance (unequalPathChoice geometry (Nat.card F)) s hs (i+2) 1 (by omega)
  have hYS : E ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two z e (s (i+3)).path.end_color
      (s (i+2)).path.end_color hdist.le)
  have heS := (s (i+2)).path.endpoint_Z_le_start_stabilizer (by omega : 0<geometry.b d.radical)
  have hbad : ¬ ⁅E,Z d.radical e⁆ ≤ Z d.radical c := by
    intro hdisp
    exact hnormbad (normalizes_sup_of_displacement _ _ _
      (heS.trans (Z_normalized d.radical c)) hdisp)
  have hsmall : (Q d.radical e).relIndex (Z d.radical c)<Nat.card F^2 := by
    rw [(hdata i).1]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hZX : Z d.radical e ≤ X d.radical e := geometry.omega_bound e (s (i+2)).path.end_color (by
    rw [geometry.distance_constant e (s (i+2)).path.end_color]
    exact lt_of_lt_of_le (by decide : 0<4) hb.le)
  have hneX : ⁅E,X d.radical e ⊓ Q d.radical c⁆ ≠ ⊥ := by
    intro hz
    have hfix := (commutator_eq_bot_iff_le_centralizer.mp hz).trans
      (centralizer_le (inf_le_inf_right _ hZX))
    apply hbad
    rw [commutator_comm]
    exact (h.replacement_critical_fixed_intersection_displacement d (s (i+2)).path (by omega)
      E hYS hYQ hfix).trans (critical_commutator_le_start (s (i+2)) (by omega))
  have hcard := h.replacement_root_intersection_commutator_card_ge_field d (s (i+2)).path hb.le hsmall E hYS hneX
  have hXU := (h.replacement_root_intersection_fixed_and_commutator d
    (s (i+2)).path hb.le hsmall E hYS).1
  have hZXeq : ⁅E,Z d.radical e ⊓ Q d.radical c⁆ = ⁅E,X d.radical e ⊓ Q d.radical c⁆ := by
    apply le_antisymm (commutator_mono le_rfl (inf_le_inf_right _ hZX))
    rw [hXU]
    exact commutator_mono le_rfl (inf_le_inf_right _ (U_le_Z e))
  exact ⟨hnormbad,by rwa [hZXeq],by rwa [hZXeq],hZXeq.symm,hZXeq.trans hXU⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
