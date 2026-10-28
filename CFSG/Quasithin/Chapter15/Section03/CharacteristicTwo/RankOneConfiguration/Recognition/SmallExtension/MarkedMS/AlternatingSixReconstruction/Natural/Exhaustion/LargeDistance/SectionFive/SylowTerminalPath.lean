module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalIntersection

/-!
# Iterated shift paths and propagation of the terminal central factor

Each actual backward shift adds the relation between its zeroth and fourth
vertices, with the transporter in the second vertex stabilizer. Its literal
overlap carries every previously established two-step orbit relation.
Iteration therefore constructs a critical path satisfying all the orbit
relations in MS93 (5.10)(iii), without assuming them of the initial path.
A finite chain records its connection to that initial path.

A subgroup centralized by the first two component stabilizers is centralized
along the whole resulting path. If it is the full moving central attachment
at the second component vertex, that equality propagates along alternating
component vertices. Applied to the restricted-kernel span from
SylowTerminalIntersection, this fixes its central factor along the entire
preceding path, including its critical endpoint. In the nonnormalizing
branch the alternative remains either coincident commutator lines or the
full order-two moving attachment along those alternating vertices.

The original-radical consumer first uses its literal restricted embedding
and transporter, then constructs the finite chain and final three shifts.
It discharges every orbit-prefix premise and retains the exact index-two
central factor. Both moved covers and all central attachments are preserved.
The nonnormalizing contradiction, mover equality and core containment,
(5.11), the image-eight branch and distance-four whole-core estimates remain
with the large-distance assembly.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.10)(iii) and the central-intersection argument, printed p.922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalPath
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- The first n two-step orbit relations on the literal critical walk. -/
@[expose] def OrbitPrefix {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') (n : ℕ) : Prop :=
  ∀ i < n, 2*i+4 ≤ p.walk.length →
    ∃ x ∈ stabilizer d.radical (p.walk.getVert (2*i+2)),
      act d.radical x (p.walk.getVert (2*i)) = p.walk.getVert (2*i+4)

/-- A finite chain of actual generating backward shifts from the given path. -/
inductive ShiftChain {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    {c c' : Vertex d.radical} →
      CriticalPath d.radical (replacementGeometry h d) c c' → ℕ → Prop
  | nil : ShiftChain p p 0
  | step {c c' : Vertex d.radical}
      {v : CriticalPath d.radical (replacementGeometry h d) c c'} {n : ℕ}
      (chain : ShiftChain p v n) (q : BackwardShift (h := h) v) :
      ShiftChain p q.path (n+1)

/-- A backward shift adds the first orbit relation and transports the others
through its exact overlap. -/
theorem orbitPrefix_backwardShift
    (hb : 4 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) {n : ℕ} (hp : OrbitPrefix (h := h) p n) :
    OrbitPrefix (h := h) q.path (n+1) := by
  have hl : p.walk.length = replacementDistance h d := p.length_eq_b
  have hq : q.path.walk.length = replacementDistance h d := q.path.length_eq_b
  intro i hi hbound
  cases i with
  | zero =>
    have hq2 : q.path.walk.getVert 2 = a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using q.overlap 0 (by omega)
    have hq4 : q.path.walk.getVert 4 = p.walk.getVert 2 := q.overlap 2 (by omega)
    refine ⟨q.transporter⁻¹,?_,?_⟩
    · simpa only [Nat.mul_zero,Nat.zero_add,hq2] using
        (stabilizer d.radical a).inv_mem q.transporter_mem
    · simp only [Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero,hq4]
      rw [←q.start_eq,←act_mul,mul_inv_cancel,act_one]
  | succ i =>
    obtain ⟨x,hx,he⟩ := hp i (by omega) (by omega)
    have h0 : q.path.walk.getVert (2*(i+1)) = p.walk.getVert (2*i) := by
      simpa only [show 2*(i+1) = 2*i+2 by omega] using q.overlap (2*i) (by omega)
    have h2 : q.path.walk.getVert (2*(i+1)+2) = p.walk.getVert (2*i+2) := by
      simpa only [show 2*(i+1)+2 = (2*i+2)+2 by omega] using q.overlap (2*i+2) (by omega)
    have h4 : q.path.walk.getVert (2*(i+1)+4) = p.walk.getVert (2*i+4) := by
      simpa only [show 2*(i+1)+4 = (2*i+4)+2 by omega] using q.overlap (2*i+4) (by omega)
    exact ⟨x,by simpa only [h2] using hx,by simpa only [h0,h4] using he⟩

/-- Iteration supplies the source orbit relations; no path regularity is
assumed of the input critical path. The complete chain of generating shifts
is retained. -/
theorem exists_orbitPrefix_chain_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') (n : ℕ) :
    ∃ c c', ∃ v : CriticalPath d.radical (replacementGeometry h d) c c',
      ShiftChain (h := h) p v n ∧ OrbitPrefix (h := h) v n := by
  induction n with
  | zero => exact ⟨a,a',p,ShiftChain.nil,by intro i hi; omega⟩
  | succ n ih =>
    obtain ⟨c,c',v,hv,ho⟩ := ih
    obtain ⟨q,_⟩ := SylowShiftChain.backwardShift_with_edge hb hcard v
    exact ⟨_,_,q.path,ShiftChain.step hv q,orbitPrefix_backwardShift hb v q ho⟩

private theorem prefix_mono {a a' : Vertex d.radical}
    {p : CriticalPath d.radical (replacementGeometry h d) a a'} {m n : ℕ}
    (hp : OrbitPrefix (h := h) p n) (hm : m ≤ n) : OrbitPrefix (h := h) p m :=
  fun i hi => hp i (lt_of_lt_of_le hi hm)

private theorem full_prefix_shift
    (hb : 4 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (hp : OrbitPrefix (h := h) p (replacementDistance h d)) :
    OrbitPrefix (h := h) q.path (replacementDistance h d) :=
  prefix_mono (orbitPrefix_backwardShift hb p q hp) (Nat.le_succ _)

omit [Finite G] in
private theorem central_transport (A : Subgroup (FreeAmalgam d.radical))
    {a b c : Vertex d.radical}
    (ha : A ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hb : A ≤ centralizer (stabilizer d.radical b : Set (FreeAmalgam d.radical)))
    {x : FreeAmalgam d.radical} (hx : x ∈ stabilizer d.radical b)
    (he : act d.radical x a = c) :
    A ≤ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  rw [←he,stabilizer_act]
  have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) ha).trans
    (map_centralizer_le_centralizer_image _ _)
  have hfixed : A.map (MulAut.conj x⁻¹).toMonoidHom = A :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hb ((stabilizer d.radical b).inv_mem hx)))
  rwa [hfixed] at hh

/-- Centrality at the first two component vertices propagates along every
component vertex of an orbit-complete critical path. -/
theorem central_along_orbit_path
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : OrbitPrefix (h := h) p (replacementDistance h d))
    (A : Subgroup (FreeAmalgam d.radical))
    (h0 : A ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (h2 : A ≤ centralizer
      (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
    ∀ i, 2*i ≤ p.walk.length →
      A ≤ centralizer
        (stabilizer d.radical (p.walk.getVert (2*i)) : Set (FreeAmalgam d.radical)) := by
  intro i
  induction i using Nat.twoStepInduction with
  | zero => simpa only [Nat.mul_zero,SimpleGraph.Walk.getVert_zero] using fun _ => h0
  | one => simpa only [Nat.mul_one] using fun _ => h2
  | more i hi hi1 =>
    intro hib
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    obtain ⟨x,hx,he⟩ := hp i (by omega) (by omega)
    have hh := central_transport A (hi (by omega)) (hi1 (by omega)) hx he
    simpa only [Nat.mul_add,Nat.mul_one] using hh

/-- The terminal central factor is fixed along the entire preceding path,
not only at the three selected starts. -/
theorem three_shift_kernel_central_along_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : OrbitPrefix (h := h) r.path (replacementDistance h d)) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    (∀ i, 2*i ≤ r.path.walk.length → I ≤ centralizer
      (stabilizer d.radical (r.path.walk.getVert (2*i)) : Set (FreeAmalgam d.radical))) ∧
    I ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) := by
  let z := q.path.walk.getVert (q.path.walk.length-2)
  let v := r.path.walk.getVert (r.path.walk.length-2)
  let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
  let D := ⁅Z d.radical t.start,Z d.radical v⁆
  let I := (H ⊔ D) ⊓ Z d.radical t.edge
  have hc := SylowTerminalIntersection.three_shift_kernel_central_decomposition_knownSimple
    hb hcard p q r t
  have hr2 : r.path.walk.getVert 2 = q.start := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
  have hall := central_along_orbit_path r.path hr I hc.2.1 (by simpa only [hr2] using hc.2.2.1)
  refine ⟨hall,?_⟩
  obtain ⟨n,hn⟩ := replacementDistance_even h d
  have hl : r.path.walk.length = 2*n := r.path.length_eq_b.trans (by change replacementDistance h d = _; omega)
  have hh := hall n (by omega)
  rw [←hl,SimpleGraph.Walk.getVert_length] at hh
  exact hh

omit [Finite G] in
private theorem fixed_map (A : Subgroup (FreeAmalgam d.radical))
    {b : Vertex d.radical}
    (hb : A ≤ centralizer (stabilizer d.radical b : Set (FreeAmalgam d.radical)))
    {x : FreeAmalgam d.radical} (hx : x ∈ stabilizer d.radical b) :
    A.map (MulAut.conj x).toMonoidHom = A :=
  mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
    (le_centralizer_iff.mp hb hx))

omit [Finite G] in
private theorem attachment_transport (A : Subgroup (FreeAmalgam d.radical))
    {a b c : Vertex d.radical}
    (ha : A = U d.radical a ⊓ centralizer
      (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hb : A ≤ centralizer (stabilizer d.radical b : Set (FreeAmalgam d.radical)))
    {x : FreeAmalgam d.radical} (hx : x ∈ stabilizer d.radical b)
    (he : act d.radical x a = c) :
    A = U d.radical c ⊓ centralizer
      (stabilizer d.radical c : Set (FreeAmalgam d.radical)) := by
  have hmap : ∀ y (v : Vertex d.radical),
      (U d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))).map
        (MulAut.conj y⁻¹).toMonoidHom ≤
      U d.radical (act d.radical y v) ⊓ centralizer
        (stabilizer d.radical (act d.radical y v) : Set (FreeAmalgam d.radical)) := by
    intro y v
    apply le_inf
    · simpa only [U_act] using map_mono (f := (MulAut.conj y⁻¹).toMonoidHom)
        (inf_le_left : U d.radical v ⊓ centralizer
          (stabilizer d.radical v : Set (FreeAmalgam d.radical)) ≤ U d.radical v)
    · rw [stabilizer_act]
      exact (map_mono inf_le_right).trans (map_centralizer_le_centralizer_image _ _)
  have hforward := hmap x a
  rw [←ha,he,fixed_map A hb ((stabilizer d.radical b).inv_mem hx)] at hforward
  apply le_antisymm hforward
  have hback := hmap x⁻¹ c
  have heback : act d.radical x⁻¹ c = a := by
    rw [←he,←act_mul,mul_inv_cancel,act_one]
  rw [heback,←ha,inv_inv] at hback
  rw [←fixed_map A hb hx] at hback
  exact (map_le_map_iff_of_injective (MulAut.conj x).injective).mp hback

/-- Equality with the full moving central attachment propagates along each
parity class of component vertices, using centrality on the intermediate
vertices. -/
theorem attachment_along_orbit_path
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hp : OrbitPrefix (h := h) p (replacementDistance h d))
    (A : Subgroup (FreeAmalgam d.radical))
    (hc : ∀ i, 2*i ≤ p.walk.length → A ≤ centralizer
      (stabilizer d.radical (p.walk.getVert (2*i)) : Set (FreeAmalgam d.radical)))
    (h2 : A = U d.radical (p.walk.getVert 2) ⊓ centralizer
      (stabilizer d.radical (p.walk.getVert 2) : Set (FreeAmalgam d.radical))) :
    ∀ i, 4*i+2 ≤ p.walk.length → A = U d.radical (p.walk.getVert (4*i+2)) ⊓ centralizer
      (stabilizer d.radical (p.walk.getVert (4*i+2)) : Set (FreeAmalgam d.radical)) := by
  intro i
  induction i with
  | zero => simpa only [Nat.mul_zero,Nat.zero_add] using fun _ => h2
  | succ i ih =>
    intro hib
    have hl : p.walk.length = replacementDistance h d := p.length_eq_b
    obtain ⟨x,hx,he⟩ := hp (2*i+1) (by omega) (by omega)
    have hc' := hc (2*i+2) (by omega)
    have hA := ih (by omega)
    have hh := attachment_transport A
      (a := p.walk.getVert (2*(2*i+1)))
      (b := p.walk.getVert (2*(2*i+1)+2))
      (c := p.walk.getVert (2*(2*i+1)+4))
      (by simpa only [show 2*(2*i+1) = 4*i+2 by omega] using hA)
      (by simpa only [show 2*(2*i+1)+2 = 2*(2*i+2) by omega] using hc') hx he
    simpa only [show 2*(2*i+1)+4 = 4*(i+1)+2 by omega] using hh

/-- In the nonnormalizing branch, the two-line span is either a single line
or its entire central attachment propagates along the alternating component
vertices of the preceding critical path. -/
theorem three_shift_attachment_along_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (q : BackwardShift (h := h) p) (r : BackwardShift (h := h) q.path)
    (t : BackwardShift (h := h) r.path)
    (hr : OrbitPrefix (h := h) r.path (replacementDistance h d))
    (hnorm : ¬ Z d.radical (q.path.walk.getVert (q.path.walk.length-2)) ≤ normalizer
      (((Z d.radical t.start ⊓ Q d.radical (r.path.walk.getVert (r.path.walk.length-2))) ⊔
        Z d.radical r.start : Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) :
    let z := q.path.walk.getVert (q.path.walk.length-2)
    let v := r.path.walk.getVert (r.path.walk.length-2)
    let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
    let D := ⁅Z d.radical t.start,Z d.radical v⁆
    let I := (H ⊔ D) ⊓ Z d.radical t.edge
    H = D ∨ (Nat.card I = 2 ∧
      ∀ i, 4*i+2 ≤ r.path.walk.length → I = U d.radical (r.path.walk.getVert (4*i+2)) ⊓
        centralizer (stabilizer d.radical (r.path.walk.getVert (4*i+2)) :
          Set (FreeAmalgam d.radical))) := by
  have ha := SylowTerminalIntersection.three_shift_nonnormalized_central_alternative_knownSimple
    hb hcard p q r t hnorm
  rcases ha.2.2 with he | he
  · exact Or.inl he
  · have hc := three_shift_kernel_central_along_path_knownSimple hb hcard p q r t hr
    have hr2 : r.path.walk.getVert 2 = q.start := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using r.overlap 0 (Nat.zero_le _)
    exact Or.inr ⟨he.2.2,attachment_along_orbit_path r.path hr _ hc.1 (by
      simpa only [hr2] using he.2.1)⟩

/-- The literal original radical starts a finite generating shift chain.
At its final three shifts the central factor is fixed along the entire
preceding path; its exact index and nonnormalizing attachment alternative
retain both covers. All orbit-prefix premises are constructed here. -/
theorem original_radical_terminal_path_knownSimple
    (hb : 4 < replacementDistance h d)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hfirst : p.walk.getVert 1 = beta d.radical) :
    let T := ((R.subgroupOf (L ⊔ R)).subgroupOf d.overgroup).map (embedM d.radical)
    ∃ q₀ : BackwardShift (h := h) p,
      act d.radical q₀.transporter (beta d.radical) = q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom = Q d.radical q₀.edge ∧
      T.map (MulAut.conj q₀.transporter⁻¹).toMonoidHom ⊔ Z d.radical a' =
        stabilizer d.radical (alpha d.radical) ∧
      ∃ c c', ∃ v₀ : CriticalPath d.radical (replacementGeometry h d) c c',
      ShiftChain (h := h) q₀.path v₀ (replacementDistance h d) ∧
      ∃ (q : BackwardShift (h := h) v₀) (r : BackwardShift (h := h) q.path)
        (t : BackwardShift (h := h) r.path),
      OrbitPrefix (h := h) r.path (replacementDistance h d) ∧
      let z := q.path.walk.getVert (q.path.walk.length-2)
      let v := r.path.walk.getVert (r.path.walk.length-2)
      let H := ⁅Z d.radical t.start ⊓ Q d.radical v,Z d.radical z ⊓ Q d.radical r.start⁆
      let D := ⁅Z d.radical t.start,Z d.radical v⁆
      let I := (H ⊔ D) ⊓ Z d.radical t.edge
      H ⊔ D = D ⊔ I ∧ D ⊓ I = ⊥ ∧ I.relIndex (H ⊔ D) = 2 ∧
      I ≤ centralizer (stabilizer d.radical t.start : Set (FreeAmalgam d.radical)) ∧
      I ≤ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical)) ∧
      (∀ i, 2*i ≤ r.path.walk.length → I ≤ centralizer
        (stabilizer d.radical (r.path.walk.getVert (2*i)) : Set (FreeAmalgam d.radical))) ∧
      ((¬ Z d.radical z ≤ normalizer
        (((Z d.radical t.start ⊓ Q d.radical v) ⊔ Z d.radical r.start :
          Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical))) →
        H = D ∨ (Nat.card I = 2 ∧
          ∀ i, 4*i+2 ≤ r.path.walk.length → I = U d.radical (r.path.walk.getVert (4*i+2)) ⊓
            centralizer (stabilizer d.radical (r.path.walk.getVert (4*i+2)) :
              Set (FreeAmalgam d.radical)))) := by
  obtain ⟨q₀,hqe,hqT,hqgen⟩ := SylowShiftChain.original_radical_backward_shift_knownSimple
    hb hcard p hfirst
  obtain ⟨c,c',v₀,hchain,hprefix⟩ := exists_orbitPrefix_chain_knownSimple hb hcard q₀.path
    (replacementDistance h d)
  obtain ⟨q,_⟩ := SylowShiftChain.backwardShift_with_edge hb hcard v₀
  obtain ⟨r,_⟩ := SylowShiftChain.backwardShift_with_edge hb hcard q.path
  obtain ⟨t,_⟩ := SylowShiftChain.backwardShift_with_edge hb hcard r.path
  have hr := full_prefix_shift hb q.path r (full_prefix_shift hb v₀ q hprefix)
  have hc := SylowTerminalIntersection.three_shift_kernel_central_decomposition_knownSimple
    hb hcard v₀ q r t
  have hf := SylowTerminalIntersection.three_shift_kernel_central_factor_knownSimple
    hb hcard v₀ q r t
  have hp := three_shift_kernel_central_along_path_knownSimple hb hcard v₀ q r t hr
  exact ⟨q₀,hqe,hqT,hqgen,c,c',v₀,hchain,q,r,t,hr,hc.2.2.2.2.2.1,hf.2.1,hf.2.2,
    hc.2.2.2.1,hp.2,hp.1,three_shift_attachment_along_path_knownSimple hb hcard v₀ q r t hr⟩


end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.SylowTerminalPath
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
