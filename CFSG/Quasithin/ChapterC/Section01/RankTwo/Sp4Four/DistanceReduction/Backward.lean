module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.CriticalPairs
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.LocalGroups
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Rigidity.Moving
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.RadiusCentrality
public import Theory.GroupTheory.NormalizedSupConsequences

/-!
# The chosen backward seeds in the nonbinary symplectic argument

These deductions use the original holomorph amalgam and its right action.
A local conjugator preserves the exact moving index modulo B. The common
edge bounds the size of the joined seed modulo Z. A generating pair that
normalizes this join then puts the backward seed in B, once the earlier
small normal-section action lemma is supplied. A radius-intersection
commutator bound therefore forces a genuine backward critical path, with
its actual two-edge overlap retained.

The local representation assertions remain explicit: no abelian edge
quotient, splitting of the central layer, or binary natural module is used.
These are the normalization and displacement branches of MS93 (5.7),
printed p.919. The exceptional nonnormalizing branch still uses (3.3).
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M}
  (geometry : Geometry R)

/-- The exact relative moving index survives every local source conjugator. -/
theorem movingIndex_act (hb : 2 < geometry.b R) {a d : Vertex R}
    (ha : color R a = false) (x : FreeAmalgam R) (hx : x ∈ stabilizer R a) :
    (B R a (geometry.Z_normal a)).relIndex (U R (act R x d)) =
      (B R a (geometry.Z_normal a)).relIndex (U R d) := by
  have hB : (B R a (geometry.Z_normal a)).map (MulAut.conj x⁻¹).toMonoidHom =
      B R a (geometry.Z_normal a) :=
    mem_normalizer_iff_map_conj_eq.mp
      (Escape.Propagation.Rigidity.B_normalized (geometry := geometry) hb a ha
        ((stabilizer R a).inv_mem hx))
  rw [U_act]
  conv_lhs => rw [← hB]
  exact relIndex_map_map_of_injective (f := (MulAut.conj x⁻¹).toMonoidHom)
    _ _ (MulAut.conj x⁻¹).injective

omit [Finite M] in
/-- Both original-group vertices over an edge are within radius two. -/
theorem neighbor_distance_le_two {a d t : Vertex R}
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    (cosetGraph R).dist d a ≤ 2 := by
  have hdt' := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdt)
  have hta' := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat))
  have htri := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := a)
  omega

omit [Finite M] in
/-- The backward seed and the starting seed lie in the literal radius group. -/
theorem neighbor_seed_join_le_radius {a d t : Vertex R}
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    Z R d ⊔ Z R a ≤ V R a :=
  sup_le (le_iSup_of_le d (le_iSup_of_le (neighbor_distance_le_two hat hdt) le_rfl))
    (Z_le_VBall R a 2)

/-- The common edge seed bounds the joined seed, with no fixed-layer split. -/
theorem neighbor_seed_join_index_le (hb : 0 < geometry.b R)
    {a d t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    (Z R a).relIndex (Z R d ⊔ Z R a) ≤ (Z R t).relIndex (Z R d) := by
  let := finite_Z R d
  let := finite_Z R a
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases hc : color R t <;> simp_all
  have hZaQ : Z R a ≤ Q R a :=
    (geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])).trans
      (omegaCenter_le _)
  have hn : Z R a ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    ((hZaQ.trans (Q_le_adjacent_h R ht hat)).trans
      (fun _ hx => hx.2 d (adjacent_symm R hdt))).trans (Z_normalized R d)
  rw [relIndex_sup_of_normalizes _ _ hn]
  exact relIndex_le_of_le_left (adjacent_Z_le R ha hat) index_ne_zero_of_finite

omit [Finite M] in
/-- The local edge normalizes the joined seeds at its two neighbors. -/
theorem edge_normalizes_neighbor_seed_join {a d t : Vertex R}
    (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    Q R t ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  apply le_trans (le_inf _ _) (normalizer_inf_normalizer_le_normalizer_sup _ _)
  · exact (show Q R t ≤ stabilizer R d from
      fun _ hx => hx.2 d (adjacent_symm R hdt)).trans (Z_normalized R d)
  · exact (show Q R t ≤ stabilizer R a from
      fun _ hx => hx.2 a (adjacent_symm R hat)).trans (Z_normalized R a)

omit [Finite M] in
/-- The original fixed preimage contains a radius subgroup precisely when
its residual action is trivial modulo the original Z-layer. -/
theorem radius_le_B_of_commutator (hb : 2 < geometry.b R)
    {a : Vertex R} (ha : color R a = false) (H : Subgroup (FreeAmalgam R))
    (hH : H ≤ V R a) (hcomm : ⁅H,Ltilde R a⁆ ≤ Z R a) :
    H ≤ B R a (geometry.Z_normal a) := by
  have hV := geometry.V_local a ha (by rwa [geometry.distance_constant a ha])
  intro x hx
  apply (mem_B_iff R a (geometry.Z_normal a) hV x).mpr
  refine ⟨hH hx, fun l hl => ?_⟩
  apply hcomm
  rw [commutator_comm]
  exact commutator_mem_commutator hl hx

/-- Source generation and the small local section action put a normalized
backward seed in B. The section-action premise belongs to the local module
calculation and contains no assertion about critical paths. -/
theorem neighbor_seed_le_B_of_normalized_join
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (n : ℕ) (hindex : (Z R t).relIndex (Z R d) ≤ n)
    (hsmall : ∀ H : Subgroup (FreeAmalgam R), H ≤ V R a →
      stabilizer R a ≤ normalizer (H : Set _) → (Z R a).relIndex H ≤ n →
      ⁅H,Ltilde R a⁆ ≤ Z R a)
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e)
    (hn : Z R e ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) :
    Z R d ≤ B R a (geometry.Z_normal a) := by
  have hnorm : stabilizer R a ≤
      normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
    hgen.trans (sup_le (edge_normalizes_neighbor_seed_join hat hdt) hn)
  have hi := (neighbor_seed_join_index_le geometry (by omega) ha hat hdt).trans hindex
  exact le_sup_left.trans (radius_le_B_of_commutator geometry hb ha _
    (neighbor_seed_join_le_radius hat hdt)
    (hsmall _ (neighbor_seed_join_le_radius hat hdt) hnorm hi))

private theorem normalizes_join_of_commutator_le {G : Type*} [Group G]
    (A D Z : Subgroup G) (hAZ : A ≤ normalizer (Z : Set G))
    (hAD : ⁅A,D⁆ ≤ Z) : A ≤ normalizer ((D ⊔ Z : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha d hd
  have hm : (D ⊔ Z).map (MulAut.conj a).toMonoidHom ≤ D ⊔ Z := by
    rw [Subgroup.map_sup]
    apply sup_le
    · rintro _ ⟨x,hx,rfl⟩
      have hc := hAD (commutator_mem_commutator ha hx)
      change a*x*a⁻¹ ∈ D ⊔ Z
      rw [show a*x*a⁻¹ = ⁅a,x⁆*x by simp [commutatorElement_def,mul_assoc]]
      exact mul_mem (mem_sup_right hc) (mem_sup_left hx)
    · rw [MulEquiv.toMonoidHom_eq_coe,mem_normalizer_iff_map_conj_eq.mp (hAZ ha)]
      exact le_sup_right
  exact hm (mem_map_of_mem (MulAut.conj a).toMonoidHom hd)

/-- A nonzero moving index contradicts normalization of its conjugated seed. -/
theorem conjugate_seed_join_not_normalized
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (ha : color R a = false) (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hat : Adjacent R a t) (hdt : Adjacent R (act R x d) t)
    (n : ℕ) (hindex : (Z R t).relIndex (Z R (act R x d)) ≤ n)
    (hsmall : ∀ H : Subgroup (FreeAmalgam R), H ≤ V R a →
      stabilizer R a ≤ normalizer (H : Set _) → (Z R a).relIndex H ≤ n →
      ⁅H,Ltilde R a⁆ ≤ Z R a)
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e)
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d)) :
    ¬ Z R e ≤ normalizer
      ((Z R (act R x d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
  intro hn
  have hU : U R (act R x d) ≤ B R a (geometry.Z_normal a) :=
    (U_le_Z _).trans (neighbor_seed_le_B_of_normalized_join geometry hb ha hat hdt
      n hindex hsmall hgen hn)
  have hi := relIndex_eq_one.mpr hU
  rw [movingIndex_act geometry hb ha x hx] at hi
  omega

/-- The radius-displacement branch of (5.7) produces noncontainment of the
chosen seed, using the literal source generator and conjugator. -/
theorem backward_seed_not_le_of_radius_displacement
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (p : CriticalPath R geometry a e)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hat : Adjacent R a t) (hdt : Adjacent R (act R x d) t)
    (n : ℕ) (hindex : (Z R t).relIndex (Z R (act R x d)) ≤ n)
    (hsmall : ∀ H : Subgroup (FreeAmalgam R), H ≤ V R a →
      stabilizer R a ≤ normalizer (H : Set _) → (Z R a).relIndex H ≤ n →
      ⁅H,Ltilde R a⁆ ≤ Z R a)
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e)
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d))
    (hdisp : ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R a) :
    ¬ Z R (act R x d) ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  apply conjugate_seed_join_not_normalized geometry hb p.start_color x hx hat hdt
    n hindex hsmall hgen hmove
  apply normalizes_join_of_commutator_le
  · exact (p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a)
  · rw [commutator_comm]
    exact (commutator_mono (le_inf
      (le_sup_left.trans (neighbor_seed_join_le_radius hat hdt)) hbad) le_rfl).trans hdisp

omit [Finite M] in
/-- The selected noncontainment gives a shortest backward critical path,
with the common edge and every overlapping vertex identified. -/
theorem exists_backward_path_of_not_le
    (hb : 2 ≤ geometry.b R) {a d t e : Vertex R}
    (p : CriticalPath R geometry a e)
    (hat : Adjacent R a t) (hdt : Adjacent R d t)
    (hn : ¬ Z R d ≤ Q R (p.walk.getVert (p.walk.length-2))) :
    ∃ q : CriticalPath R geometry d (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧
      ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i := by
  have hd : color R d = false := by
    have h₁ := adjacent_color_ne R hat
    have h₂ := adjacent_color_ne R hdt
    rw [p.start_color] at h₁
    cases hc : color R t <;> cases hd : color R d <;> simp_all
  let w : (cosetGraph R).Walk d a :=
    .cons ((cosetGraph_adj R _ _).mpr hdt)
      (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hat)) .nil)
  refine ⟨p.prepend_two hb hd w rfl hn, ?_, ?_⟩
  · change ((w.append (p.walk.take (p.walk.length-2))).getVert 1) = t
    rfl
  · intro i hi
    exact p.prepend_two_overlap hb hd w rfl hn hi

/-- Actual consumer application: the local displacement calculation supplies
both the critical backward path and escape of the full original radius. -/
theorem backward_path_of_radius_displacement
    (hb : 2 < geometry.b R) {a d t e : Vertex R}
    (p : CriticalPath R geometry a e)
    (x : FreeAmalgam R) (hx : x ∈ stabilizer R a)
    (hat : Adjacent R a t) (hdt : Adjacent R (act R x d) t)
    (n : ℕ) (hindex : (Z R t).relIndex (Z R (act R x d)) ≤ n)
    (hsmall : ∀ H : Subgroup (FreeAmalgam R), H ≤ V R a →
      stabilizer R a ≤ normalizer (H : Set _) → (Z R a).relIndex H ≤ n →
      ⁅H,Ltilde R a⁆ ≤ Z R a)
    (hgen : stabilizer R a ≤ Q R t ⊔ Z R e)
    (hmove : 1 < (B R a (geometry.Z_normal a)).relIndex (U R d))
    (hdisp : ⁅V R a ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R a) :
    (∃ q : CriticalPath R geometry (act R x d) (p.walk.getVert (p.walk.length-2)),
      q.walk.getVert 1 = t ∧
      ∀ i ≤ p.walk.length-2, q.walk.getVert (i+2) = p.walk.getVert i) ∧
      ¬ V R a ≤ Q R (p.walk.getVert (p.walk.length-2)) := by
  have hn := backward_seed_not_le_of_radius_displacement geometry hb p x hx hat hdt
    n hindex hsmall hgen hmove hdisp
  exact ⟨exists_backward_path_of_not_le geometry (by omega) p hat hdt hn,
    fun h => hn ((le_sup_left.trans (neighbor_seed_join_le_radius hat hdt)).trans h)⟩

end CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
