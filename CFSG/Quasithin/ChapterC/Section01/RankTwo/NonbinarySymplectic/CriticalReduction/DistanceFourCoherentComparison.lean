module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCentralObstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedOriginalFixedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SelectedNontrapping

/-!
# Coherent two-step paths retaining the literal comparison

The strict equal-mover branch uses one original maximizing-plane selector.
Its two members retain both original-versus-selected full-Z fixed identities.
The joined-commutator calculation excludes simultaneous trapping, giving an
actual first path from this same pair. Its full root commutator is fixed at
the original source, which excludes trapping of the actual second selector.

The same raw second selector is chosen before proving its nontrapping and
its literal source comparison. Its movement and marked-plane fixer data are
retained together; no existential selector is replaced between the proofs.

The final reduction splits the local neighboring index bound. A uniform
bound supplies the first path for the previously constructed exact selector;
a strict equal-mover witness uses the new construction. A strict witness
with unequal mover is retained explicitly, with its actual neighboring
vertex. No equality of movers is transported to an unrelated neighbor.
Source: MS93 (5.7)--(5.8), pp.919--920, and (5.12), p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

/-- Two actual backward paths and comparison (1) on their same selected
second source, with the first pair's exact selectors and the second residual orbit. -/
@[expose] def distanceFourCoherentComparison {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {a z : Vertex R}
    (path : CriticalPath R geometry a z) (c t : Vertex R) (q : ℕ) : Prop :=
  ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
    let c₁ := act R g⁻¹ c
    let t₁ := act R g⁻¹ t
    ∃ u w, (u=c₁ ∧ w=t₁ ∨ u=act R x c₁ ∧ w=act R x t₁) ∧
      Adjacent R a w ∧ Adjacent R u w ∧
      ∃ back : CriticalPath R geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ∃ v s, ∃ y ∈ Ltilde R u,
          act R y a=v ∧ act R y (back.walk.getVert 1)=s ∧
          Adjacent R u s ∧ Adjacent R v s ∧
          ¬ Z R (path.walk.getVert 2) ≤ normalizer
            ((Z R v ⊔ Z R u : Subgroup (FreeAmalgam R)) : Set _) ∧
          ∃ x₂ ∈ Ltilde R u,
          ((Subgroup.SmallMover.join (U R v) (Q R v) (Q R s) (q^2) ⊔
            Z R (path.walk.getVert 2)) ⊔
              (Z R (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom = stabilizer R u) ∧
          ⁅U R v ⊓ Q R z,Z R (path.walk.getVert 2)⁆ ≤
            ⁅Z R u,Z R (path.walk.getVert 2)⁆ ⊔
              ⁅U R v ⊓ Q R z,X R (path.walk.getVert 2) ⊓ Q R u⁆ ∧
          ∃ next : CriticalPath R geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i

private theorem mover_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
        (Q R (act R y t)) q =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R t) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
      (Q R (act R y t)) q : Set (FreeAmalgam R))).relIndex (U R (act R y v)) =
      (centralizer (Subgroup.SmallMover.join (U R v) (Q R v)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R v) := by
  rw [mover_act,U_act,Subgroup.SmallMover.centralizer_index_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_neighbors {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) {a t c : Vertex R} (hat : Adjacent R a t) (hct : Adjacent R c t) :
    (centralizer (Subgroup.SmallMover.join (U R c) (Q R c)
      (Q R t) q : Set (FreeAmalgam R))).relIndex (U R c) =
      (centralizer (Subgroup.SmallMover.join (U R a) (Q R a)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R a) := by
  obtain ⟨y,hy,hya⟩ := stabilizer_transitive_neighbors R t
    (adjacent_symm R hat) (adjacent_symm R hct)
  have hyt : act R y t=t := hy
  simpa only [hya,hyt] using own_index_act q y a t

private theorem global_neighbor_bound_of_edge
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t) (q : ℕ)
    (hbound : ∀ c, Adjacent R c t → (B R a (geometry.Z_normal a)).relIndex (U R c) ≤ q)
    {v w c : Vertex R} (hv : color R v=false)
    (hvw : Adjacent R v w) (hcw : Adjacent R c w) :
    (B R v (geometry.Z_normal v)).relIndex (U R c) ≤ q := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color R hv
  obtain ⟨j,hj⟩ := exists_mVertex_of_color R ha
  let y := g⁻¹*j
  have hy : act R y v=a := by
    rw [hg,act_mVertex]
    dsimp [y]
    rw [mul_inv_cancel_left,←hj]
  have had : Adjacent R a (act R y w) := by
    rw [←hy]
    exact (adjacent_act_iff R y _ _).mpr hvw
  obtain ⟨x,hx,hxt⟩ := stabilizer_transitive_neighbors R a had hat
  have hc : Adjacent R (act R x (act R y c)) t := by
    rw [←hxt]
    exact (adjacent_act_iff R x _ _).mpr ((adjacent_act_iff R y _ _).mpr hcw)
  have hi := hbound _ hc
  rw [movingIndex_act geometry hb ha x hx] at hi
  rw [←hy,Escape.PairingControl.FirstPairing.B_act hb y v hv,U_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective] at hi
  exact hi


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem second_selector_not_trapped
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hn : ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hCa : ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hmove : ¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))) :
    ¬ Z d.radical v ≤ Q d.radical (back.walk.getVert (back.walk.length-2)) := by
  intro htrap
  let e := path.walk.getVert 2
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅Z d.radical v,A⁆
  let T := ⁅Z d.radical u,Z d.radical e⁆
  let C := U d.radical u ⊓ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical t) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hv : color d.radical v=false := by rw [←hya,action_preserves_color]; exact path.start_color
  obtain ⟨hDU,hDcard,hDUindex,hDZindex,hDsource,_⟩ :=
    h.replacement_trapped_root_exact_indices d back hb4 hut hvt hn htrap
  change D=⁅U d.radical v,A⁆ at hDU
  change Nat.card D=Nat.card F at hDcard
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hDZ : D ≤ Z d.radical v :=
    le_normalizer_iff_commutator_le_left.mp (hAS.trans (Z_normalized d.radical v))
  have hDT : D ≤ T := by
    change ⁅Z d.radical v,X d.radical e ⊓ Q d.radical u⁆ ≤ T
    rw [hDsource]
    have hh := h.replacement_trapped_root_commutator_le_critical d back hb4 hut hvt hn htrap
    exact hh.trans (commutator_mono le_rfl (U_le_Z e))
  let Cv := stabilizer d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  let := finite_Z d.radical v
  let : Finite D := Finite.of_injective (inclusion hDZ) (inclusion_injective _)
  have hDidx : Cv.relIndex D=Nat.card D := by
    have hh := h.replacement_displacement_central_index d geometry hb4 hv A hAS
    rw [commutator_comm] at hh
    exact hh.trans (hDZindex.trans hDcard.symm)
  have hdisv : Disjoint D Cv := by
    have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (D ⊓ Cv) D
      bot_le inf_le_left
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hDidx] at hm
    apply disjoint_iff.mpr
    apply card_eq_one.mp
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D))
    simpa only [one_mul] using hm
  have hIcent : D ⊓ C ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    let I := D ⊓ C
    have hIa : I ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans hDT).trans hCa
    have hIu : I ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) :=
      inf_le_right.trans inf_le_right
    have hIg : I.map (MulAut.conj y⁻¹).toMonoidHom=I :=
      mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
        (le_centralizer_iff.mp hIu ((stabilizer d.radical u).inv_mem hy)))
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hIa).trans
      (map_centralizer_le_centralizer_image _ _)
    change I.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hIg,←stabilizer_act,hya] at hh
  have hdis : Disjoint D C := by
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    exact (le_inf inf_le_left (le_inf
      (inf_le_left.trans (hDZ.trans (Z_le_stabilizer d.radical v))) hIcent)).trans hdisv.le_bot
  have hCT : C ≤ T :=
    (inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer u))).trans
      (le_sup_left.trans (h.replacement_critical_commutator_contains_fixed_kernels d back (by omega)))
  have hTZ : T ≤ Z d.radical u := critical_commutator_le_start_seed back
  let := finite_Z d.radical u
  let : Finite T := Finite.of_injective (inclusion hTZ) (inclusion_injective _)
  have hroot : (Q d.radical e).relIndex (Z d.radical u)=Nat.card F := by
    have hYS : Z d.radical v ≤ stabilizer d.radical e :=
      (le_inf (le_sup_left.trans (neighbor_seed_join_le_radius hut hvt)) htrap).trans
        (truncated_radius_le_endpoint_stabilizer back (by omega))
    exact (h.replacement_critical_indices_eq_field_of_seed_escape d back (by omega)
      (Z d.radical v) hYS
      ((le_sup_left.trans (neighbor_seed_join_le_radius hut hvt)).trans
        (geometry.V_le_Q (by omega) u back.start_color)) hn).1
  have hTcard : Nat.card T=Nat.card F*Nat.card C := by
    have hh := h.replacement_critical_commutator_card d back hb4
    rwa [hroot] at hh
  have hCD : C ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le (hDT.trans (hTZ.trans (Z_le_stabilizer d.radical u))))
  have hsplit : D ⊔ C=T := eq_of_le_of_card_ge (sup_le hDT hCT) (by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint D C
      (hCD.trans (Subgroup.centralizer_le_normalizer _)) hdis,hDcard,hTcard])
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hut
    rw [back.start_color] at hh
    cases hcol : color d.radical t <;> simp_all
  have hAT : A ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hut)
  have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    rw [hDU]
    exact h.replacement_small_mover_join_centralizes_field_displacement d geometry hb4
      hv hvt A hAT hDUindex.le
  have hJS : J ≤ stabilizer d.radical u := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 u (adjacent_symm _ hut))
  have hTJ : T ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    rw [←hsplit]
    exact sup_le hDJ (inf_le_right.trans (centralizer_le hJS))
  apply hmove
  have hwhole := h.replacement_Z_commutator_eq_U d geometry hb4 back.start_color
    (Z d.radical e) (back.endpoint_Z_le_start_stabilizer (by omega))
  rw [commutator_comm,←hwhole]
  exact hTJ


omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh


private theorem trapped_pair_impossible
    {geometry : Geometry d.radical} {a z t v r w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (har : Adjacent d.radical a r) (hwr : Adjacent d.radical w r)
    (x : FreeAmalgam d.radical) (hx : x ∈ stabilizer d.radical a)
    (hxv : act d.radical x v=w)
    (hcommv : ⁅Z d.radical v,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t)
        (Nat.card F^2) : Set (FreeAmalgam d.radical)))
    (hcommw : ⁅Z d.radical w,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical w) (Q d.radical w) (Q d.radical r)
        (Nat.card F^2) : Set (FreeAmalgam d.radical)))
    (hfixed : (Z d.radical a ⊓ centralizer (Subgroup.SmallMover.join (U d.radical v)
        (Q d.radical v) (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
      centralizer (Subgroup.SmallMover.join (U d.radical w) (Q d.radical w)
        (Q d.radical r) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hgen : (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical t) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        (Z d.radical z).map (MulAut.conj x).toMonoidHom = stabilizer d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v))
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (htrapw : Z d.radical w ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) : False := by
  let A := X d.radical z ⊓ Q d.radical a
  have hV : Z d.radical v ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hat hvt)
  have hS := (le_inf hV htrap).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hi := (h.replacement_critical_indices_eq_field_of_seed_escape d path (by omega)
    (Z d.radical v) hS (hV.trans (geometry.V_le_Q (by omega) a path.start_color)) hn).2
  have hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    rw [hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨he,_,halt⟩ := h.replacement_equal_trapped_commutators d path hb
    hat hvt har hwr (hcommv.trans inf_le_left) (hcommw.trans inf_le_left) hn htrap htrapw
  have hcommon : ⁅Z d.radical w,A⁆=⊥ ∨ (⁅Z d.radical w,A⁆=⁅Z d.radical v,A⁆ ∧
      ⁅Z d.radical v,A⁆ ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
    rcases halt with hz | hw
    · exact Or.inl hz
    · have heq : ⁅Z d.radical w,A⁆=⁅Z d.radical v,A⁆ := hw.trans he.symm
      refine Or.inr ⟨heq,?_⟩
      have hv := (commutator_mono le_rfl (show A ≤ Q d.radical a from inf_le_right)).trans hcommv
      have hw := (commutator_mono le_rfl (show A ≤ Q d.radical a from inf_le_right)).trans hcommw
      have hh := le_inf hv (heq.ge.trans (hw.trans inf_le_right))
      exact (hh.trans_eq hfixed).trans inf_le_right
  exact h.replacement_equal_root_trapped_excluded d path hb hat hvt x hx hsmall hn hgen
    hmove (by simpa only [hxv] using hcommon) ⟨htrap,by simpa only [hxv] using htrapw⟩


private theorem root_second_selector
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hequal : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2))
    (hsmall : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2) :
    ∃ g ∈ Ltilde d.radical u, ∃ x ∈ Ltilde d.radical u,
      let t₁ := act d.radical g⁻¹ (back.walk.getVert 1)
      let c₁ := act d.radical g⁻¹ a
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v=c₁ ∧ w=t₁ ∨ v=c₂ ∧ w=t₂) ∧
        Adjacent d.radical u w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ next : CriticalPath d.radical geometry v (back.walk.getVert (back.walk.length-2)),
          next.walk.getVert 1=w ∧
          ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i) ∨
        (Z d.radical v ≤ Q d.radical (back.walk.getVert (back.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical (path.walk.getVert 2) ⊓ Q d.radical u) ∧
          X d.radical (path.walk.getVert 2) ⊓ Q d.radical u ≤
            normalizer (Z d.radical v : Set _) ∧
          ⁅⁅X d.radical (path.walk.getVert 2) ⊓ Q d.radical u,Z d.radical v⁆,
            Z d.radical v⁆=⊥)) ∧
        (¬ ⁅Z d.radical (path.walk.getVert 2),U d.radical u⁆ ≤ centralizer
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
            (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ∧
        (∃ x₂ ∈ Ltilde d.radical u,
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
            (Z d.radical (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom =
              stabilizer d.radical u) ∧
        (¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
          ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
            ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ →
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤
            centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))) := by
  let e := path.walk.getVert 2
  let t := back.walk.getVert 1
  let J := Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
    (Q d.radical t) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hut : Adjacent d.radical u t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 0<back.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hat : Adjacent d.radical a t := by
    rw [←hmid]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 1<back.walk.length)))
  have hnormal : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 back.start_color hut
  have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 back.start_color hut B hB f hfQ hTf hindex hmax hJm
  let D := ((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
    (stabilizer d.radical u).subtype)
  obtain ⟨g,hg,x,hx,hu₁,hc₁,hu₂,hc₂,hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,
      v,hv,w,hwhich,huw,hvw,hn,hnext⟩ :=
    h.replacement_equal_smaller_selected_root_alternative d back hb4 hut rfl hat
      hnormal hequal hsmall B hB f hf hfQ hTf hindex hquad hJplane
  let t₁ := act d.radical g⁻¹ t
  let c₁ := act d.radical g⁻¹ a
  let t₂ := act d.radical x t₁
  let c₂ := act d.radical x c₁
  let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
    (Q d.radical t₁) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
    (Q d.radical t₂) (Nat.card F^2)
  have hJD : J ≤ D := by
    have hh := map_mono (f := (stabilizer d.radical u).subtype) hJplane
    rwa [map_subgroupOf_eq_of_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
      (show Q d.radical t ≤ stabilizer d.radical u from fun _ hy => hy.2 u (adjacent_symm _ hut)))] at hh
  have heJ : Z d.radical e ≤ J := h.replacement_root_endpoint_le_small_mover d back hb4
    hut rfl hsmall B hB f hf hTf hindex hJplane
  have heD : Z d.radical e ≤ D := heJ.trans hJD
  have hfixD : Z d.radical u ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
      Z d.radical u ⊓ centralizer (D : Set (FreeAmalgam d.radical)) :=
    h.replacement_small_mover_parabolic_full_fixed d geometry hb4 back.start_color hut
      B hB f hf hfQ hindex hJplane
  have hRfixed : ⁅Z d.radical u,Z d.radical e⁆ ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hsmall
  have hQJ : Q d.radical u ≤ J := core_le_mover h d back.start_color hut
  have hbase : ⁅Z d.radical a,J⁆ ≤ omegaCenter J :=
    (h.replacement_equal_root_neighbor_commutator d back hb4 hut hat hsmall hJm hequal).2
  have hgS : g ∈ stabilizer d.radical u := Ltilde_le_stabilizer u hg
  have hxS : x ∈ stabilizer d.radical u := Ltilde_le_stabilizer u hx
  have hJ₁ : J₁=J.map (MulAut.conj g).toMonoidHom := by
    dsimp only [J₁,c₁,t₁]
    rw [mover_act,inv_inv,hequal]
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := by
    dsimp only [J₂,c₂,t₂]
    exact mover_act _ _ _ _
  have hQJ₁ : Q d.radical u ≤ J₁ := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hQJ
    have hQg : (Q d.radical u).map (MulAut.conj g).toMonoidHom=Q d.radical u :=
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical u hgS)
    rw [hQg,←hJ₁] at hh
    exact hh
  have hQJ₂ : Q d.radical u ≤ J₂ := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hQJ₁
    have hQx : (Q d.radical u).map (MulAut.conj x⁻¹).toMonoidHom=Q d.radical u :=
      mem_normalizer_iff_map_conj_eq.mp
        (Q_normalized d.radical u ((stabilizer d.radical u).inv_mem hxS))
    rw [hQx,←hJ₂] at hh
    exact hh
  have hcomm₁ : ⁅Z d.radical c₁,J₁⁆ ≤ omegaCenter J₁ := by
    have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hbase
    rw [map_commutator,←omegaCenter_map _ _ (MulAut.conj g).injective,←hJ₁] at hh
    simpa only [c₁,Z_act,inv_inv] using hh
  have hcomm₂ : ⁅Z d.radical c₂,J₂⁆ ≤ omegaCenter J₂ := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hcomm₁
    rw [map_commutator,←omegaCenter_map _ _ (MulAut.conj x⁻¹).injective,←hJ₂] at hh
    simpa only [c₂,Z_act] using hh
  have finish (v w : Vertex d.radical) (Jv : Subgroup (FreeAmalgam d.radical))
      (huw : Adjacent d.radical u w) (hvw : Adjacent d.radical v w)
      (hQJv : Q d.radical u ≤ Jv) (hcomm : ⁅Z d.radical v,Jv⁆ ≤ omegaCenter Jv)
      (y : FreeAmalgam d.radical) (hy : y ∈ normalizer (D : Set (FreeAmalgam d.radical)))
      (hgen : (Jv ⊔ Z d.radical e) ⊔ (Z d.radical e).map (MulAut.conj y).toMonoidHom =
        stabilizer d.radical u)
      (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical e⁆ ≤
        ⁅Z d.radical u,Z d.radical e⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical e ⊓ Q d.radical u⁆) :
      ⁅U d.radical v ⊓ Q d.radical z,X d.radical e ⊓ Q d.radical u⁆ ≤
        centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) := by
    let R₁ := ⁅U d.radical v ⊓ Q d.radical z,X d.radical e ⊓ Q d.radical u⁆
    have hbound : R₁ ≤ ⁅Z d.radical u,Z d.radical e⁆ :=
      (h.replacement_distance_four_root_comparison_of_failure d path hb back huw hvw hbad).1
    have hRZu : R₁ ≤ Z d.radical u := hbound.trans (critical_commutator_le_start_seed back)
    have hRD : R₁ ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
      ((le_inf hRZu (hbound.trans hRfixed)).trans hfixD.le).trans inf_le_right
    have hRJv : R₁ ≤ centralizer (Jv : Set (FreeAmalgam d.radical)) := by
      apply ((commutator_mono (inf_le_left.trans (U_le_Z v))
        (inf_le_right.trans hQJv)).trans hcomm).trans
      intro y hy
      exact (mem_omegaCenter_iff.mp hy).2.2
    have hRZe : R₁ ≤ Z d.radical e := hbound.trans (critical_commutator_le_endpoint_seed back)
    let := geometry.Z_elementary (by omega) e back.end_color
    have hRZ : R₁ ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
      hRZe.trans (Z d.radical e).le_centralizer
    have heDy : (Z d.radical e).map (MulAut.conj y).toMonoidHom ≤ D := by
      exact (map_mono heD).trans_eq (mem_normalizer_iff_map_conj_eq.mp hy)
    have hRZy := hRD.trans (centralizer_le heDy)
    rw [←hgen]
    intro r hr
    have hj : Jv ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun s hs => mem_centralizer_singleton_iff.mpr (hRJv hr s hs)
    have hz : Z d.radical e ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun s hs => mem_centralizer_singleton_iff.mpr (hRZ hr s hs)
    have hzy : (Z d.radical e).map (MulAut.conj y).toMonoidHom ≤
        centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun s hs => mem_centralizer_singleton_iff.mpr (hRZy hr s hs)
    intro s hs
    exact mem_centralizer_singleton_iff.mp ((sup_le (sup_le hj hz) hzy) hs)
  refine ⟨g,hg,x,hx,v,hv,w,hwhich,huw,hvw,hn,hnext,?_,?_,?_⟩
  · rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hmove₁
    · exact hmove₂
  · rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨x,hx,hgen₁⟩
    · exact ⟨x⁻¹,(Ltilde d.radical u).inv_mem hx,hgen₂⟩
  · rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact finish c₁ t₁ J₁ hu₁ hc₁ hQJ₁ hcomm₁ x hxn hgen₁
    · have hxN : x ∈ normalizer (D : Set (FreeAmalgam d.radical)) := hxn
      exact finish c₂ t₂ J₂ hu₂ hc₂ hQJ₂ hcomm₂ x⁻¹
        ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxN) hgen₂


private theorem second_path_of_full_root_centrality
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hbackequal : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2))
    (hbackindex : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2)
    (hCa : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ v s, ∃ y ∈ Ltilde d.radical u,
      act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
      Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
      ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ x₂ ∈ Ltilde d.radical u,
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
        (Z d.radical (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom =
          stabilizer d.radical u ∧
      ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ∧
      ∃ next : CriticalPath d.radical geometry v (back.walk.getVert (back.walk.length-2)),
        next.walk.getVert 1=s ∧
        ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have residual_selector (g₂ x₂ : FreeAmalgam d.radical)
      (hg₂ : g₂ ∈ Ltilde d.radical u) (hx₂ : x₂ ∈ Ltilde d.radical u)
      (v s : Vertex d.radical)
      (hs : (v=act d.radical g₂⁻¹ a ∧ s=act d.radical g₂⁻¹ (back.walk.getVert 1)) ∨
        (v=act d.radical x₂ (act d.radical g₂⁻¹ a) ∧
          s=act d.radical x₂ (act d.radical g₂⁻¹ (back.walk.getVert 1)))) :
      ∃ y ∈ Ltilde d.radical u,
        act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s := by
    rcases hs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl⟩
    · refine ⟨g₂⁻¹*x₂,(Ltilde d.radical u).mul_mem
        ((Ltilde d.radical u).inv_mem hg₂) hx₂,?_,?_⟩ <;> rw [act_mul]
  have hut₀ : Adjacent d.radical u (back.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 0 < back.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hat₀ : Adjacent d.radical a (back.walk.getVert 1) := by
    have hh := adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by rw [back.length_eq_b]; omega : 1 < back.walk.length)))
    simpa only [hmid] using hh
  have hun : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  by_cases hsmall₂ : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨g₂,hg₂,x₂,hx₂,v,hv,s,hwhich₂,hus,hvs,hn₂,hnext₂,hmove,hgeneration,hCu⟩ :=
      root_second_selector h d path hb back hmid hbackequal hsmall₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    have hnot := second_selector_not_trapped h d path hb back hus hvs y
      (Ltilde_le_stabilizer u hy) hya hn₂ (hCa hsmall₂) hmove
    have hcompare : ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
      by_contra hbad
      have hRa := (h.replacement_distance_four_root_comparison_of_failure d
        path hb back hus hvs hbad).1.trans (hCa hsmall₂)
      exact h.replacement_distance_four_comparison_not_two_centers d path hb back hus hvs y
        (Ltilde_le_stabilizer u hy) hya hbad (le_inf hRa (hCu hbad))
    obtain ⟨xgen,hxgen,hgen⟩ := hgeneration
    exact ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,xgen,hxgen,hgen,hcompare,
      exists_backward_path_of_not_le geometry (by omega) back hus hvs hnot⟩
  · have hlarge₂ := le_of_not_gt hsmall₂
    obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g₂,hg₂,x₂,hx₂,hu₁,ha₁,hu₂,ha₂,
        hgen₁,hgen₂,hfixed,hxn,hxp,v,hv,s,hwhich₂,hus,hvs,hn₂,hmove,hnext₂⟩ :=
      h.replacement_equal_small_index_large_backward_path d back hb4 hut₀ rfl hat₀
        hun hbackequal hlarge₂ hbackindex
    obtain ⟨y,hy,hya,hys⟩ := residual_selector g₂ x₂ hg₂ hx₂ v s hwhich₂
    have hgeneration : ∃ xgen ∈ Ltilde d.radical u,
        (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
            (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
          (Z d.radical (path.walk.getVert 2)).map (MulAut.conj xgen).toMonoidHom =
            stabilizer d.radical u := by
      rcases hwhich₂ with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨x₂,hx₂,hgen₁⟩
      · exact ⟨x₂⁻¹,(Ltilde d.radical u).inv_mem hx₂,hgen₂⟩
    obtain ⟨xgen,hxgen,hgen⟩ := hgeneration
    refine ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,xgen,hxgen,hgen,?_,hnext₂⟩
    by_contra hbad
    have hi := (h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad).2.1
    have hq : 1 < Nat.card F := Finite.one_lt_card
    rw [hi] at hlarge₂
    nlinarith

private theorem equal_root_kernel_displacement
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)) :
    ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨hZ,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d path hb hat hct
    hsmall hJm hequal
  have hh := (commutator_mono le_rfl (core_le_mover h d path.start_color hat)).trans hcomm
  rw [hequal]
  exact le_inf (hh.trans hZ) (fun r hr => (mem_omegaCenter_iff.mp (hh hr)).2.2)

/-- A strict neighboring index in the equal-root branch supplies two actual
backward critical paths and the literal comparison on the same second member.
The first selector retains both original-versus-selected full-Z fixed identities;
the second retains its movement and marked-plane fixed data together. -/
theorem Input.replacement_distance_four_strict_equal_root_coherent_comparison
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    distanceFourCoherentComparison path c t (Nat.card F) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb4 hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  obtain ⟨g,hg,x,hx,hgen,_,hfixed,hxn,hxp,hO₁,hO₂⟩ :=
    h.replacement_smaller_mover_original_fixed_selection d path hb4 hat hfirst
      E hE f hf hfQ hTf hindex hJP
  let v := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  let v' := act d.radical x v
  let w' := act d.radical x w
  let J₁ := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2)
  let J₂ := Subgroup.SmallMover.join (U d.radical v') (Q d.radical v') (Q d.radical w') (Nat.card F^2)
  have hgS := Ltilde_le_stabilizer a hg
  have hxS := Ltilde_le_stabilizer a hx
  have hga : act d.radical g⁻¹ a=a := (stabilizer d.radical a).inv_mem hgS
  have hxa : act d.radical x a=a := hxS
  have haw : Adjacent d.radical a w := by
    rw [←hga]
    exact (adjacent_act_iff _ _ _ _).mpr hat
  have hvw : Adjacent d.radical v w := (adjacent_act_iff _ _ _ _).mpr hct
  have haw' : Adjacent d.radical a w' := by
    rw [←hxa]
    exact (adjacent_act_iff _ _ _ _).mpr haw
  have hvw' : Adjacent d.radical v' w' := (adjacent_act_iff _ _ _ _).mpr hvw
  have hJ₁ : J₁=J.map (MulAut.conj g).toMonoidHom := by
    simpa only [J₁,v,w,mover_act,inv_inv] using
      congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) hequal
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := mover_act _ x v w
  have hgen₁ : (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
      stabilizer d.radical a := by rwa [hJ₁]
  have hgen₂ : (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
      stabilizer d.radical a := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hgen₁
    have hS : (stabilizer d.radical a).map (MulAut.conj x⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hxS))
    have hcomp : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
        MonoidHom.id (FreeAmalgam d.radical) := by
      apply MonoidHom.ext
      intro y
      change x⁻¹*(x*y*x⁻¹)*(x⁻¹)⁻¹=y
      group
    rw [Subgroup.map_sup,Subgroup.map_sup,Subgroup.map_map,hcomp,Subgroup.map_id,hS,←hJ₂] at hh
    rw [sup_assoc,sup_comm (Z d.radical z),←sup_assoc]
    exact hh
  have hfixed' : (Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hO₁' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₁ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₁]
  have hO₂' : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
      centralizer (J₂ : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    rwa [hJ₂,hJ₁]
  have hi₁ := movingIndex_act geometry (d := c) (by omega) path.start_color g⁻¹
    ((stabilizer d.radical a).inv_mem hgS)
  have hi₂ := (movingIndex_act geometry (d := v) (by omega) path.start_color x hxS).trans hi₁
  have heq₁ : J₁=Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hequal
    change (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t)
      (Nat.card F^2)).map _ = (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map _ at hh
    rwa [←mover_act,←mover_act,hga] at hh
  have heq₂ : J₂=Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w') (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) heq₁
    change (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w)
      (Nat.card F^2)).map _ = (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2)).map _ at hh
    rwa [←mover_act,←mover_act,hxa] at hh
  have hjw : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) g⁻¹ a t
    rw [hga] at hh
    exact hh.trans_le hJm
  have hjw' : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w') (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) x a w
    rw [hxa] at hh
    exact hh.trans_le hjw
  have hcomm₁ := equal_root_kernel_displacement h d path hb4 haw hvw hsmall hjw heq₁
  have hcomm₂ := equal_root_kernel_displacement h d path hb4 haw' hvw' hsmall hjw' heq₂
  have hn : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hh := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hn
    rw [map_normalizer_eq_of_bijective _ (MulAut.conj g⁻¹).bijective,Subgroup.map_sup] at hh
    have hS : (stabilizer d.radical a).map (MulAut.conj g⁻¹).toMonoidHom=stabilizer d.radical a :=
      mem_normalizer_iff_map_conj_eq.mp ((stabilizer d.radical a).le_normalizer
        ((stabilizer d.radical a).inv_mem hgS))
    have hvc : act d.radical g v=c := by
      dsimp only [v]
      rw [←act_mul,inv_mul_cancel,act_one]
    have hga' : act d.radical g a=a := hgS
    rw [hS,←Z_act,←Z_act,hvc,hga'] at hh
    exact hnormal hh
  have hnot : ¬ (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      Z d.radical v' ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) := by
    rintro ⟨ht₁,ht₂⟩
    by_cases hn₁ : Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)
    · have hn₂ : ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v' ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
        intro hn₂
        have hb' := paired_endpoint_normalizes_first_join x hxS hn₂
        apply hn
        rw [←hgen₁]
        refine sup_le (sup_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
          (edge_normalizes_neighbor_seed_join haw hvw)) hn₁) ?_
        simpa only [Z_act,inv_inv] using hb'
      have hback : act d.radical x⁻¹ v'=v := by
        dsimp only [v']
        rw [←act_mul,mul_inv_cancel,act_one]
      exact trapped_pair_impossible h d path hb4 haw' hvw' haw hvw x⁻¹
        ((stabilizer d.radical a).inv_mem hxS) hback hcomm₂ hcomm₁
        ((inf_right_comm _ _ _).trans hfixed') hgen₂ (by rw [hi₂]; exact hmove) hn₂ ht₂ ht₁
    · exact trapped_pair_impossible h d path hb4 haw hvw haw' hvw' x hxS rfl
        hcomm₁ hcomm₂ hfixed' hgen₁ (by rw [hi₁]; exact hmove) hn₁ ht₁ ht₂
  have complete (u w : Vertex d.radical) (r : FreeAmalgam d.radical)
      (hr : r ∈ stabilizer d.radical a)
      (hrc : act d.radical r c=u) (hrt : act d.radical r t=w)
      (haw : Adjacent d.radical a w) (huw : Adjacent d.radical u w)
      (hnot : ¬ Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
      (hO : (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ∃ v s, ∃ y ∈ Ltilde d.radical u,
          act d.radical y a=v ∧ act d.radical y (back.walk.getVert 1)=s ∧
          Adjacent d.radical u s ∧ Adjacent d.radical v s ∧
          ¬ Z d.radical (path.walk.getVert 2) ≤ normalizer
            ((Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
          ∃ x₂ ∈ Ltilde d.radical u,
          (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
              (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
            (Z d.radical (path.walk.getVert 2)).map (MulAut.conj x₂).toMonoidHom =
              stabilizer d.radical u ∧
          ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
            ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
              ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ∧
          ∃ next : CriticalPath d.radical geometry v a,
            next.walk.getVert 1=s ∧
            ∀ i ≤ back.walk.length-2, next.walk.getVert (i+2)=back.walk.getVert i := by
    have hlen : path.walk.length-2=2 := by rw [path.length_eq_b,hb]
    obtain ⟨back,hback,hover⟩ :
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
      have hh := exists_backward_path_of_not_le geometry (by omega) path haw huw hnot
      have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := congrArg _ hlen
      rw [he] at hh
      exact hh
    have hmid : back.walk.getVert 2=a := by simpa only [SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hlast : back.walk.getVert 3=path.walk.getVert 1 := hover 1 (by omega)
    have hra : act d.radical r a=a := hr
    have he : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
      have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
      rw [←mover_act,←mover_act,hra,hrc,hrt] at hh
      simpa only [hback] using hh.symm
    have hi : (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical u) ≤ Nat.card F^2 := by
      rw [hback,←hrc,←hrt,own_index_act,own_index_neighbors _ hat hct]
      exact hJm
    have hCa (hs : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2) :
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
      have hOroot := h.replacement_distance_four_root_original_fixed d path hb back hmid hlast hs
      rw [hfirst] at hOroot
      have hSroot := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hs
      rw [hback] at hSroot
      exact ((le_inf hOroot hSroot).trans_eq hO).trans inf_le_right
    obtain ⟨v,s,y,hy,hya,hys,hus,hvs,hn,xgen,hxgen,hgen,hcompare,hnext⟩ :=
      second_path_of_full_root_centrality h d path hb back hmid he hi hCa
    have ht : back.walk.getVert (back.walk.length-2)=a := by
      rw [back.length_eq_b,hb]
      exact hmid
    rw [ht] at hnext
    exact ⟨back,hback,hover,v,s,y,hy,hya,hys,hus,hvs,hn,xgen,hxgen,hgen,hcompare,hnext⟩
  by_cases ht₁ : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))
  · refine ⟨g,hg,x,hx,v',w',Or.inr ⟨rfl,rfl⟩,haw',hvw',?_⟩
    exact complete v' w' (g⁻¹*x)
      ((stabilizer d.radical a).mul_mem ((stabilizer d.radical a).inv_mem hgS) hxS)
      (by rw [act_mul]) (by rw [act_mul]) haw' hvw' (fun ht₂ => hnot ⟨ht₁,ht₂⟩) hO₂'
  · exact ⟨g,hg,x,hx,v,w,Or.inl ⟨rfl,rfl⟩,haw,hvw,
      complete v w g⁻¹ ((stabilizer d.radical a).inv_mem hgS) rfl rfl haw hvw ht₁ hO₁'⟩

/-- The equal/small original branch reduces to two coherent actual paths
with their same-member comparison, or an explicit strict-index neighbor with
unequal mover. The uniform bound and both trapping alternatives are discharged internally. Rebased neighbors are
recorded, rather than identified with the prescribed original neighbor. -/
theorem Input.replacement_distance_four_coherent_comparison_or_strict_unequal_neighbor
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    (∃ c', Adjacent d.radical c' t ∧
      Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ∧
      Subgroup.SmallMover.join (U d.radical c') (Q d.radical c')
          (Q d.radical t) (Nat.card F^2) ≠
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)) ∨
    (∃ c', Adjacent d.radical c' t ∧
      Subgroup.SmallMover.join (U d.radical c') (Q d.radical c')
          (Q d.radical t) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2) ∧
      distanceFourCoherentComparison path c' t (Nat.card F)) := by
  classical
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  by_cases hlarge : ∃ c', Adjacent d.radical c' t ∧
      Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c')
  · obtain ⟨c',hc',hm⟩ := hlarge
    by_cases he : Subgroup.SmallMover.join (U d.radical c') (Q d.radical c')
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)
    · exact Or.inr ⟨c',hc',he,
        h.replacement_distance_four_strict_equal_root_coherent_comparison d path hb hat hfirst hc'
          hm he hsmall hJm⟩
    · exact Or.inl ⟨c',hc',hm,he⟩
  · have hlocal : ∀ c', Adjacent d.radical c' t →
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c') ≤ Nat.card F := by
      intro c' hc'
      exact le_of_not_gt (fun hm => hlarge ⟨c',hc',hm⟩)
    have hbound : ∀ v w c' : Vertex d.radical, color d.radical v=false →
        Adjacent d.radical v w → Adjacent d.radical c' w →
        (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c') ≤ Nat.card F := by
      intro v w c' hv hvw hc'w
      exact global_neighbor_bound_of_edge geometry (by omega) path.start_color hat
        (Nat.card F) hlocal hv hvw hc'w
    obtain ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,_,hCa⟩ :=
      h.replacement_distance_four_first_selector_root_centrality d path hb hat hfirst hct
        hnormal hequal hsmall hJm
    have hlen : path.walk.length-2=2 := by rw [path.length_eq_b,hb]
    obtain ⟨back,hback,hover⟩ :
        ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
      have hh := h.replacement_selected_seed_backward_of_uniform_bound d path hb4 haw huw hn hbound
      have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := congrArg _ hlen
      rw [he] at hh
      exact hh
    have hmid : back.walk.getVert 2=a := by simpa only [SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hlast : back.walk.getVert 3=path.walk.getVert 1 := hover 1 (by omega)
    have huData : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) ∧
        (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
            (U d.radical u) ≤ Nat.card F^2 := by
      have transport (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a) :
          Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
              (Q d.radical (act d.radical r t)) (Nat.card F^2) =
            Subgroup.SmallMover.join (U d.radical (act d.radical r c))
              (Q d.radical (act d.radical r c)) (Q d.radical (act d.radical r t)) (Nat.card F^2) ∧
          (centralizer (Subgroup.SmallMover.join (U d.radical (act d.radical r c))
              (Q d.radical (act d.radical r c)) (Q d.radical (act d.radical r t))
              (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
            (U d.radical (act d.radical r c)) ≤ Nat.card F^2 := by
        have hra : act d.radical r a=a := hr
        constructor
        · conv_lhs => rw [←hra]
          rw [mover_act,mover_act,hequal]
        · rw [own_index_act,own_index_neighbors _ hat hct]
          exact hJm
      rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact transport g⁻¹ ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg))
      · simpa only [act_mul] using transport (g⁻¹*x)
          ((stabilizer d.radical a).mul_mem
            ((stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg)) (Ltilde_le_stabilizer a hx))
    obtain ⟨v,s,y,hy,hya,hys,hus,hvs,hn₂,xgen,hxgen,hgen,hcompare,hsecond⟩ :=
      second_path_of_full_root_centrality h d path hb back hmid
        (by simpa only [hback] using huData.1) (by simpa only [hback] using huData.2)
        (hCa back hback hmid hlast)
    have ht : back.walk.getVert (back.walk.length-2)=a := by
      rw [back.length_eq_b,hb]
      exact hmid
    rw [ht] at hsecond
    exact Or.inr ⟨c,hct,hequal,g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hover,
      v,s,y,hy,hya,hys,hus,hvs,hn₂,xgen,hxgen,hgen,hcompare,hsecond⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
