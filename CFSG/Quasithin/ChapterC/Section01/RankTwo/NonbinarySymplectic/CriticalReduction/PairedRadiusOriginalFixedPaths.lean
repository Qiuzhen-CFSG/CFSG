module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedOriginalFixedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusSeedIntersection

/-!
# Backward paths retaining the original and selected fixed planes

One strengthened selector supplies the original and selected full-Z fixed
identities together with the paired generation clauses. If both selected
seeds were trapped, the endpoint-nonnormal member would force reciprocal
root indices. The existing joined-commutator comparison and the same paired
fixed identity then contradict strict movement. Hence one of these same
two seeds escapes; reorientation replaces x by its inverse and retains
both original-versus-selected identities.

Iteration preserves the literal critical paths and every overlap. The
strict-movement seed-intersection theorem now makes each three consecutive
starting seeds central at their middle vertex. All full central attachments
remain, and every commutator endpoint is the actual paired endpoint.
Source: MS93 (5.6)--(5.11), printed pp.917--924.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

/-- The same oriented pair retains both original-versus-selected fixed
identities, in addition to the full existing paired source data. -/
@[expose] def pairedRadiusOriginalFixedChoice {M : Type*} [Group M] {R : Subgroup M}
    (geometry : Geometry R) (q : ℕ) (p : CriticalSegment geometry) (v w : Vertex R) : Prop :=
  pathOrbitChoice geometry p v w ∧
    ∃ x ∈ Ltilde R p.first,
      let v' := act R x v
      let w' := act R x w
      let J := Subgroup.SmallMover.join (U R v) (Q R v) (Q R w) (q^2)
      let J' := Subgroup.SmallMover.join (U R v') (Q R v') (Q R w') (q^2)
      let J₀ := Subgroup.SmallMover.join (U R p.first) (Q R p.first)
        (Q R (p.path.walk.getVert 1)) (q^2)
      Adjacent R p.first w' ∧ Adjacent R v' w' ∧
      (B R p.first (geometry.Z_normal p.first)).relIndex (U R v') = nextMovingIndex p ∧
      (J ⊔ Z R p.last) ⊔ (Z R p.last).map (MulAut.conj x).toMonoidHom = stabilizer R p.first ∧
      (J' ⊔ Z R p.last) ⊔ (Z R p.last).map (MulAut.conj x⁻¹).toMonoidHom = stabilizer R p.first ∧
      ((Z R p.first ⊓ centralizer (J : Set (FreeAmalgam R))) ⊓
        centralizer (J' : Set (FreeAmalgam R))) =
          Z R p.first ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R)) ∧
      ((Z R p.first ⊓ centralizer (J₀ : Set (FreeAmalgam R))) ⊓
        centralizer (J : Set (FreeAmalgam R))) =
          Z R p.first ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R)) ∧
      ((Z R p.first ⊓ centralizer (J₀ : Set (FreeAmalgam R))) ⊓
        centralizer (J' : Set (FreeAmalgam R))) =
          Z R p.first ⊓ centralizer (stabilizer R p.first : Set (FreeAmalgam R))

private theorem forget_original {M : Type*} [Group M] {R : Subgroup M}
    {geometry : Geometry R} {q : ℕ} {p : CriticalSegment geometry} {v w : Vertex R}
    (hc : pairedRadiusOriginalFixedChoice geometry q p v w) :
    pairedRadiusChoice geometry q p v w := by
  obtain ⟨hp,x,hx,ha,hv,hi,hg,hg',hf,_,_⟩ := hc
  exact ⟨hp,x,hx,ha,hv,hi,hg,hg',hf⟩

private theorem mover_act {M : Type*} [Group M] [Finite M]
    (R : Subgroup M) (g : FreeAmalgam R) (a t : Vertex R) (q : ℕ) :
    Subgroup.SmallMover.join (U R (act R g a)) (Q R (act R g a))
      (Q R (act R g t)) q =
      (Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) q).map
        (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,Subgroup.SmallMover.join_map _ (MulAut.conj g⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

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

private theorem equal_kernel_displacement
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hc : color d.radical c=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)) :
    ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  have hQaJ : Q d.radical a ≤ J := by
    dsimp only [J]
    rw [hequal]
    exact core_le_mover h d ha hat
  have hJS : J ≤ stabilizer d.radical c := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 c (adjacent_symm _ hct))
  have hDZ : ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical c :=
    le_normalizer_iff_commutator_le_left.mp (hQaJ.trans (hJS.trans (Z_normalized _ c)))
  have hDJ : ⁅⁅Z d.radical c,Q d.radical a⁆,J⁆=⊥ :=
    le_bot_iff.mp ((commutator_mono (commutator_mono le_rfl hQaJ) le_rfl).trans
      (h.replacement_small_mover_Z_quadratic_of_four_lt d geometry hb hc hct).le)
  have hlarge : Nat.card F < (Q d.radical c).relIndex J := by
    have hh := h.replacement_small_mover_join_index d geometry hb.le hc hct
    have hq : 1 < Nat.card F := Finite.one_lt_card
    exact lt_of_lt_of_le (by nlinarith) hh
  exact h.replacement_equal_mover_large_actor_fixed_le_seed d geometry hb hc hct hat
    hequal.symm J le_rfl hlarge _ hDZ hDJ

private theorem trapped_pair_impossible
    {geometry : Geometry d.radical} {a z t v r w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical)
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
  obtain ⟨he,_,halt⟩ := h.replacement_equal_trapped_commutators d path hb.le
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
  exact h.replacement_equal_root_trapped_excluded d path hb.le hat hvt x hx hsmall hn hgen
    hmove (by simpa only [hxv] using hcommon) ⟨htrap,by simpa only [hxv] using htrapw⟩

/-- Above distance four an actual backward pair retains the original and
both selected fixed planes, using the same source conjugators throughout. -/
theorem Input.replacement_paired_radius_original_fixed_step
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ v w, pairedRadiusOriginalFixedChoice geometry (Nat.card F) p v w ∧
      Adjacent d.radical p.first w ∧ Adjacent d.radical v w ∧
      ¬ Z d.radical v ≤ Q d.radical (p.path.walk.getVert (geometry.b d.radical-2)) := by
  let a := p.first
  let z := p.last
  let t := p.path.walk.getVert 1
  let c := p.path.walk.getVert 2
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hat : Adjacent d.radical a t := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; omega : 0 < p.path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical c t := adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
    (p.path.walk.adj_getVert_succ (by rw [p.path.length_eq_b]; omega : 1 < p.path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2)=J := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d p hb
  have hmove := h.replacement_path_moving_index_gt_field d p.path hb
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic_contains_mover_of_four_lt d geometry hb p.path.start_color hat
  obtain ⟨g,hg,x,hx,hgen,_,hfixed,hxn,hxp,hO₁,hO₂⟩ :=
    h.replacement_smaller_mover_original_fixed_selection d p.path hb.le hat rfl
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
  have hJ₂ : J₂=J₁.map (MulAut.conj x⁻¹).toMonoidHom := mover_act _ x v w _
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
  have hi₁ := movingIndex_act geometry (d := c) (by omega) p.path.start_color g⁻¹
    ((stabilizer d.radical a).inv_mem hgS)
  have hi₂ := (movingIndex_act geometry (d := v) (by omega) p.path.start_color x hxS).trans hi₁
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
  have hc : color d.radical c=false :=
    (p.path.vertex_color (by rw [p.path.length_eq_b]; omega : 2 ≤ p.path.walk.length)).mpr (by decide)
  have hv : color d.radical v=false := by simpa only [v,action_preserves_color] using hc
  have hv' : color d.radical v'=false := by simpa only [v',action_preserves_color] using hv
  have hcomm₁ := equal_kernel_displacement h d geometry hb p.path.start_color hv haw hvw heq₁
  have hcomm₂ := equal_kernel_displacement h d geometry hb p.path.start_color hv' haw' hvw' heq₂
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
    exact h.replacement_path_neighbor_join_not_normal d p.path hb hh
  have hnot : ¬ (Z d.radical v ≤ Q d.radical (p.path.walk.getVert (p.path.walk.length-2)) ∧
      Z d.radical v' ≤ Q d.radical (p.path.walk.getVert (p.path.walk.length-2))) := by
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
      exact trapped_pair_impossible h d p.path hb haw' hvw' haw hvw x⁻¹
        ((stabilizer d.radical a).inv_mem hxS) hback hcomm₂ hcomm₁
        ((inf_right_comm _ _ _).trans hfixed') hgen₂ (by rw [hi₂]; exact hmove) hn₂ ht₂ ht₁
    · exact trapped_pair_impossible h d p.path hb haw hvw haw' hvw' x hxS rfl
        hcomm₁ hcomm₂ hfixed' hgen₁ (by rw [hi₁]; exact hmove) hn₁ ht₁ ht₂
  by_cases ht₁ : Z d.radical v ≤ Q d.radical (p.path.walk.getVert (p.path.walk.length-2))
  · have hbackv : act d.radical x⁻¹ v'=v := by
      dsimp only [v']
      rw [←act_mul,mul_inv_cancel,act_one]
    have hbackw : act d.radical x⁻¹ w'=w := by
      dsimp only [w']
      rw [←act_mul,mul_inv_cancel,act_one]
    refine ⟨v',w',⟨⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,
      by rw [act_mul],by rw [act_mul],hi₂⟩,x⁻¹,(Ltilde d.radical a).inv_mem hx,?_⟩,
      haw',hvw',?_⟩
    · dsimp only
      rw [hbackv,hbackw,inv_inv]
      exact ⟨haw,hvw,hi₁,hgen₂,hgen₁,(inf_right_comm _ _ _).trans hfixed',hO₂',hO₁'⟩
    · simpa only [p.path.length_eq_b] using (fun ht₂ => hnot ⟨ht₁,ht₂⟩)
  · exact ⟨v,w,⟨⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,rfl,rfl,hi₁⟩,
      x,hx,haw',hvw',hi₂,hgen₁,hgen₂,hfixed',hO₁',hO₂'⟩,haw,hvw,by
        simpa only [p.path.length_eq_b] using ht₁⟩

/-- Three consecutive actual starting seeds centralize the middle vertex.
The two seed-intersection equalities use their literal path edges. -/
theorem Input.replacement_paired_radius_original_fixed_triple
    {geometry : Geometry d.radical} (hb : 4 < geometry.b d.radical)
    (s : ℕ → CriticalSegment geometry)
    (hs : ∀ i, BackwardLink geometry (pairedRadiusOriginalFixedChoice geometry (Nat.card F))
      (s i) (s (i+1))) (i : ℕ) :
    (Z d.radical (s i).first ⊓ Z d.radical (s (i+1)).first) ⊓ Z d.radical (s (i+2)).first ≤
      centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical)) := by
  have htwo (j : ℕ) : (s (j+1)).path.walk.getVert 2=(s j).first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using (hs j).overlap 0 (by omega)
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := (hs (i+1)).choice
  obtain ⟨_,x,hx,_,_,_,_,_,_,hO,_⟩ := hchoice
  have hi := h.replacement_path_seed_intersection_of_four_lt d (s (i+1)).path hb
  rw [htwo i] at hi
  have hi' := h.replacement_path_seed_intersection_of_four_lt d (s (i+2)).path hb
  have htwo' : (s (i+2)).path.walk.getVert 2=(s (i+1)).first := by
    simpa only [Nat.add_assoc] using htwo (i+1)
  have hfirst' : (s (i+2)).path.walk.getVert 1=t := by
    simpa only [Nat.add_assoc] using hfirst
  rw [htwo',hfirst'] at hi'
  intro y hy
  have h₁ := hi ▸ (show y ∈ Z d.radical (s (i+1)).first ⊓ Z d.radical (s i).first from
    ⟨hy.1.2,hy.1.1⟩)
  have h₂ := hi' ▸ (show y ∈ Z d.radical (s (i+2)).first ⊓ Z d.radical (s (i+1)).first from
    ⟨hy.2,hy.1.2⟩)
  exact (hO ▸ (show y ∈ (Z d.radical (s (i+1)).first ⊓ centralizer
    (Subgroup.SmallMover.join (U d.radical (s (i+1)).first) (Q d.radical (s (i+1)).first)
      (Q d.radical ((s (i+1)).path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
    centralizer (Subgroup.SmallMover.join (U d.radical (s (i+2)).first) (Q d.radical (s (i+2)).first)
      (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) from ⟨h₁,h₂.2⟩)).2

/-- Iterate the strengthened source selection with every overlap and
ordinary paired-path compatibility, retaining full triple-seed centrality. -/
theorem Input.replacement_paired_radius_original_fixed_paths
    {geometry : Geometry d.radical} (p : CriticalSegment geometry)
    (hb : 4 < geometry.b d.radical) :
    ∃ s : ℕ → CriticalSegment geometry, s 0=p ∧
      (∀ i, BackwardLink geometry (pairedRadiusOriginalFixedChoice geometry (Nat.card F))
        (s i) (s (i+1))) ∧
      (∀ i, BackwardLink geometry (pairedRadiusChoice geometry (Nat.card F))
        (s i) (s (i+1))) ∧
      (∀ i k j, j+2*k ≤ geometry.b d.radical →
        (s (i+k)).path.walk.getVert (j+2*k)=(s i).path.walk.getVert j) ∧
      (∀ i, Nat.card F < nextMovingIndex (s i)) ∧
      ∀ i, (Z d.radical (s i).first ⊓ Z d.radical (s (i+1)).first) ⊓
        Z d.radical (s (i+2)).first ≤
          centralizer (stabilizer d.radical (s (i+1)).first : Set (FreeAmalgam d.radical)) := by
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega)
    (pairedRadiusOriginalFixedChoice geometry (Nat.card F))
    (fun q => h.replacement_paired_radius_original_fixed_step d q hb) p
  refine ⟨s,hs0,hs,?_,hover,fun i => h.replacement_path_moving_index_gt_field d (s i).path hb,
    fun i => h.replacement_paired_radius_original_fixed_triple d hb s hs i⟩
  intro i
  obtain ⟨t,hchoice,hat,hvt,hfirst⟩ := (hs i).choice
  exact ⟨⟨t,forget_original hchoice,hat,hvt,hfirst⟩,(hs i).last_eq,(hs i).overlap⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
