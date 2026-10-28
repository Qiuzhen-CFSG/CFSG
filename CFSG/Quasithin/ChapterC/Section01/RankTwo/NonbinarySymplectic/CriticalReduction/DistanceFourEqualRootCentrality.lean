module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNeighbor
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths

/-!
# The same selected equal-root mover centralizes the failed comparison

At distance four, use the actual backward critical path and its original
midpoint to make the equal-mover root selection. The full intersection
commutator of a failed comparison lies in the critical root displacement,
which fixes the original mover. The original mover and its maximizing
parabolic core have identical fixed subgroups on the whole starting seed.

The selected mover contains the original kernel. Its quadratic action on
the selected seed therefore fixes the intersection commutator as well.
The very same three-generator equality, endpoint placement and parabolic
normalizer then imply centrality at the backward starting vertex.

The selected neighbor retains its nonnormal seed join and the actual
backward-path-or-trapped alternative. No criticality of that neighbor to
the original midpoint is assumed. Source: MS93 (5.12)(1), printed p.925,
the equal-mover branch using the same selector from (5.6).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem mover_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
        (Q R (act R y t)) (q^2) =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R t) (q^2)).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [CharP F 2] in
private theorem core_le_mover
    {u t : Vertex d.radical} (hu : color d.radical u=false)
    (hut : Adjacent d.radical u t) :
    Q d.radical u ≤ Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) hu hut
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

/-- The actual equal-root selector has a member retaining all the geometric
alternatives, and any failed source comparison at that member centralizes
the whole backward starting stabilizer. -/
theorem Input.replacement_distance_four_equal_root_selected_centrality
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
  refine ⟨g,hg,x,hx,v,hv,w,hwhich,huw,hvw,hn,hnext,?_⟩
  rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact finish c₁ t₁ J₁ hu₁ hc₁ hQJ₁ hcomm₁ x hxn hgen₁
  · have hxN : x ∈ normalizer (D : Set (FreeAmalgam d.radical)) := hxn
    exact finish c₂ t₂ J₂ hu₂ hc₂ hQJ₂ hcomm₂ x⁻¹
      ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxN) hgen₂

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
