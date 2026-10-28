module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FirstPairing.Transport
public import Theory.Representation.SymplecticFourOrthogonalCover.RootValues
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.OriginalLargePaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedLowIndex

/-!
# Uniform small indices and the terminal twist in a trapped radius

If the whole starting radius is trapped two steps before the critical endpoint,
the large-image backward selector excludes a large critical image. The complete
root selector then bounds every neighbor's index modulo B by q. Vertex and edge
transitivity transport that bound to every original-group vertex, retaining the
literal whole B-preimage and U-layer.

On any full natural cover, a commutator lying in the residual-fixed subgroup is
trivial: each of its generating commutator values is a displacement in the full
cover kernel, so fixed-point lifting kills it. The trapped source commutator has
order q and therefore cannot be residual-fixed at the endpoint. No complement
to the covering kernel is chosen.

Residual-edge generation constructs the actual terminal-edge transporter. The
consumer keeps it, its invariant B-index, and the same escaping neighbor with
both full fixed indices and its order-q nonfixed commutator. This supplies the
uniform bound and terminal obstruction used in MS93 (5.8), printed p.920. The
identity U_z intersect Q_a = U_z intersect B_(z-2), its commutator transport under
this twist, and the ensuing contradiction remain to be established; no backward
path or distance-two replacement is asserted from the trapped hypothesis.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A trapped full radius excludes both the large-image backward branch and every root neighbor whose B-relative moving index exceeds q. -/
theorem Input.replacement_trapped_radius_edge_indices
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 ∧
      ∀ c, Adjacent d.radical c t →
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F := by
  have hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2 := by
    by_contra! hlarge
    obtain ⟨c,hct,hn,y,hy,haw,hvw,hidx,hn',back,hfirst',hover⟩ :=
      h.replacement_large_image_backward_step d path hb hat hfirst hlarge
    exact back.critical.2 ((le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)).trans htrap)
  refine ⟨hsmall,?_⟩
  intro c hct
  by_contra! hmove
  obtain ⟨y,hy,haw,hvw,hidx,back,hfirst',hover⟩ :=
    h.replacement_root_backward_step d path hb hat hfirst hct hmove hsmall
  exact back.critical.2 ((le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)).trans htrap)

omit h in
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

/-- A single trapped full radius forces the field-sized upper bound at every oriented two-edge configuration in the actual amalgam graph. -/
theorem Input.replacement_trapped_radius_uniform_indices
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F := by
  have hi := (h.replacement_trapped_radius_edge_indices d path hb hat hfirst htrap).2
  intro v w c hv hvw hcw
  exact global_neighbor_bound_of_edge geometry (by omega) path.start_color hat (Nat.card F)
    hi hv hvw hcw

/-- A commutator on any subgroup of the whole U-layer is residual-fixed precisely when it is trivial, including the entire central attachment. -/
theorem Input.replacement_natural_commutator_fixed_iff
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTU : T ≤ U d.radical z) :
    ⁅Y,T⁆ ≤ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ↔ ⁅Y,T⁆=⊥ := by
  refine ⟨?_,fun he => he ▸ bot_le⟩
  intro hfixed
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hz
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ ((γ.comp (inclusion hYS)) y) w))=
        y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  apply le_bot_iff.mp
  apply commutator_le.mpr
  intro y hy u hu
  have hU : ⁅y,u⁆ ∈ U d.radical z :=
    le_normalizer_iff_commutator_le_right.mp (hYS.trans (U_normalized z))
      (commutator_mem_commutator hy (hTU hu))
  obtain ⟨v,hv⟩ := (hjr.symm ▸ hU : ⁅y,u⁆ ∈ j.range)
  have hzero : p v.toAdd=0 := (hker v.toAdd).mpr (by
    change j v ∈ _
    rw [hv]
    exact hfixed (commutator_mem_commutator hy hu))
  have hvalue := embedded_cover_value_in_kernel_eq_one (U d.radical z) Y p he j hj hjr
    (γ.comp (inclusion hYS)) hact y hy u (hTU hu) ⟨v,hzero,hv⟩
  exact hvalue

/-- The literal source U-intersection has an order-q commutator that is not residual-fixed at the original critical endpoint. -/
theorem Input.replacement_trapped_root_commutator_not_fixed
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    ¬ ⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ ≤
      centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  have hYS : Z d.radical v ≤ stabilizer d.radical z :=
    (le_inf (le_sup_left.trans (neighbor_seed_join_le_radius hat hvt)) htrap).trans
      (truncated_radius_le_endpoint_stabilizer path (by omega))
  obtain ⟨_,hcard,_,_,hsource,_⟩ :=
    h.replacement_trapped_root_exact_indices d path hb hat hvt hn htrap
  intro hfix
  have he := (h.replacement_natural_commutator_fixed_iff d geometry hb path.end_color
    (Z d.radical v) (U d.radical z ⊓ Q d.radical a) hYS inf_le_left).mp hfix
  rw [hsource,he,Subgroup.card_bot] at hcard
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

omit h in
private theorem residual_neighbor_transporter
    {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (hgen : pResidual 2 M ⊔ R = ⊤)
    {a t u : Vertex R} (ha : color R a=false)
    (hat : Adjacent R a t) (hau : Adjacent R a u) :
    ∃ x ∈ Ltilde R a, act R x t=u := by
  let S := stabilizer R a
  let N := pResidual 2 S
  let T := (Q R t).subgroupOf S
  have hTS : Q R t ≤ S := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hn : N.map S.subtype=Ltilde R a := rfl
  have htop : T ⊔ N=⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hTS,hn,sup_comm,
      CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.local_residual_edge_generation R hgen ha hat,
      ←MonoidHom.range_eq_map,range_subtype]
  let : N.Normal := inferInstanceAs (pResidual 2 S).Normal
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors R a hat hau
  have hg' : (⟨g,hg⟩ : S) ∈ T ⊔ N := htop ▸ mem_top _
  obtain ⟨v,hv,x,hx,hvx⟩ := mem_sup_of_normal_right.mp hg'
  have hvt : act R v.val t=t := (show v.val ∈ Q R t from hv).1
  refine ⟨x.val,mem_map_of_mem S.subtype hx,?_⟩
  have he : v.val*x.val=g := congrArg Subtype.val hvx
  rw [←he,act_mul,hvt] at hgt
  exact hgt

omit [Finite F] [CharP F 2] in
/-- The residual at the two-step terminal vertex moves the last edge to the preceding edge and preserves the exact whole-U index modulo B. -/
theorem Input.replacement_terminal_edge_residual_twist
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical) :
    ∃ x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2)),
      act d.radical x (path.walk.getVert (path.walk.length-1)) =
        path.walk.getVert (path.walk.length-3) ∧
      (B d.radical (path.walk.getVert (path.walk.length-2))
          (geometry.Z_normal _)).relIndex (U d.radical (act d.radical x z)) =
        (B d.radical (path.walk.getVert (path.walk.length-2))
          (geometry.Z_normal _)).relIndex (U d.radical z) := by
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
    apply (path.vertex_color (Nat.sub_le _ _)).mpr
    have he : Even path.walk.length := by
      rw [path.shortest,path.critical.1]
      exact geometry.even a path.start_color
    rw [Nat.even_iff] at he ⊢
    omega
  have ht : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
      (path.walk.getVert (path.walk.length-1)) := by
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-2 < path.walk.length)
    rw [show path.walk.length-2+1=path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hu : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
      (path.walk.getVert (path.walk.length-3)) := by
    apply adjacent_symm d.radical
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-3 < path.walk.length)
    rw [show path.walk.length-3+1=path.walk.length-2 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  obtain ⟨x,hx,he⟩ := residual_neighbor_transporter (h.replacement_residual_edge_generation d) hp ht hu
  exact ⟨x,hx,he,movingIndex_act geometry (by omega) hp x (Ltilde_le_stabilizer _ hx)⟩

/-- The trapped-radius consumer simultaneously retains the global index bound, the actual terminal twist, and the same escaping neighbor with its exact source commutator and both full fixed indices. -/
theorem Input.replacement_trapped_radius_twist_configuration
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    (∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) ∧
    (∃ x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2)),
      act d.radical x (path.walk.getVert (path.walk.length-1)) =
        path.walk.getVert (path.walk.length-3) ∧
      (B d.radical (path.walk.getVert (path.walk.length-2))
        (geometry.Z_normal _)).relIndex (U d.radical z) ≤ Nat.card F ∧
      (B d.radical (path.walk.getVert (path.walk.length-2))
        (geometry.Z_normal _)).relIndex (U d.radical (act d.radical x z)) =
      (B d.radical (path.walk.getVert (path.walk.length-2))
        (geometry.Z_normal _)).relIndex (U d.radical z)) ∧
    ∃ u y, Adjacent d.radical u t ∧ y ∈ stabilizer d.radical a ∧
      let v := act d.radical y u
      let w := act d.radical y t
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
      Nat.card (⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ :
        Subgroup (FreeAmalgam d.radical)) = Nat.card F ∧
      (centralizer ((U d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (U d.radical v) = Nat.card F ∧
      (centralizer ((U d.radical z ⊓ Q d.radical a :
        Subgroup (FreeAmalgam d.radical)) : Set _)).relIndex (Z d.radical v) = Nat.card F ∧
      ¬ ⁅Z d.radical v,U d.radical z ⊓ Q d.radical a⁆ ≤
        centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  have hbound := h.replacement_trapped_radius_uniform_indices d path hb hat hfirst htrap
  refine ⟨hbound,?_,?_⟩
  · obtain ⟨x,hx,he,hi⟩ := h.replacement_terminal_edge_residual_twist d path hb
    have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
    have hp : color d.radical (path.walk.getVert (path.walk.length-2))=false := by
      apply (path.vertex_color (Nat.sub_le _ _)).mpr
      have he : Even path.walk.length := by
        rw [path.shortest,path.critical.1]
        exact geometry.even a path.start_color
      rw [Nat.even_iff] at he ⊢
      omega
    have ht : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
        (path.walk.getVert (path.walk.length-1)) := by
      have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-2 < path.walk.length)
      rw [show path.walk.length-2+1=path.walk.length-1 by omega] at hh
      exact (cosetGraph_adj d.radical _ _).mp hh
    have hz : Adjacent d.radical z (path.walk.getVert (path.walk.length-1)) := by
      apply adjacent_symm d.radical
      have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
      rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
      exact (cosetGraph_adj d.radical _ _).mp hh
    exact ⟨x,hx,he,hbound _ _ _ hp ht hz,hi⟩
  · obtain ⟨u,y,hut,hy,haw,hvw,hcases⟩ :=
      h.replacement_backward_path_or_root_escape d path hb hat
    rcases hcases with ⟨back,hback,hover⟩ | ⟨hk,hn,hi,hi',hmove,hnorm,hquad⟩
    · exact (back.critical.2
        ((le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)).trans htrap)).elim
    · obtain ⟨hcomm,hcard,hU,hZ,hsource,hfixed,hsourceU,hsourceZ⟩ :=
        h.replacement_trapped_root_exact_indices d path hb haw hvw hn hk
      rw [hsource] at hcard
      exact ⟨u,y,hut,hy,haw,hvw,hk,hn,hi,hi',hcard,hsourceU,hsourceZ,
        h.replacement_trapped_root_commutator_not_fixed d path hb haw hvw hn hk⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
