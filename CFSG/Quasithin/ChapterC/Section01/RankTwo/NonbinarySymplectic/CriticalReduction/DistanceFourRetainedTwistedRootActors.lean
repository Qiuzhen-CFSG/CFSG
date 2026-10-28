module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRetainedTwistedPath
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPairCoordinates
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCommonEdgeRootActors

/-!
# Retained full root actors on the actual common edge

The frozen twisted-path producer supplies the same directed escape, the
original reciprocal full-seed indices, and a twisted companion with its two
reciprocal indices.  This owner strengthens that companion to the literal
overlap supplied by the directed escape construction.  The two unchanged
full endpoint actors then receive one natural quotient marking at the same
backward vertex, with their fixed kernels distinct and their root images
of product order q².  No selector is replaced and all three original
generators remain in the hypotheses.

Source: MS93 (5.12)(3), printed p.927, with (5.1).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource CentralRootGeometry.SmallMovers

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem retained_full_critical_fixed_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (_hb : 0<geometry.b d.radical) :
    Z d.radical a ⊓ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical z := by
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hC := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) z path.end_color
  rw [←hC]
  ext x
  exact ⟨fun hx => ⟨hx.1,hAS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩

private theorem retained_full_critical_actor_field_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4≤geometry.b d.radical)
    (hi : (Q d.radical z).relIndex (Z d.radical a)=Nat.card F) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)=Nat.card F := by
  have hZS := path.endpoint_Z_le_start_stabilizer (by omega)
  have heq := retained_full_critical_fixed_kernel h d path (by omega)
  let := finite_Z d.radical a
  have hu : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)≤Nat.card F := by
    apply (relIndex_le_of_le_right (U_le_Z a) index_ne_zero_of_finite).trans
    rw [←inf_relIndex_left,heq,inf_relIndex_left,hi]
  have hn : ⁅Z d.radical z,U d.radical a⁆ ≠ ⊥ := by
    intro hz
    have hzero : ⁅Z d.radical a,Z d.radical z⁆=⊥ := by
      rw [h.replacement_Z_commutator_eq_U d geometry hb path.start_color _ hZS,
        commutator_comm,hz]
    have hfixed : Z d.radical a ≤ centralizer (Z d.radical z : Set _) :=
      commutator_eq_bot_iff_le_centralizer.mp hzero
    have hQ : Z d.radical a ≤ Q d.radical z := by
      have hh : Z d.radical a ⊓ Q d.radical z=Z d.radical a := by
        rw [←heq,inf_eq_left.mpr hfixed]
      exact hh ▸ inf_le_right
    exact path.critical.2 hQ
  have hbot : centralizer ((⊥ : Subgroup (FreeAmalgam d.radical)) :
      Set (FreeAmalgam d.radical)) = ⊤ := by
    apply top_unique
    intro x _ y hy
    have hy1 : y=1 := mem_bot.mp hy
    rw [hy1,one_mul,mul_one]
  have hlo := h.replacement_fixed_U_moving_index_lower d geometry hb path.start_color
    (Z d.radical z) ⊥ hZS bot_le (by simpa only [hbot,inf_top_eq] using hn)
  have hlo' : Nat.card F≤(centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) := by simpa only [hbot,inf_top_eq] using hlo
  exact Nat.le_antisymm hu hlo'

omit [Finite H] [Field F] [Finite F] [CharP F 2] h in
private theorem retained_critical_endpoint_le_first_core
    {geometry : Geometry d.radical} {a z w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 0<geometry.b d.radical)
    (hfirst : path.walk.getVert 1=w) : Z d.radical z ≤ Q d.radical w := by
  rw [←hfirst]
  apply Z_le_Q_of_dist_lt _ z (geometry.exists_critical z path.end_color)
  rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,
    path.length_eq_b]
  change geometry.b d.radical-1<geometry.b d.radical
  omega

set_option maxHeartbeats 800000 in
/-- The frozen twisted path, strengthened to a literal overlap companion and
the natural coordinates of the two retained full root actors. -/
theorem Input.replacement_distance_four_retained_twisted_root_actors
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (r k : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hk : k ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hrw : act d.radical r (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hfixa : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hterminal : Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 3))
        (Nat.card F^2))
    (hterminalmove : (centralizer (Subgroup.SmallMover.join
        (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F^2)
    (hfixe : (Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
          (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (stabilizer d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hkn : k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        Z d.radical (act d.radical k z)=stabilizer d.radical a) :
    (¬ Z d.radical u ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2))) ∧
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
    (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ companion : CriticalPath d.radical geometry u
        (act d.radical k (path.walk.getVert 2)),
      companion.walk.getVert 1=w ∧
      (∀ i≤2, companion.walk.getVert (i+2)=
        act d.radical k (path.walk.getVert i)) ∧
      (Q d.radical (act d.radical k (path.walk.getVert 2))).relIndex
        (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex
        (Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F ∧
      Z d.radical (path.walk.getVert 2)≤Q d.radical w ∧
      Z d.radical (act d.radical k (path.walk.getVert 2))≤Q d.radical w ∧
      (centralizer (Z d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u)=Nat.card F ∧
      (centralizer (Z d.radical (act d.radical k (path.walk.getVert 2)) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical u)=Nat.card F ∧
      Z d.radical u ⊓ centralizer (Z d.radical (path.walk.getVert 2) : Set _) ≠
        Z d.radical u ⊓ centralizer
          (Z d.radical (act d.radical k (path.walk.getVert 2)) : Set _) ∧
      ∃ E : BinaryField, E.degree=n ∧
        ∃ f : stabilizer d.radical u →* Sp E.Carrier,
          Function.Surjective f ∧ f.ker.map (stabilizer d.radical u).subtype=Q d.radical u ∧
          ((Q d.radical w).subgroupOf (stabilizer d.radical u)).map f ≤ unipotent ∧
          (∀ A : Subgroup (stabilizer d.radical u),
            (centralizer (A : Set (stabilizer d.radical u))).relIndex
              ((U d.radical u).subgroupOf (stabilizer d.radical u)) =
              2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
                (symplecticNatural (k := E.Carrier) 2)) (A.map f)) ∧
          ∃ s₁ s₂ : Option E.Carrier, s₁ ≠ s₂ ∧
            ((Z d.radical (path.walk.getVert 2)).subgroupOf
              (stabilizer d.radical u)).map f=rootImage s₁ ∧
            ((Z d.radical (act d.radical k (path.walk.getVert 2))).subgroupOf
              (stabilizer d.radical u)).map f=rootImage s₂ ∧
            Nat.card (rootImage s₁ ⊔ rootImage s₂ : Subgroup (Sp E.Carrier))=Nat.card F^2 ∧
            (Q d.radical u).relIndex
              (Z d.radical (path.walk.getVert 2) ⊔
                Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F^2 ∧
            Nat.card F^2 < (Q d.radical u).relIndex
              (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
                (Q d.radical w) (Nat.card F^2)) := by
  obtain ⟨hescape,hroot,hroot',_oldCompanion,htwist,htwist'⟩ :=
    h.replacement_distance_four_retained_twisted_path d path hb r k hr hk hru hrw
      hequal hJm hmove hfixa hterminal hterminalmove hfixe hkn back hfirst hnot hgen
  let e := path.walk.getVert 2
  let p₀ := path.act k
  have hka : act d.radical k a=a := hk
  let p : CriticalPath d.radical geometry a (act d.radical k z) := {
    start_color := path.start_color
    walk := p₀.walk.copy hka rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact p₀.shortest.trans (congrArg
        (fun b => (cosetGraph d.radical).dist b (act d.radical k z)) hka)
    critical := by simpa only [hka] using p₀.critical }
  have hp (i : ℕ) : p.walk.getVert i=act d.radical k (path.walk.getVert i) := by
    change (p₀.walk.copy hka rfl).getVert i=_
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical k path.walk i
  have hl : p.walk.length=4 := p.length_eq_b.trans hb
  have hp2 : p.walk.getVert (p.walk.length-2)=act d.radical k e := by
    rw [hl]
    exact hp 2
  have hescape' : ¬ Z d.radical u≤Q d.radical (p.walk.getVert (p.walk.length-2)) := by
    rw [hp2]
    intro hh
    exact hescape (le_inf inf_le_left (inf_le_left.trans hh))
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj d.radical _ _).mp
        (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e (path.walk.getVert 1) := by
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have haw : Adjacent d.radical a w := by
    rw [←hr,←hrw]
    exact (adjacent_act_iff d.radical r _ _).mpr hat
  have huw : Adjacent d.radical u w := by
    rw [←hru,←hrw]
    exact (adjacent_act_iff d.radical r _ _).mpr het
  obtain ⟨c,hc,hcover⟩ := exists_backward_path_of_not_le geometry (by omega) p haw huw hescape'
  let companion : CriticalPath d.radical geometry u (act d.radical k e) := {
    start_color := c.start_color
    walk := c.walk.copy rfl hp2
    shortest := by rw [SimpleGraph.Walk.length_copy,←hp2]; exact c.shortest
    critical := by simpa only [hp2] using c.critical }
  have hcfirst : companion.walk.getVert 1=w := by
    change (c.walk.copy rfl hp2).getVert 1=w
    rwa [SimpleGraph.Walk.getVert_copy]
  have hcover' (i : ℕ) (hi : i≤2) :
      companion.walk.getVert (i+2)=act d.radical k (path.walk.getVert i) := by
    change (c.walk.copy rfl hp2).getVert (i+2)=_
    rw [SimpleGraph.Walk.getVert_copy,hcover i (by omega),hp]
  have hu : color d.radical u=false := by
    rw [←hru,action_preserves_color]
    exact (path.vertex_color (by omega)).mpr (by decide)
  have hE₁ : Z d.radical e≤Q d.radical w :=
    retained_critical_endpoint_le_first_core d back (by omega) hfirst
  have hE₂ : Z d.radical (act d.radical k e)≤Q d.radical w :=
    retained_critical_endpoint_le_first_core d companion (by omega) hcfirst
  have hi₁ := retained_full_critical_actor_field_index h d back (by omega) hroot
  have hi₂ := retained_full_critical_actor_field_index h d companion (by omega) htwist
  have hne : Z d.radical u ⊓ centralizer (Z d.radical e : Set _) ≠
      Z d.radical u ⊓ centralizer
        (Z d.radical (act d.radical k e) : Set _) := by
    rw [retained_full_critical_fixed_kernel d back (by omega),
      retained_full_critical_fixed_kernel d companion (by omega)]
    exact fun hh => hescape hh.le
  obtain ⟨E,hE,f,hf,hfQ,hTf,hglobal,s₁,s₂,hsne,hs₁,hs₂,hpair,hpairIndex,hlarge⟩ :=
    h.replacement_distinct_root_actor_coordinates d (by omega) hu huw
      (Z d.radical e) (Z d.radical (act d.radical k e)) hE₁ hE₂ hroot' htwist'
      hi₁ hi₂ hne
  exact ⟨hescape,hroot,hroot',companion,hcfirst,hcover',htwist,htwist',hE₁,hE₂,
    hi₁,hi₂,hne,E,hE,f,hf,hfQ,hTf,hglobal,s₁,s₂,hsne,hs₁,hs₂,hpair,hpairIndex,hlarge⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
