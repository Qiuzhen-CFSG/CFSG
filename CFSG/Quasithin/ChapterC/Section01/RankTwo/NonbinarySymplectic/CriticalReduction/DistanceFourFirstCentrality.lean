module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourOriginalFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths

/-!
# The original first selector centralizes a failed distance-four comparison

The initial neighboring seed is arbitrary. Construct the actual equal-mover
root selector and retain its two residual conjugators and geometric
alternative. For a compatible backward path, reversing that path fixes its
critical commutator under the full mover at the original forward edge.
The equal/unequal full-mover comparison transfers this to the original
mover, with its whole central attachment. Thus the same commutator fixes
the original maximizing plane.

The critical root also fixes its own first mover. The actual generating
triple, whose two endpoint seeds lie in the original plane, now yields
centrality at the original starting vertex. This uses the same first
selector and never identifies its arbitrary initial neighbor with the
forward midpoint. Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The same first root selector supplies original-vertex centrality for
every failed comparison on a compatible actual backward path. The initial
neighbor remains arbitrary; its equality with the forward midpoint is not
assumed. All three displayed path identities are supplied by the retained
backward alternative's overlap equations. -/
theorem Input.replacement_distance_four_first_root_selected_centrality
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
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ t
      let c₁ := act d.radical g⁻¹ c
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      ∃ u ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (u=c₁ ∧ w=t₁ ∨ u=c₂ ∧ w=t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical u w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical u ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ((∃ back : CriticalPath d.radical geometry u (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (Z d.radical u ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
          Nat.card F ≤ (centralizer (Z d.radical u : Set (FreeAmalgam d.radical))).relIndex
            (Z d.radical z ⊓ Q d.radical a) ∧
          X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical u : Set _) ∧
          ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical u⁆,Z d.radical u⁆=⊥)) ∧
        (∀ (back : CriticalPath d.radical geometry u (path.walk.getVert 2)),
          back.walk.getVert 1=w → back.walk.getVert 2=a →
          back.walk.getVert 3=path.walk.getVert 1 →
          ∀ v s, Adjacent d.radical u s → Adjacent d.radical v s →
          (¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
            ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
              ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) →
            ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤
              centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic d geometry hb4 path.start_color hat
  have hJplane := h.replacement_small_mover_le_maximizing_plane_of_index_le d
    geometry hb4 path.start_color hat E hE f hfQ hTf hindex hmax hJm
  let D := ((((CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype).comap f).map
    (stabilizer d.radical a).subtype)
  have hJD : J ≤ D := by
    have hh := map_mono (f := (stabilizer d.radical a).subtype) hJplane
    rwa [map_subgroupOf_eq_of_le ((Subgroup.SmallMover.join_le _ _ _ _).trans
      (show Q d.radical t ≤ stabilizer d.radical a from fun _ hy => hy.2 a (adjacent_symm _ hat)))] at hh
  have hzD : Z d.radical z ≤ D :=
    (h.replacement_root_endpoint_le_small_mover d path hb4 hat hfirst hsmall
      E hE f hf hTf hindex hJplane).trans hJD
  have hfixed : Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (D : Set (FreeAmalgam d.radical)) :=
    h.replacement_small_mover_parabolic_full_fixed d geometry hb4 path.start_color hat
      E hE f hf hfQ hindex hJplane
  obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hpair,hmove₁,hmove₂,hxn,hxp,
      u,hu,w,hwhich,haw,huw,hn,hnext⟩ :=
    h.replacement_equal_smaller_selected_root_alternative d path hb4 hat hfirst hct
      hnormal hequal hsmall E hE f hf hfQ hTf hindex hquad hJplane
  have finish (u w : Vertex d.radical) (y : FreeAmalgam d.radical)
      (hy : y ∈ normalizer (D : Set (FreeAmalgam d.radical)))
      (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
          (Z d.radical z).map (MulAut.conj y).toMonoidHom = stabilizer d.radical a)
      (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
      (hback : back.walk.getVert 1=w) (hmid : back.walk.getVert 2=a)
      (hlast : back.walk.getVert 3=path.walk.getVert 1)
      (v s : Vertex d.radical) (hus : Adjacent d.radical u s) (hvs : Adjacent d.radical v s)
      (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
        ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
          ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
      ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤
        centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    let C := ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆
    have hbound : C ≤ ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ :=
      (h.replacement_distance_four_root_comparison_of_failure d path hb back hus hvs hbad).1
    have horiginal := h.replacement_distance_four_root_commutator_fixed_by_original_mover d
      path hb back hmid hlast hus hvs hbad
    rw [hfirst] at horiginal
    have hCD : C ≤ centralizer (D : Set (FreeAmalgam d.radical)) :=
      ((hbound.trans horiginal).trans hfixed.le).trans inf_le_right
    have hi := (h.replacement_distance_four_comparison_failure d path hb back hus hvs hbad).2.1
    have hsmall' : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 := by
      rw [hi]
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    have hCJ := hbound.trans
      (h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hsmall')
    rw [hback] at hCJ
    have hzDy : (Z d.radical z).map (MulAut.conj y).toMonoidHom ≤ D :=
      (map_mono hzD).trans_eq (mem_normalizer_iff_map_conj_eq.mp hy)
    have hCZ := hCD.trans (centralizer_le hzD)
    have hCZy := hCD.trans (centralizer_le hzDy)
    intro r hr
    have hJ : Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical w) (Nat.card F^2) ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCJ hr b hb)
    have hZ : Z d.radical z ≤ centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCZ hr b hb)
    have hZy : (Z d.radical z).map (MulAut.conj y).toMonoidHom ≤
        centralizer ({r} : Set (FreeAmalgam d.radical)) :=
      fun b hb => mem_centralizer_singleton_iff.mpr (hCZy hr b hb)
    intro b hb
    exact mem_centralizer_singleton_iff.mp ((sup_le (sup_le hJ hZ) hZy) (hgen.symm ▸ hb))
  refine ⟨g,hg,x,hx,u,hu,w,hwhich,haw,huw,hn,hnext,?_⟩
  rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact finish _ _ x hxn hgen₁
  · exact finish _ _ x⁻¹ ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxn) hgen₂

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
