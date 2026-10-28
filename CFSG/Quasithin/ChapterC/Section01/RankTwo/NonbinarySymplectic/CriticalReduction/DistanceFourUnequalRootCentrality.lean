module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootCentrality

/-!
# The actual unequal first selector fixes the whole backward root

The unequal individual selector retains its own residual generation clause.
For a compatible root backward critical path, the whole critical commutator
lies in the original seed and fixes the selected neighbor's original mover.
It also fixes the original endpoint seed by the literal distance-two overlap.
Those same generators and the full original core therefore centralize the
commutator at the original vertex, retaining all central attachments.

Every clause of the original unequal selector remains attached to the same
g. The small backward image is an intermediate case, forced by comparison
failure or by a trapped second selector. Source: MS93 (5.12)(1), p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem first_root_centrality
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hback : back.walk.getVert 1=w) (hmid : back.walk.getVert 2=a)
    (hlast : back.walk.getVert 3=path.walk.getVert 1)
    (hroot : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2)
    (hres : Ltilde d.radical a ≤
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u) (Q d.radical w)
        (Nat.card F^2) ⊔ Z d.radical z) :
    ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  let e := path.walk.getVert 2
  let T := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hTZa : T ≤ Z d.radical a :=
    (h.replacement_distance_four_root_original_fixed d path hb back hmid hlast hroot).trans inf_le_left
  have hTJ : T ≤ centralizer (Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
    have hh := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hroot
    rwa [hback] at hh
  have hez : (cosetGraph d.radical).dist e z=2 := by
    dsimp only [e]
    rw [path.dist_end,path.length_eq_b,hb]
  have hZeQz : Z d.radical e ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e back.end_color)
    rw [geometry.distance_constant e back.end_color,hez]
    change 2 < geometry.b d.radical
    omega
  have hTZz : T ≤ centralizer (Z d.radical z : Set (FreeAmalgam d.radical)) :=
    ((critical_commutator_le_endpoint_seed back).trans hZeQz).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes z path.end_color)))
  have hTL : T ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hres.trans (sup_le (le_centralizer_iff.mp hTJ)
      (le_centralizer_iff.mp hTZz)))
  have hTQ : T ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
    hTZa.trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color))
  have hwhole : Ltilde d.radical a ⊔ Q d.radical a=stabilizer d.radical a := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
      d.radical (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb4,←MonoidHom.range_eq_map,hir]
  apply le_centralizer_iff.mp
  rw [←hwhole]
  exact sup_le (le_centralizer_iff.mp hTL) (le_centralizer_iff.mp hTQ)

/-- One actual unequal first selector retains all its original clauses and
centralizes the entire root commutator of every compatible backward path.
The residual generation is supplied by that same selector, with no caller
fixedness or generation assumption. -/
theorem Input.replacement_distance_four_unequal_first_root_centrality
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
      (Q d.radical t) (Nat.card F^2) ≠ Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2)) :
    ∃ g ∈ Ltilde d.radical a,
      let w := act d.radical g⁻¹ t
      let v := act d.radical g⁻¹ c
      let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2)
      let Ja := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical w) (Nat.card F^2)
      let Ec := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical w) (Nat.card F^2)
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical v) =
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ∧
      J.map (MulAut.conj g).toMonoidHom =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical w) (Nat.card F^2) ⊔
        Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical w) (Nat.card F^2) ∧
      J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z = stabilizer d.radical a ∧
      Ltilde d.radical a ≤ Ec ⊔ Z d.radical z ∧
      Z d.radical t ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      Z d.radical t ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
        Z d.radical t ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) ∧
      ⁅⁅U d.radical a,Ja⁆,Ja⁆ = ⊥ ∧ ⁅⁅U d.radical v,Ec⁆,Ec⁆ = ⊥ ∧
      (centralizer (Ec : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) = Nat.card F^3 ∧
      ¬ Q d.radical a ≤ Ec ∧ Nat.card F^2 < (Q d.radical a).relIndex Ec ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ((∃ back : CriticalPath d.radical geometry v (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = w ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i) ∨
      (Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) ∧
        (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
        (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
        Nat.card F ≤ (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (Z d.radical z ⊓ Q d.radical a) ∧
        X d.radical z ⊓ Q d.radical a ≤ normalizer (Z d.radical v : Set _) ∧
        ⁅⁅X d.radical z ⊓ Q d.radical a,Z d.radical v⁆,Z d.radical v⁆ = ⊥)) ∧
      (∀ (back : CriticalPath d.radical geometry v (path.walk.getVert 2)),
        back.walk.getVert 1=w → back.walk.getVert 2=a →
        back.walk.getVert 3=path.walk.getVert 1 →
        (Q d.radical v).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2 →
        ⁅Z d.radical v,Z d.radical (path.walk.getVert 2)⁆ ≤
          centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  obtain ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquad,hquadV,hcube,hnot,hlarge,hn,hnext⟩ :=
    h.replacement_unequal_individual_generation_root_at_neighbor d path (by omega)
      hat hfirst hct hnormal hsmall hne
  refine ⟨g,hg,haw,hvw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquad,hquadV,hcube,hnot,hlarge,hn,hnext,?_⟩
  intro back hback hmid hlast hroot
  exact first_root_centrality h d path hb back hback hmid hlast hroot hres

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
