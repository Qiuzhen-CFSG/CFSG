module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeOffenders

/-!
# Coordinated choices in the original binary symplectic source

Every incident edge has its full kernel as maximal-offender join. This makes
the first component-generation alternative of MS93 (5.5)(c) follow from the
same neighbor generation used in (a). The exceptional critical-image split
is impossible, so the source tilde Z is exactly the original Z-layer.

Local transitivity transports the prescribed delta to the selected edge.
The identity element of the actual component then satisfies both generating
equations, both seed-center bounds, and the first alternative of (c), all on
that same transported vertex. The resulting two-vertex set is the exact
A_delta witness used by (5.7). Its backward critical noncontainment remains
the next source argument; no core equality is asserted here.

Source: Meierfrankenfeld--Stellmacher (1993), (5.5), pp.915--917, and the
notation preceding (5.7), p.919; Aschbacher--Smith C.1.37 and 13.7.4(1).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal]
namespace Source
variable (s : Source L R W)

/-- The source tilde Z: in the exceptional split-image case centralize one
of the two transvection preimages, and otherwise retain the whole Z-layer. -/
noncomputable def selectedCriticalLayer (a e : Vertex R) : Subgroup (FreeAmalgam R) := by
  classical
  exact if h : SplitCriticalImage a e then
    Z R e ⊓ centralizer ((Classical.choose h : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) else Z R e

theorem selectedCriticalLayer_eq (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {a e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry a e) :
    selectedCriticalLayer a e = Z R e := by
  classical
  simp only [selectedCriticalLayer,dif_neg (s.critical_image_not_split h u hfull p)]

/-- The simultaneous source (5.5) choices, in its first (c) alternative.
The orbit representative and conjugator are shared by every clause. -/
structure CoordinatedChoice {e : Vertex R}
    (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (delta : Vertex R) where
  beta1 : Vertex R
  transporter : FreeAmalgam R
  transporter_mem : transporter ∈ stabilizer R (alpha R)
  transporter_seed : act R transporter (p.walk.getVert 1) = beta1
  alpha1 : Vertex R
  alpha1_eq : alpha1 = act R transporter delta
  adjacent_start : Adjacent R (alpha R) beta1
  adjacent_back : Adjacent R alpha1 beta1
  x : FreeAmalgam R
  x_mem : x ∈ Ltilde R (alpha R)
  generation : Q R beta1 ⊔ selectedCriticalLayer (alpha R) e = stabilizer R (alpha R)
  generation_conjugate : (Q R beta1).map (MulAut.conj x⁻¹).toMonoidHom ⊔
    selectedCriticalLayer (alpha R) e = stabilizer R (alpha R)
  seed_fixer : Z R (p.walk.getVert 1) ⊓
    centralizer (edgeOffenderJoin (alpha R) beta1 : Set (FreeAmalgam R)) ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype
  seed_fixer_conjugate : Z R (p.walk.getVert 1) ⊓
    centralizer ((edgeOffenderJoin (alpha R) beta1).map
      (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam R)) ≤
    (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype
  component_generation : Ltilde R (alpha R) ≤
    (edgeOffenderJoin alpha1 beta1 ⊔ selectedCriticalLayer (alpha R) e) ⊓
    ((edgeOffenderJoin alpha1 beta1).map (MulAut.conj x⁻¹).toMonoidHom ⊔
      selectedCriticalLayer (alpha R) e)

theorem exists_coordinatedChoice (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    {e : Vertex R} (p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e)
    (delta : Vertex R) (hdelta : Adjacent R delta (p.walk.getVert 1)) :
    Nonempty (s.CoordinatedChoice p delta) := by
  have hpoint : R.map s.projection =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj u).toMonoidHom := by
    simpa only [Model.pointCore_eq_exceptional] using hfull
  obtain ⟨t,ht,hgen,hfix⟩ := s.exists_generating_neighbor_and_seed_fixer h u hpoint p
  have hpos : 0 < p.walk.length := p.length_eq_b ▸ s.criticalDistance_pos
  have hb : Adjacent R (alpha R) (p.walk.getVert 1) := by
    apply (cosetGraph_adj R _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using p.walk.adj_getVert_succ (i := 0) hpos
  obtain ⟨g,hg,hgt⟩ := stabilizer_transitive_neighbors R (alpha R) hb ht
  have hadj : Adjacent R (act R g delta) t := by
    rw [←hgt]
    exact (adjacent_act_iff R g delta (p.walk.getVert 1)).mpr hdelta
  have hdcol : color R (act R g delta) = false := by
    have h1 := adjacent_color_ne R ht
    have h2 := adjacent_color_ne R hadj
    change false ≠ color R t at h1
    cases hc : color R (act R g delta) <;> cases hc' : color R t <;> simp_all
  have hj := s.edgeOffenderJoin_eq h u hfull rfl ht
  have hj' := s.edgeOffenderJoin_eq h u hfull hdcol hadj
  have htilde := s.selectedCriticalLayer_eq h u hfull p
  have hcenter : Z R (p.walk.getVert 1) ⊓ centralizer (Q R t : Set (FreeAmalgam R)) ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype := by
    intro z hz
    have hzG := ((DistanceEight.PathCentrality.adjacent_Z_le R rfl hb).trans
      (Z_le_stabilizer R (alpha R))) hz.1
    refine ⟨⟨z,hzG⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hfix hz y y.property
  have hc1 : (MulAut.conj (1 : FreeAmalgam R)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro a
    change 1 * a * (1 : FreeAmalgam R)⁻¹ = a
    simp only [inv_one,one_mul,mul_one]
  refine ⟨{
    beta1 := t
    transporter := g
    transporter_mem := hg
    transporter_seed := hgt
    alpha1 := act R g delta
    alpha1_eq := rfl
    adjacent_start := ht
    adjacent_back := hadj
    x := 1
    x_mem := one_mem _
    generation := ?_
    generation_conjugate := ?_
    seed_fixer := ?_
    seed_fixer_conjugate := ?_
    component_generation := ?_
  }⟩
  · simpa only [htilde] using hgen
  · simpa only [inv_one,hc1,map_id,htilde] using hgen
  · simpa only [hj] using hcenter
  · simpa only [inv_one,hc1,map_id,hj] using hcenter
  · simp only [inv_one,hc1,map_id,hj',htilde,hgen,inf_idem]
    exact map_subtype_le _

/-- The source set A_delta for one fixed coordinated choice. The second
vertex is alpha1^x, with the same x appearing in every generation clause. -/
def CoordinatedChoice.backwardVertices {e : Vertex R}
    {p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e}
    {delta : Vertex R} (c : s.CoordinatedChoice p delta) : Set (Vertex R) :=
  {c.alpha1,act R c.x c.alpha1}

theorem CoordinatedChoice.backwardVertices_nonempty {e : Vertex R}
    {p : DistanceEight.PathCentrality.CriticalPath R s.geometry (alpha R) e}
    {delta : Vertex R} (c : s.CoordinatedChoice p delta) : c.backwardVertices.Nonempty :=
  ⟨c.alpha1,Or.inl rfl⟩

end Source
namespace SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (h : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original source supplies the complete coordinated choice or its final
alternating block; neither the full-image nor a tilde-layer premise remains. -/
theorem reducedSource_block_or_coordinatedChoice
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : DistanceEight.PathCentrality.CriticalPath r.radical
      ((originalSource d h).reduce r).geometry (alpha r.radical) e)
    (delta : Vertex r.radical) (hdelta : Adjacent r.radical delta (p.walk.getVert 1)) :
    IsAlternatingBlock L 6 ∨
      Nonempty (((originalSource d h).reduce r).CoordinatedChoice p delta) := by
  rcases reducedSource_block_or_full_point_image d h r with hb | hf
  · exact Or.inl hb
  · apply Or.inr
    apply Source.exists_coordinatedChoice ((originalSource d h).reduce r)
      (reduced_nativeCentralLayer d h r) d.relabeler.val⁻¹ _ p delta hdelta
    simpa only [Model.pointCore_eq_exceptional] using hf
end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
