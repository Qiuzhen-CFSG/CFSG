module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2Generation
public import Theory.AtlasPort.LinearGroups.G2.ParabolicApartment
public import Theory.AtlasPort.LinearGroups.G2.ParabolicLocalOrder
public import Theory.GroupAction.RankTwoCosetGeometry.AlternatingSeven
public import Theory.GroupAction.RankTwoCosetGeometry.Valence
public import Theory.GroupAction.RankTwoCosetGeometry.PathCardinality
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.SevenGirth
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.HexagonRecognition
public import Theory.GroupAction.DihedralPolygon
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.Pair
public import Theory.GroupAction.RankTwoCosetCover.SmallCover

/-!
# Geometry and recognition of the prepared G₂ completion

The actual octonion parabolics have (q+1)q⁶ nonbacktracking seven-paths
from either vertex. The alternating Weyl path has fixer in the split torus,
of order (q-1)². Orbit–stabilizer proves seven-path transitivity, which
transfers through the universal amalgam's whole-overlap coset coverings.
Consequently the actual ambient pair has valence q+1 and girth at least twelve.

Matching endpoint involutions satisfying the hexagon relation in two
completions produce a twelve-cycle in their paired completion. Seven-path
transitivity bounds its diameter by six; the two short-cover projections
are therefore injective, giving an actual group isomorphism. The canonical
native Weyl relation is verified in octonion coordinates.

The source application retains both original parabolic maps and the entire
Borel. It proves the geometric conclusions without an extra premise and
reduces concrete G₂ recognition to the explicit canonical Weyl relation.
That relation, exhaustive F.1.12 comparison and original uniqueness remain
obligations of the generic-global assembly. The Chapter12 companion gives
the actual rank-two output at the original exponent n>1 under that relation.

Source: Aschbacher–Smith F.3.3–6, F.4.6 and F.4.8, printed pp.270–278,
and their use in 5.3.3–4, p.659 (`refs/quasithin.pdf`). The native calculation
generalizes the ternary source-completion argument already in ChapterF;
the imported octonion coordinates retain LICENSES/ATLAS.txt attribution.
-/

open Theory.GroupTheory Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open SimpleGraph SimpleGraph.PathTransitivePolygon
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry.Native
variable (F : Type) [Field F]
local notation "q" => Nat.card F
abbrev MG := Model F
def family : Bool → Subgroup (MG F) := fun i => if i then parabolic₂ else parabolic₁
def first (i : Bool) : MG F := if i then weylR else weylS
def second (i : Bool) : MG F := if i then weylS else weylR

theorem first_mem (i : Bool) : first F i ∈ family F i := by
  cases i
  · exact mem_sup_right (subset_closure (by simp [first]))
  · exact weylR_mem_parabolic

theorem second_mem (i : Bool) : second F i ∈ family F (!i) := by
  cases i
  · exact weylR_mem_parabolic
  · exact mem_sup_right (subset_closure (by simp [second]))

private theorem weylS_not_mem : (weylS : MG F) ∉ parabolic₂ := by
  intro h
  obtain ⟨a,ha⟩ := (mem_pointStabilizer_iff _).mp (parabolic_le_pointStabilizer h)
  have hh := congrFun ha 1
  simp [weylS,weylSEquiv,weylSLinear,weylSApply,basisVector] at hh
private theorem weylR_not_mem : (weylR : MG F) ∉ parabolic₁ := by
  intro h
  have hh := (parabolic₁_le_shortPlaneStabilizer h).1 (basisVector 1)
    (basis_mem_shortPlane 1 (by decide)) 2 (by decide)
  change (-1 : F) = 0 at hh
  exact neg_ne_zero.mpr one_ne_zero hh

theorem first_not_mem (i : Bool) : first F i ∉ family F (!i) := by
  cases i
  · exact weylS_not_mem F
  · exact weylR_not_mem F

theorem second_not_mem (i : Bool) : second F i ∉ family F i := by
  cases i
  · exact weylR_not_mem F
  · exact weylS_not_mem F

theorem longest (i : Bool) : second F i * first F i * second F i * first F i * second F i * first F i =
    ParabolicApartment.longest := by
  cases i
  · simp only [first,second,Bool.false_eq_true,↓reduceIte,ParabolicApartment.longest,pow_succ,
      pow_zero,one_mul,mul_assoc]
  · have hr : (weylR : MG F)⁻¹=weylR := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylR_sq (K := F)))
    have hs : (weylS : MG F)⁻¹=weylS := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using (weylS_sq (K := F)))
    rw [←ParabolicApartment.longest_inv]
    simp only [first,second,↓reduceIte,ParabolicApartment.longest,
      mul_inv_rev,hr,hs,pow_succ,pow_zero,one_mul,mul_assoc]

theorem family_intersection (i : Bool) : family F i ⊓ family F (!i) = Atlas.G2.borel := by
  cases i
  · exact parabolics_intersection
  · exact (inf_comm _ _).trans parabolics_intersection

def path (i : Bool) : BasedWalk (graph (family F)) 7 (RankTwo.base (family F) i) :=
  alternatingSeven (family F) i (first F i) (second F i) (first_mem F i) (second_mem F i)

theorem path_nonbacktracking (i : Bool) : (path F i).Nonbacktracking :=
  alternatingSeven_nonbacktracking (family F) i (first F i) (second F i)
    (first_mem F i) (second_mem F i) (first_not_mem F i) (second_not_mem F i)

theorem path_fixer_le (i : Bool) : pathStabilizer (family F) (path F i) ≤ splitTorus := by
  have h := alternatingSeven_fixer_le (family F) i (first F i) (second F i)
    (first_mem F i) (second_mem F i)
  rw [family_intersection,longest,ParabolicApartment.longest_inv] at h
  exact h.trans ParabolicApartment.opposite_borel_le_torus

variable [Finite F]

theorem path_fixer_card_le (i : Bool) : Nat.card (pathStabilizer (family F) (path F i)) ≤ (q-1)^2 := by
  have h := Nat.card_le_card_of_injective (Subgroup.inclusion (path_fixer_le F i))
    (Subgroup.inclusion_injective (path_fixer_le F i))
  rw [card_splitTorus] at h
  exact h

theorem family_card (i : Bool) : Nat.card (family F i) = (q+1)*(q^6*(q-1)^2) := by
  cases i
  · change Nat.card (parabolic₁ (F := F)) = _
    rw [ParabolicCells.short_card,card_borel]
  · change Nat.card (parabolic₂ (F := F)) = _
    rw [card_parabolic]
    ring

theorem base_neighbor_card (i : Bool) :
    Nat.card ((graph (family F)).neighborSet (RankTwo.base (family F) i)) = q+1 := by
  rw [card_neighbor_base]
  have hidx := ((family F (!i)).subgroupOf (family F i)).card_mul_index
  have hmid : Nat.card ((family F (!i)).subgroupOf (family F i)) = Nat.card (Atlas.G2.borel (K := F)) := by
    rw [←Subgroup.inf_subgroupOf_right]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv,inf_comm,
      family_intersection]
  rw [hmid,card_borel,family_card] at hidx
  have hb : 0 < q^6*(q-1)^2 := by
    have hq : 0 < q := Nat.card_pos
    have hsub : 0 < q-1 := Nat.sub_pos_of_lt Finite.one_lt_card
    positivity
  apply Nat.eq_of_mul_eq_mul_left hb
  exact hidx.trans (Nat.mul_comm _ _)

theorem neighbor_card (v : RankTwo.Vertex (family F)) : Nat.card ((graph (family F)).neighborSet v) = q+1 := by
  obtain ⟨g,hg⟩ := exists_smul_base (family F) v
  have hh := Nat.card_congr ((translationGraphIso (family F) g).mapNeighborSet (RankTwo.base (family F) v.type))
  change Nat.card ((graph (family F)).neighborSet (RankTwo.base (family F) v.type)) =
    Nat.card ((graph (family F)).neighborSet (g • RankTwo.base (family F) v.type)) at hh
  rw [hg] at hh
  rw [←hh]
  exact base_neighbor_card F v.type

theorem seven_path_card (i : Bool) :
    Nat.card {p : BasedWalk (graph (family F)) 7 (RankTwo.base (family F) i) // p.Nonbacktracking} = (q+1)*q^6 := by
  have (x : RankTwo.Vertex (family F)) : Finite ((graph (family F)).neighborSet x) :=
    Nat.finite_of_card_ne_zero (by rw [neighbor_card F]; positivity)
  have hf : ∀ {x y : RankTwo.Vertex (family F)}, (graph (family F)).Adj x y → y.type = !x.type := by
    intro x y h
    have hxy := h.1
    cases hx : x.type <;> cases hy : y.type <;> simp_all
  have hc := BasedWalk.card_nonbacktracking_succ (graph (family F))
    (fun x : RankTwo.Vertex (family F) => x.type) (fun _ => q+1) hf (neighbor_card F) 6 (RankTwo.base (family F) i)
  simpa only [BasedWalk.forwardCount, Nat.add_sub_cancel, pow_succ, pow_zero, mul_one, one_mul,
    mul_assoc] using hc

theorem seven_path_transitive (i : Bool) :
    RootPathTransitive (graph (family F)) (MG F) (RankTwo.base (family F) i) 7 := by
  have : Finite {p : BasedWalk (graph (family F)) 7 (RankTwo.base (family F) i) // p.Nonbacktracking} :=
    Nat.finite_of_card_ne_zero (by rw [seven_path_card F]; have : 0 < q := Nat.card_pos; positivity)
  apply rootPathTransitive_of_pathStabilizer_card_le (family F) (path F i)
    (path_nonbacktracking F i) (by have : 0 < q-1 := Nat.sub_pos_of_lt Finite.one_lt_card; positivity : 0 < (q-1)^2) (path_fixer_card_le F i)
  rw [stabilizer,stabilizer_base,family_card,seven_path_card]
  ring
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry.Native

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry
variable {F : Type} [Field F]
abbrev Completion (F : Type) [Field F] (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)) (G := G)

def modelCompletion : Completion F (Model F) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    parabolic₁ (parabolic₁ ⊓ parabolic₂) parabolic₂ inf_le_left inf_le_right parabolics_generate

theorem model_overlap : (modelCompletion (F := F)).left.range ⊓ modelCompletion.right.range =
    modelCompletion.middle.range := by
  change parabolic₁.subtype.range ⊓ parabolic₂.subtype.range =
    (parabolic₁ (F := F) ⊓ parabolic₂).subtype.range
  simp only [range_subtype]

theorem model_family : (modelCompletion (F := F)).cosetFamily = Native.family F := by
  funext i
  cases i <;> exact range_subtype _

namespace Completion
variable {G : Type*} [Group G] (c : Completion F G)
local notation "q" => Nat.card F
abbrev Vertex := RankTwo.Vertex c.cosetFamily
abbrev graph := RankTwo.graph c.cosetFamily

theorem connected : c.graph.Connected := RankTwo.connected c.cosetFamily c.generated

theorem graphAction : GraphAction c.graph G where
  map_adj g := (translationGraphIso c.cosetFamily g).toHom.map_adj

variable [Finite F]

theorem seven_transitive (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (v : c.Vertex) : RootPathTransitive c.graph G v 7 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hm : RootPathTransitive (graph (modelCompletion (F := F))) (Model F)
      (RankTwo.base modelCompletion.cosetFamily v.type) 7 := by
    change RootPathTransitive (RankTwo.graph modelCompletion.cosetFamily) _ _ _
    rw [model_family]
    exact Native.seven_path_transitive F _
  have hb := (RankTwoAmalgam.Universal.rootPathTransitive_iff_of_overlap
    _ c modelCompletion hc model_overlap v.type 7).mpr hm
  simpa only [hg] using RootPathTransitive.smul c.graphAction hb g

theorem card_neighbors (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (v : c.Vertex) : Nat.card (c.graph.neighborSet v) = q+1 := by
  obtain ⟨g,hg⟩ := exists_smul_base c.cosetFamily v
  have hbase : Nat.card (c.graph.neighborSet (RankTwo.base c.cosetFamily v.type)) = q+1 := by
    have cover := RankTwoAmalgam.Universal.coverData_of_overlap _ c hc
    have native := RankTwoAmalgam.Universal.coverData_of_overlap _
      (modelCompletion (F := F)) model_overlap
    have h1 := Nat.card_congr (Equiv.ofBijective _
      (cover.neighbor_bijective (RankTwo.base _ v.type)))
    have h2 := Nat.card_congr (Equiv.ofBijective _
      (native.neighbor_bijective (RankTwo.base _ v.type)))
    change Nat.card _ = Nat.card ((RankTwo.graph c.cosetFamily).neighborSet
      (cover.vertex (RankTwo.base _ v.type))) at h1
    change Nat.card _ = Nat.card ((RankTwo.graph modelCompletion.cosetFamily).neighborSet
      (native.vertex (RankTwo.base _ v.type))) at h2
    rw [CoverData.vertex_base] at h1 h2
    rw [←h1,h2,model_family]
    exact Native.base_neighbor_card F v.type
  have hh := Nat.card_congr
    ((translationGraphIso c.cosetFamily g).mapNeighborSet (RankTwo.base c.cosetFamily v.type))
  change Nat.card (c.graph.neighborSet (RankTwo.base c.cosetFamily v.type)) =
    Nat.card (c.graph.neighborSet (g • RankTwo.base c.cosetFamily v.type)) at hh
  rw [hg] at hh
  exact hh.symm.trans hbase

theorem thick (hc : c.left.range ⊓ c.right.range = c.middle.range) (v a b : c.Vertex) : ∃z,c.graph.Adj v z ∧ z≠a ∧ z≠b := by
  classical
  let : Finite (c.graph.neighborSet v) := Nat.finite_of_card_ne_zero
    (by rw [c.card_neighbors hc]; positivity)
  let := Fintype.ofFinite (c.graph.neighborSet v)
  have hc : 2 < Fintype.card (c.graph.neighborSet v) := by
    rw [←Nat.card_eq_fintype_card,c.card_neighbors hc]
    have : 1 < q := Finite.one_lt_card
    omega
  obtain ⟨x,y,z,hxy,hxz,hyz⟩ := Fintype.two_lt_card_iff.mp hc
  by_contra hh
  push Not at hh
  have hx : x.val=a ∨ x.val=b := by
    by_cases ha : x.val=a
    · exact Or.inl ha
    · exact Or.inr (hh x.val x.property ha)
  have hy : y.val=a ∨ y.val=b := by
    by_cases ha : y.val=a
    · exact Or.inl ha
    · exact Or.inr (hh y.val y.property ha)
  have hz : z.val=a ∨ z.val=b := by
    by_cases ha : z.val=a
    · exact Or.inl ha
    · exact Or.inr (hh z.val z.property ha)
  have hxy' : x.val≠y.val := fun h => hxy (Subtype.ext h)
  have hxz' : x.val≠z.val := fun h => hxz (Subtype.ext h)
  have hyz' : y.val≠z.val := fun h => hyz (Subtype.ext h)
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;> simp_all

theorem hasTwoNeighbors (hc : c.left.range ⊓ c.right.range = c.middle.range) : BasedWalk.HasTwoNeighbors c.graph := by
  intro v a
  obtain ⟨z,hz,hza,_⟩ := c.thick hc v a a
  exact ⟨z,hz,hza⟩

theorem cycle_length_ge_twelve (hc : c.left.range ⊓ c.right.range = c.middle.range) (v : c.Vertex) (p : c.graph.Walk v v) (hp : p.IsCycle) :
    12≤p.length :=
  cycle_bound_of_seven_transitive c.graphAction (c.thick hc) (c.seven_transitive hc)
    (·.type) (fun h => h.1) v p hp

end Completion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry.Completion
variable {F : Type} [Field F] [Finite F]
variable {G : Type*} [Group G] (c : Completion F G)
open HexagonRecognition
theorem uniqueGeodesicsBelow_six (hc : c.left.range ⊓ c.right.range = c.middle.range) : c.graph.UniqueGeodesicsBelow 6 := by
  intro x y p q hp hq hd
  by_contra hh
  obtain ⟨v,_,_,r,hr,hlen⟩ := (p.isPath_of_length_eq_dist hp).exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hh
  have hb := c.cycle_length_ge_twelve hc v r hr
  omega

def bipartiteAction : GroupAction.DihedralPolygon.BipartiteAction G c.graph where
  color := (·.type)
  adjacent_color h := h.1
  smul_adj := c.graphAction.map_adj
  smul_color _ _ := rfl

theorem exists_twelve_cycle_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    ∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12 := by
  have hsx : s • RankTwo.base c.cosetFamily false=RankTwo.base c.cosetFamily false := by
    change s∈stabilizer c.cosetFamily (RankTwo.base c.cosetFamily false)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_false] using hs
  have htl : t • RankTwo.base c.cosetFamily true=RankTwo.base c.cosetFamily true := by
    change t∈stabilizer c.cosetFamily (RankTwo.base c.cosetFamily true)
    simpa only [stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_true] using ht
  have hsl : s • RankTwo.base c.cosetFamily true≠RankTwo.base c.cosetFamily true := by
    intro hh
    have hh' : s∈c.right.range := by
      change s∈stabilizer c.cosetFamily (RankTwo.base c.cosetFamily true) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_true] using hh
    exact hsout (hc ▸ show s∈c.left.range⊓c.right.range from ⟨hs,hh'⟩)
  have htx : t • RankTwo.base c.cosetFamily false≠RankTwo.base c.cosetFamily false := by
    intro hh
    have hh' : t∈c.left.range := by
      change t∈stabilizer c.cosetFamily (RankTwo.base c.cosetFamily false) at hh
      simpa only [stabilizer,RankTwo.base,stabilizer_base,RankTwoAmalgam.FaithfulCompletion.cosetFamily, Bool.cond_false] using hh
    exact htout (hc ▸ show t∈c.left.range⊓c.right.range from ⟨hh',ht⟩)
  let e : cycleGraph 12 ↪g c.graph := GroupAction.DihedralPolygon.edgeEmbedding c.bipartiteAction
    (by decide : 1<6) (c.uniqueGeodesicsBelow_six hc) (by decide : 0<6) le_rfl
    ⟨Bool.false_ne_true,incident_base c.cosetFamily false true⟩ hs2 ht2 hsx hsl htl htx
    (by rw [hst,one_smul]) (by rw [hst,one_smul])
  exact (cycleGraph_isContained_iff (by decide : 2<12)).mp ⟨e.toCopy⟩

theorem hexagon_metric_of_involutions (hc : c.left.range ⊓ c.right.range = c.middle.range) (s t : G)
    (hs : s∈c.left.range) (ht : t∈c.right.range)
    (hsout : s∉c.middle.range) (htout : t∉c.middle.range)
    (hs2 : s^2=1) (ht2 : t^2=1) (hst : (s*t)^6=1) :
    (∀v (p : c.graph.Walk v v),p.IsCycle → 12≤p.length) ∧
    (∀v w,c.graph.dist v w≤6) ∧
    (∃v,∃p : c.graph.Walk v v,p.IsCycle ∧ p.length=12) := by
  have hex := c.exists_twelve_cycle_of_involutions hc s t hs ht hsout htout hs2 ht2 hst
  refine ⟨c.cycle_length_ge_twelve hc,diameter_bound_of_seven_endpoint_bound c.connected ?_,hex⟩
  intro v p hp
  exact seven_endpoint_bound c.graphAction (c.seven_transitive hc) (·.type) (fun h => h.1)
    (fun h => (same_orbit_iff c.cosetFamily _ _).mpr h) hex p hp

omit [Finite F] in
private theorem pair_overlap {H : Type*} [Group H] (d : Completion F H)
    (hc : c.left.range ⊓ c.right.range = c.middle.range) :
    (c.pairCompletion d).left.range ⊓ (c.pairCompletion d).right.range =
      (c.pairCompletion d).middle.range := by
  let e := c.pairCompletion d
  apply le_antisymm _ (le_inf e.middle_le_left e.middle_le_right)
  rintro z ⟨⟨x,hx⟩,⟨y,hy⟩⟩
  have hxy : c.left x=c.right y := by
    have he := congrArg (c.pairFst d) (hx.trans hy.symm)
    simpa only [e,RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using he
  obtain ⟨b,hb⟩ := hc.le (show c.left x∈c.left.range⊓c.right.range from
    ⟨⟨x,rfl⟩,⟨y,hxy.symm⟩⟩)
  have hbx : (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).left b=x :=
    c.left_injective hb
  exact ⟨b,by change e.left _=z; rw [hbx]; exact hx⟩

/-- Matching endpoint involutions with the hexagon relation determine the actual
completion group; the whole overlap is retained in both projections. -/
theorem nonempty_mulEquiv_of_matching_involutions {H : Type*} [Group H]
    (d : Completion F H)
    (hcO : c.left.range ⊓ c.right.range = c.middle.range)
    (hdO : d.left.range ⊓ d.right.range = d.middle.range)
    (s : parabolic₁ (F := F)) (t : parabolic₂ (F := F))
    (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hc : (c.left s*c.right t)^6=1) (hd : (d.left s*d.right t)^6=1) :
    Nonempty (G ≃* H) := by
  let e : Completion F (c.Pair d) := c.pairCompletion d
  have hes : e.left s∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply hsout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left] using hh
  have het : e.right t∉e.middle.range := by
    rintro ⟨b,hb⟩
    apply htout
    refine ⟨b,?_⟩
    have hh := congrArg (c.pairFst d) hb
    simpa only [RankTwoAmalgam.FaithfulCompletion.middle, MonoidHom.comp_apply,
      e, RankTwoAmalgam.FaithfulCompletion.pairFst_left,
      RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hh
  have he6 : (e.left s*e.right t)^6=1 := by
    apply Subtype.ext
    apply Prod.ext
    · have h : c.pairFst d ((e.left s*e.right t)^6)=c.pairFst d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairFst_left,
          RankTwoAmalgam.FaithfulCompletion.pairFst_right] using hc
      exact h
    · have h : c.pairSnd d ((e.left s*e.right t)^6)=c.pairSnd d 1 := by
        simpa only [map_pow,map_mul,map_one,e,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_left,
          RankTwoAmalgam.FaithfulCompletion.pairSnd_right] using hd
      exact h
  have heO := c.pair_overlap d hcO
  have hdiam := (e.hexagon_metric_of_involutions heO (e.left s) (e.right t)
    ⟨s,rfl⟩ ⟨t,rfl⟩ hes het (by rw [←map_pow,hs,map_one])
      (by rw [←map_pow,ht,map_one]) he6).2.1
  have hf : CoverData e.cosetFamily c.cosetFamily (c.pairFst d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairFst_left d x) (by ext x; exact c.pairFst_right d x) heO hcO
  have hg : CoverData e.cosetFamily d.cosetFamily (c.pairSnd d) :=
    RankTwoAmalgam.FaithfulCompletion.coverData_of_hom _
      (by ext x; exact c.pairSnd_left d x) (by ext x; exact c.pairSnd_right d x) heO hdO
  have hif := hf.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (c.cycle_length_ge_twelve hcO v p hp))
  have his := hg.injective_of_diameter_lt_girth e.connected hdiam
    (fun v p hp => (show (6 : ℕ) < 12 by decide).trans_le (d.cycle_length_ge_twelve hdO v p hp))
  exact ⟨(MulEquiv.ofBijective (c.pairFst d) ⟨hif,hf.surjective⟩).symm.trans
    (MulEquiv.ofBijective (c.pairSnd d) ⟨his,hg.surjective⟩)⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry.Completion

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry
variable {F : Type} [Field F]

def nativeS : parabolic₁ (F := F) :=
  ⟨weylS,mem_sup_right (subset_closure (by simp))⟩
def nativeR : parabolic₂ (F := F) := ⟨weylR,weylR_mem_parabolic⟩

private theorem native_SR_six : ((nativeS.val : Model F)*nativeR.val)^6=1 := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  funext i
  fin_cases i <;> simp [nativeS,nativeR,pow_succ,weylS,weylR,weylSEquiv,weylREquiv,
    weylSLinear,weylRLinear,weylSApply,weylRApply]

namespace Completion
variable {G : Type*} [Group G] (c : Completion F G)

/-- Recognition needs the explicit Weyl relation, rather than a group-isomorphism
or polygon certificate. The native relation and all common-cover geometry are proved. -/
theorem nonempty_mulEquiv_of_weyl [Finite F]
    (hc : c.left.range ⊓ c.right.range = c.middle.range)
    (hweyl : (c.left nativeS*c.right nativeR)^6=1) :
    Nonempty (G ≃* Model F) := by
  apply c.nonempty_mulEquiv_of_matching_involutions modelCompletion hc model_overlap
    nativeS nativeR (Subtype.ext weylS_sq) (Subtype.ext weylR_sq) _ _ hweyl native_SR_six
  · rintro ⟨b,hb⟩
    have he := c.left_injective hb
    apply Native.first_not_mem F false
    change (weylS : Model F) ∈ parabolic₂
    have he' : b.val=weylS := congrArg Subtype.val he
    exact he' ▸ b.property.2
  · rintro ⟨b,hb⟩
    have he := c.right_injective ((DFunLike.congr_fun c.compatible b).symm.trans hb)
    apply Native.first_not_mem F true
    change (weylR : Model F) ∈ parabolic₁
    have he' : b.val=weylR := congrArg Subtype.val he
    exact he' ▸ b.property.1
end Completion
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2CompletionGeometry

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open G2CompletionGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}

/-- The actual ambient pair has seven-path transitivity and no cycle shorter
than twelve, with both original maps retained. The last implication isolates
the remaining Weyl relation for concrete completion recognition. -/
theorem Preparation.g2_ambient_completion_geometry
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse) :
    ∃ c : G2CompletionGeometry.Completion F G,
      c.left = (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 1).subtype.comp
        e.right.symm.toMonoidHom ∧
      c.right = (ChapterF.Source.parabolic ![L,residual H] (sourceS L H) 0).subtype.comp
        e.left.symm.toMonoidHom ∧
      c.middle.range = ChapterF.Source.commonBorel ![L,residual H] (sourceS L H) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      (∀ v, RootPathTransitive c.graph G v 7) ∧
      (∀ v (p : c.graph.Walk v v), p.IsCycle → 12≤p.length) ∧
      ((c.left nativeS*c.right nativeR)^6=1 → Nonempty (G ≃* Model F)) := by
  obtain ⟨c,hl,hr,hm,ho⟩ := d.g2_ambient_completion h hH hp F e
  let c' : G2CompletionGeometry.Completion F G := {
    left := c.right
    right := c.left
    compatible := c.compatible.symm
    left_injective := c.right_injective
    right_injective := c.left_injective
    middle_injective := by
      change Function.Injective (c.right.comp
        (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse.right)
      rw [←c.compatible]
      exact c.middle_injective
    generated := by rw [sup_comm]; exact c.generated }
  have hmid : c'.middle=c.middle := c.compatible.symm
  have hwhole : c'.left.range ⊓ c'.right.range=c'.middle.range := by
    rw [hmid]
    exact (inf_comm _ _).trans ho
  exact ⟨c',hr,hl,(congrArg MonoidHom.range hmid).trans hm,hwhole,
    c'.seven_transitive hwhole,c'.cycle_length_ge_twelve hwhole,
    c'.nonempty_mulEquiv_of_weyl hwhole⟩

/-- The literal canonical Weyl relation discharges completion recognition
for the original prepared G₂ pair, at the same field as its parabolic maps. -/
theorem Preparation.g2_ambient_recognition_of_weyl
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.G2.amalgam (F := F)).reverse)
    (hweyl : ((e.right.symm (nativeS (F := F))).val *
      (e.left.symm (nativeR (F := F))).val)^6=1) :
    Nat.card F=2^n ∧ Nonempty (G ≃* Model F) := by
  obtain ⟨c,hl,hr,_,_,_,_,hc⟩ := d.g2_ambient_completion_geometry h hH hp F e
  refine ⟨(d.g2_local_structure h hH.1.1.2 hp F (Or.inr ⟨e⟩)).1,hc ?_⟩
  simpa only [hl,hr,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,coe_subtype] using hweyl
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
