module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedKernelVanishing
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StrictIndexPathSelection
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# Prescribed equal-root escape under radius fixedness

Reverse the actual path, extend it backward, and reverse again to obtain a
true forward extension. The original path is its compatible backward path.
The source-correct full Q_a comparison then excludes trapping of the SAME
endpoint-nonnormal root selector at the prescribed midpoint. The complete
original marking, both residual conjugators, both triples, whole fixed
identity, plane placement and all actual path overlaps are retained.

Source: the prescribed first choice in MS93 (5.12), pp.924 and926--927.
No transitivity on punctured neighbor sets or unmarked endpoint orbit is used.
The internal import reuses transport of actual radius fixedness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem actual_forward_extension
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    ∃ w, ∃ next : CriticalPath d.radical geometry (path.walk.getVert 2) w,
      next.walk.getVert 2=z := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev := (show CriticalSegment geometry from ⟨a,z,path⟩).reverse hedge (by omega)
  obtain ⟨w,b,hover⟩ := h.replacement_critical_backward_extension d rev.path (by omega)
  have he : rev.path.walk.getVert (rev.path.walk.length-2)=path.walk.getVert 2 := by
    change path.walk.reverse.getVert (path.walk.reverse.length-2)=_
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,path.length_eq_b,hb]
  let q := (show CriticalSegment geometry from ⟨w,_,b⟩).reverse hedge (by omega)
  have hqfirst : q.first=path.walk.getVert 2 := he
  have hqlast : q.last=w := rfl
  let next : CriticalPath d.radical geometry (path.walk.getVert 2) w := {
    start_color := by rw [←hqfirst]; exact q.path.start_color
    walk := q.path.walk.copy hqfirst hqlast
    shortest := by rw [SimpleGraph.Walk.length_copy,←hqfirst,←hqlast]; exact q.path.shortest
    critical := by simpa only [hqfirst,hqlast] using q.path.critical }
  refine ⟨w,next,?_⟩
  change (q.path.walk.copy hqfirst hqlast).getVert 2=z
  rw [SimpleGraph.Walk.getVert_copy]
  change b.walk.reverse.getVert 2=z
  rw [SimpleGraph.Walk.getVert_reverse,b.length_eq_b,hb]
  have hh := hover 0 (by rw [rev.path.length_eq_b,hb]; omega)
  simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at hh
  change b.walk.getVert 2=z at hh
  exact hh

private theorem prescribed_selector_not_trapped
    {geometry : Geometry d.radical} {a z v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (has : Adjacent d.radical a s) (hvs : Adjacent d.radical v s)
    (r : FreeAmalgam d.radical) (hr : r ∈ Ltilde d.radical a)
    (hrv : act d.radical r (path.walk.getVert 2)=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ¬ Z d.radical v ≤ Q d.radical (path.walk.getVert 2) := by
  intro htrap
  obtain ⟨w,next,hnext⟩ := actual_forward_extension h d path hb
  let back : CriticalPath d.radical geometry a (next.walk.getVert 2) := {
    start_color := path.start_color
    walk := path.walk.copy rfl hnext.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hnext]; exact path.shortest
    critical := by simpa only [hnext] using path.critical }
  have hmid : back.walk.getVert 2=path.walk.getVert 2 := by
    change (path.walk.copy rfl hnext.symm).getVert 2=_
    rw [SimpleGraph.Walk.getVert_copy]
  have hf := radius_fixed_at d path.start_color next.start_color hfixed
  have hnorm := h.replacement_distance_four_full_fixed_kernel_normalized d next hb back hmid
    has hvs r (Ltilde_le_stabilizer a hr) hrv hf
  rw [hnext,inf_eq_left.mpr htrap] at hnorm
  exact hn hnorm

/-- The prescribed midpoint in the equal/small root branch has a genuine
backward path, retaining the original whole marking and both selector triples. -/
theorem Input.replacement_distance_four_prescribed_equal_fixed_escape
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical (path.walk.getVert 1)).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ BinaryOffender.fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let t₁ := act d.radical g⁻¹ (path.walk.getVert 1)
      let c₁ := act d.radical g⁻¹ (path.walk.getVert 2)
      let t₂ := act d.radical x t₁
      let c₂ := act d.radical x c₁
      let J₁ := Subgroup.SmallMover.join (U d.radical c₁) (Q d.radical c₁)
        (Q d.radical t₁) (Nat.card F^2)
      let J₂ := Subgroup.SmallMover.join (U d.radical c₂) (Q d.radical c₂)
        (Q d.radical t₂) (Nat.card F^2)
      Adjacent d.radical a t₁ ∧ Adjacent d.radical c₁ t₁ ∧
      Adjacent d.radical a t₂ ∧ Adjacent d.radical c₂ t₂ ∧
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (J₂ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x⁻¹).toMonoidHom =
        stabilizer d.radical a ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₁ : Set (FreeAmalgam d.radical))) ∧
      (¬ ⁅Z d.radical z,U d.radical a⁆ ≤ centralizer (J₂ : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (((((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
        (stabilizer d.radical a).subtype : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ∃ v ∈ ({c₁,c₂} : Set (Vertex d.radical)), ∃ w,
        (v = c₁ ∧ w = t₁ ∨ v = c₂ ∧ w = t₂) ∧
        Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ back : CriticalPath d.radical geometry v (path.walk.getVert 2),
          back.walk.getVert 1 = w ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2) = path.walk.getVert i := by
  let t := path.walk.getVert 1
  let e := path.walk.getVert 2
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed path).2
  have hsmall : (Q d.radical a).relIndex (Z d.radical z)<Nat.card F^2 := by
    rw [hroot]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hmove := h.replacement_path_moving_index_ge_field d path hb4
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical e ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat het).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb4 hat het hsmall)
    have hYB := h.replacement_small_radius_le_B d geometry hb2 path.start_color
      (Z d.radical e ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat het)
      ((Ltilde_le_stabilizer a).trans hn)
      (hidx.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
    have hone := relIndex_eq_one.mpr (((U_le_Z e).trans le_sup_left).trans hYB)
    rw [hone] at hmove
    exact (not_le_of_gt (show 1<Nat.card F from Finite.one_lt_card)) hmove
  obtain ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
      hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,hcases⟩ :=
    h.replacement_equal_small_index_selected_root_alternative d path hb4 hat rfl het
      hnormal hequal hsmall hJm
  refine ⟨B,hB,f,hf,hfQ,hTf,hindex,g,hg,x,hx,hat1,hct1,hat2,hct2,
    hgen1,hgen2,hfix,hmove1,hmove2,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,?_⟩
  have hpen : path.walk.getVert (path.walk.length-2)=e := by rw [hl]
  rcases hcases with ⟨back,hfirst,hover⟩ | ⟨htrap,_⟩
  · let back' : CriticalPath d.radical geometry v e := {
      start_color := back.start_color
      walk := back.walk.copy rfl hpen
      shortest := by rw [SimpleGraph.Walk.length_copy,←hpen]; exact back.shortest
      critical := by simpa only [hpen] using back.critical }
    refine ⟨back',?_,?_⟩
    · change (back.walk.copy rfl hpen).getVert 1=w
      simpa only [SimpleGraph.Walk.getVert_copy] using hfirst
    · intro i hi
      change (back.walk.copy rfl hpen).getVert (i+2)=_
      simpa only [SimpleGraph.Walk.getVert_copy] using hover i hi
  · have hr : ∃ r ∈ Ltilde d.radical a, act d.radical r e=v := by
      rcases hwhich with ⟨hv,_⟩ | ⟨hv,_⟩
      · exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,hv.symm⟩
      · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,?_⟩
        rw [act_mul]
        exact hv.symm
    obtain ⟨r,hr,hrv⟩ := hr
    rw [hpen] at htrap
    exact (prescribed_selector_not_trapped h d path hb haw hvw r hr hrv hfixed hn htrap).elim

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
