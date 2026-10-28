module
public import Theory.GroupAction.HexagonReflections
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.TrialityTwo.Smallness
public import Theory.GroupAction.RankTwoCosetGeometry.PathOrderLowerBound

/-!
# Actual endpoint reflections in a small binary triality completion

Orbit–stabilizer and the exact local valences show that every seven-path
fixer has order seven. A twelve-cycle is translated onto the original
base edge. Its reflection action therefore lifts through a kernel of order
dividing seven to an actual dihedral group. The two involutions belong to
the original endpoint images, escape their whole Borel intersection, and
have product of order exactly six. The order bound supplies the cycle.

This discharges the existence of an actual F.4.15 reflection pair. It does
not assert that the same marked preimages obey the relation in the native
model: that matching, and hence ambient recognition, remains to be proved.
Source: Aschbacher–Smith F.4.15–16,24,26, pp.281–282,287–288.
-/

@[expose] public noncomputable section
open Subgroup SimpleGraph SimpleGraph.PathTransitivePolygon
open Subgroup.CosetGeometry Subgroup.CosetGeometry.RankTwo
open GroupAction.HexagonReflections
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
variable {G : Type*} [Group G] (c : Completion G)

/-- Every nonbacktracking seven-path rooted at the original arms vertex has
pointwise stabilizer of order seven. -/
theorem seven_fixer_card (p : BasedWalk c.graph 7 (RankTwo.base c.family false))
    (hp : p.Nonbacktracking) : Nat.card (pathStabilizer c.family p)=7 := by
  have hcount : Nat.card {q : BasedWalk c.graph 7 (RankTwo.base c.family false) // q.Nonbacktracking}=36864 := by
    have hf : ∀ {v w : c.Vertex}, c.graph.Adj v w → w.type = !v.type := by
      intro v w h
      exact Bool.eq_not_iff.mpr h.1.symm
    have h := BasedWalk.card_nonbacktracking_succ c.graph (fun v : c.Vertex => v.type)
      NativeSeven.degree hf c.card_neighbors 6 (RankTwo.base c.family false)
    change _ = NativeSeven.degree false * BasedWalk.forwardCount NativeSeven.degree 6 true at h
    exact h.trans (by decide)
  have h := card_paths_mul_card_fixer c.family (c.seven_transitive _) p hp
  rw [hcount,stabilizer,stabilizer_base,c.family_card] at h
  simp only [Bool.false_eq_true,↓reduceIte] at h
  omega

private def cycleHom {v : c.Vertex} (p : c.graph.Walk v v) (hl : p.length=12) :
    cycleGraph 12 →g c.graph where
  toFun i := p.getVert i.val
  map_rel' := by
    have hstep (i : Fin 12) : c.graph.Adj (p.getVert i.val) (p.getVert (i+1).val) := by
      have h := p.adj_getVert_succ (i := i.val) (by omega)
      by_cases hi : i.val=11
      · have hs : (i+1).val=0 := by omega
        rw [hi,hs]
        simpa only [hi,show 11+1=p.length from hl.symm,Walk.getVert_length,Walk.getVert_zero] using h
      · have hs : (i+1).val=i.val+1 := by omega
        rwa [hs]
    intro i j hij
    rw [cycleGraph_adj,sub_eq_iff_eq_add,sub_eq_iff_eq_add] at hij
    rcases hij with hij | hij
    · have he : i=j+1 := by rw [hij]; abel
      rw [he]
      exact (hstep j).symm
    · have he : j=i+1 := by rw [hij]; abel
      rw [he]
      exact hstep i

private theorem cycleHom_injective {v : c.Vertex} (p : c.graph.Walk v v)
    (hp : p.IsCycle) (hl : p.length=12) : Function.Injective (cycleHom c p hl) := by
  intro i j h
  apply Fin.ext
  exact hp.getVert_injOn' (by change i.val≤p.length-1; omega)
    (by change j.val≤p.length-1; omega) h

/-- An actual twelve-cycle can be based on the literal original edge. -/
theorem exists_cycle_on_base_edge
    (hex : ∃ v, ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=12) :
    ∃ f : cycleGraph 12 →g c.graph, Function.Injective f ∧
      f 0=RankTwo.base c.family false ∧ f 1=RankTwo.base c.family true := by
  classical
  obtain ⟨v,p,hp,hl⟩ := hex
  have hcycle : ∃ v : c.Vertex, v.type=false ∧
      ∃ p : c.graph.Walk v v, p.IsCycle ∧ p.length=12 := by
    cases hv : v.type with
    | false => exact ⟨v,hv,p,hp,hl⟩
    | true =>
      have htype : p.snd.type=false := by
        have h := (p.adj_snd hp.not_nil).1
        cases hs : p.snd.type <;> simp_all
      have hs : p.snd∈p.support := p.getVert_mem_support 1
      exact ⟨p.snd,htype,p.rotate p.snd hs,hp.rotate hs,by simpa using hl⟩
  obtain ⟨v,hv,p,hp,hl⟩ := hcycle
  let f := cycleHom c p hl
  have hf := cycleHom_injective c p hp hl
  have h0 : (f 0).type=false := by
    change (p.getVert 0).type=false
    simpa only [Walk.getVert_zero] using hv
  have h01 : c.graph.Adj (f 0) (f 1) := f.map_rel' (by decide)
  have h1 : (f 1).type=true := by
    have h := h01.1
    cases hh : (f 1).type <;> simp_all
  obtain ⟨g,hg0,hg1⟩ := incident_common_translate c.family h01.2
  rw [h0] at hg0
  rw [h1] at hg1
  let k := (c.graphAction.hom g⁻¹).comp f
  refine ⟨k,(MulAction.injective g⁻¹).comp hf,?_,?_⟩
  · change g⁻¹ • f 0=RankTwo.base c.family false
    rw [←hg0,inv_smul_smul]
  · change g⁻¹ • f 1=RankTwo.base c.family true
    rw [←hg1,inv_smul_smul]

variable [Finite G]

/-- The order bound supplies genuine endpoint involutions satisfying the actual
sixth-power equation. No native equation for their marked preimages is assumed. -/
theorem exists_endpoint_involutions_of_order_bound
    (horder : Nat.card G≤Nat.card Model) :
    ∃ s : _root_.Triality.Standard.Parabolics.parabolic parameters .arms,
      ∃ t : _root_.Triality.Standard.Parabolics.parabolic parameters .central,
        s^2=1 ∧ t^2=1 ∧ c.left s∉c.middle.range ∧ c.right t∉c.middle.range ∧
          (c.left s*c.right t)^6=1 ∧ orderOf (c.left s*c.right t)=6 := by
  obtain ⟨f,hf,h0,h1⟩ := c.exists_cycle_on_base_edge
    (c.exists_twelve_cycle_of_order_bound horder)
  let p := BasedWalk.rebase h0 (arc f 0 7)
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_rebase _ _).mpr
    (arc_nonbacktracking f hf _ _)
  let Q := pathStabilizer c.family p
  have hQ (g : G) (hg : ∀ i, g • f i=f i) : g∈Q := by
    intro v hv
    change v∈p.vertices at hv
    simp only [p,BasedWalk.vertices_rebase,arc_vertices,List.mem_ofFn] at hv
    obtain ⟨i,rfl⟩ := hv
    exact hg _
  have hcop : (Nat.card Q).Coprime 12 := by rw [c.seven_fixer_card p hp]; decide
  obtain ⟨s,t,hs,ht,hst,hs0,hs1,ht1,ht0⟩ :=
    exists_reflections c.graphAction c.cycle_length_ge_twelve c.seven_transitive f hf Q hQ hcop
  rw [h0] at hs0 ht0
  rw [h1] at hs1 ht1
  have hprod : orderOf (s*t)=6 := GroupAction.DihedralPolygon.edge_exponent_eq
    c.bipartiteAction c.uniqueGeodesicsBelow_six (orderOf_pos (s*t))
    (Nat.le_of_dvd (by decide) (orderOf_dvd_of_pow_eq_one hst))
    ⟨Bool.false_ne_true,incident_base c.family false true⟩ hs ht hs0 hs1 ht1 ht0
    (by rw [pow_orderOf_eq_one,one_smul]) (by rw [pow_orderOf_eq_one,one_smul])
  have hsf : s∈c.left.range := by
    have h : s∈MulAction.stabilizer G (RankTwo.base c.family false) := hs0
    simpa only [RankTwo.base,stabilizer_base,family_false] using h
  have htf : t∈c.right.range := by
    have h : t∈MulAction.stabilizer G (RankTwo.base c.family true) := ht1
    simpa only [RankTwo.base,stabilizer_base,family_true] using h
  obtain ⟨a,rfl⟩ := hsf
  obtain ⟨b,rfl⟩ := htf
  refine ⟨a,b,c.left_injective ?_,c.right_injective ?_,?_,?_,hst,hprod⟩
  · rw [map_pow,hs,map_one]
  · rw [map_pow,ht,map_one]
  · intro h
    apply hs1
    have hmem := c.middle_le_right h
    change c.left a∈MulAction.stabilizer G (RankTwo.base c.family true)
    simpa only [RankTwo.base,stabilizer_base,family_true] using hmem
  · intro h
    apply ht0
    have hmem := c.middle_le_left h
    change c.right b∈MulAction.stabilizer G (RankTwo.base c.family false)
    simpa only [RankTwo.base,stabilizer_base,family_false] using hmem

end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo.Completion
