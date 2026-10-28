module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.PathCertificates
public import Theory.GroupAction.CubicTree.TotalSingularity
/-!
# Native regular six-path in the field-four J₂ geometry

The cubic--quintic coset graph attached to the marked parabolics `p₂` and
`l₁` contains the explicit length-six path used in DGS (10.9), printed p.163.
The terminal turn by `turn ^ 2` preserves the terminal type while avoiding the
cubic parabolic.  The Borel element `bElement 83` fixes every displayed path
vertex, and its checked conjugates move both endpoint continuations.  Since
both endpoint valences are three, the local mover criterion gives regularity
at both ends.

The finite permutation certificates below are kernel-checked through the
faithful degree-100 carrier action; no abstract identification of the graph
is used in this module.
-/
@[expose] public noncomputable section
namespace Sporadic.LeechRelated.J2.ExceptionalParabolics.PathCertificates
open Theory.GroupTheory GeneratorPair Seed PairNormalizer
open PairNormalizer.SylowData PairNormalizer.QuotientData PairNormalizer.RadicalData
open GeneratorPair.SecondOrbitCertificate SecondParabolic.Overlap
open SecondParabolic.BorelAutomorphisms
open Subgroup.CosetGeometry.RankTwo SimpleGraph
open Theory.GroupAction.CubicTree SimpleGraph.PathTransitivePolygon
local notation "u" => oddGenerator 0
def endWord : Carrier := longWord * turn ^ 2
def endTable : Equiv.Perm (Fin 100) := turnTable * oddTable 0 * turnTable * oddTable 0 * turnTable ^ 2
theorem end_inclusion : inclusion endWord = endTable := by
  simp only [endWord,longWord,map_mul,map_pow,turn_inclusion,oddGenerator_inclusion,endTable]
set_option maxRecDepth 100000 in
theorem turn_five : turn ^ 5 = 1 := by
  apply inclusion_injective
  rw [map_pow,turn_inclusion,map_one]
  decide +kernel
theorem turn_sq_not_alpha : turn ^ 2 ∉ family true := by
  intro h
  have hh : (turn ^ 2) ^ 3 ∈ family true := Subgroup.pow_mem _ h 3
  have he : (turn ^ 2) ^ 3 = turn := by
    rw [←pow_mul, show 2*3=5+1 from rfl,pow_succ,turn_five,one_mul]
  rw [he] at hh
  exact turn_not_alpha hh
private theorem fix_base {g : Carrier} {i : Bool} (hg : g ∈ family i) :
    g • base family i = base family i := by
  change g ∈ stabilizer family (base family i)
  simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hg
private theorem translate_ne {g : Carrier} {i : Bool} (hg : g ∉ family i) :
    g • base family i ≠ base family i := fun he => hg (by
      have hh : g ∈ stabilizer family (base family i) := he
      simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base] using hh)
private theorem end_edge : (graph family).Adj (path true).endpoint
    (endWord • base family true) := by
  have hh : (graph family).Adj (base family false) (base family true) :=
    ⟨by decide,Subgroup.CosetGeometry.incident_base family false true⟩
  have h := (Subgroup.CosetGeometry.translationGraphIso family endWord).toHom.map_adj hh
  change (graph family).Adj (endWord • base family false) _ at h
  have ht : turn ^ 2 • base family false = base family false :=
    fix_base (Subgroup.pow_mem _ turn_mem_l₁ 2)
  change (graph family).Adj (longWord • base family false) (endWord • base family true)
  have he : endWord • base family false = longWord • base family false := by
    rw [endWord,mul_smul,ht]
  rw [he] at h
  exact h
def sixPath : BasedWalk (graph family) 6 (base family true) :=
  (path true).snoc (z := endWord • base family true) (by exact end_edge)
theorem sixPath_vertices : sixPath.vertices =
    [base family true,base family false,turn • base family true,
    (turn*u) • base family false,(turn*u*turn) • base family true,
    longWord • base family false,endWord • base family true] := by
  rw [sixPath, BasedWalk.vertices_snoc]
  rfl
theorem sixPath_nb : sixPath.Nonbacktracking := by
  rw [sixPath, BasedWalk.nonbacktracking_snoc_iff]
  refine ⟨path_nonbacktracking true,?_⟩
  change endWord • base family true ≠ (turn*u*turn) • base family true
  have hu : u • base family true = base family true := fix_base odd_mem_alpha
  have he : (turn*u*turn) • base family true = longWord • base family true := by
    simp only [longWord,mul_smul,hu]
  rw [he]
  intro hh
  apply translate_ne turn_sq_not_alpha
  have hh' := congrArg (fun v : Vertex family => longWord⁻¹ • v) hh
  simpa only [endWord,mul_smul,inv_smul_smul] using hh'
def mover : Carrier := bElement 83
set_option maxRecDepth 100000 in
private theorem mover_conjugates :
    turn⁻¹ * mover * turn = bElement 26 ∧
    (turn*u)⁻¹ * mover * (turn*u) = bElement 6 ∧
    (turn*u*turn)⁻¹ * mover * (turn*u*turn) = bElement 6 ∧
    longWord⁻¹ * mover * longWord = bElement 5 ∧
    endWord⁻¹ * mover * endWord = bElement 121 := by
  have cert :
      turnTable⁻¹ * bTable 83 * turnTable = bTable 26 ∧
      (turnTable*oddTable 0)⁻¹ * bTable 83 * (turnTable*oddTable 0) = bTable 6 ∧
      (turnTable*oddTable 0*turnTable)⁻¹ * bTable 83 * (turnTable*oddTable 0*turnTable) = bTable 6 ∧
      (turnTable*oddTable 0*turnTable*oddTable 0)⁻¹ * bTable 83 * (turnTable*oddTable 0*turnTable*oddTable 0) = bTable 5 ∧
      endTable⁻¹ * bTable 83 * endTable = bTable 121 := by
    decide +kernel
  rcases cert with ⟨h1,h2,h3,h4,h5⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · apply inclusion_injective
    simp only [mover,map_mul,map_inv,bElement_table,turn_inclusion]
    exact h1
  · apply inclusion_injective
    simp only [mover,map_mul,map_inv,bElement_table,turn_inclusion,
      oddGenerator_inclusion]
    exact h2
  · apply inclusion_injective
    simp only [mover,map_mul,map_inv,bElement_table,turn_inclusion,
      oddGenerator_inclusion]
    exact h3
  · apply inclusion_injective
    simp only [mover,longWord,map_mul,map_inv,bElement_table,turn_inclusion,
      oddGenerator_inclusion]
    exact h4
  · apply inclusion_injective
    simp only [mover,map_mul,map_inv,bElement_table,end_inclusion]
    exact h5
private theorem fixes_translate {g w : Carrier} {i : Bool}
    (hg : w⁻¹*g*w ∈ family i) : g • (w • base family i) = w • base family i := by
  have hh := fix_base hg
  apply (MulAction.toPerm w⁻¹).injective
  simpa only [MulAction.toPerm_apply,mul_smul,inv_smul_smul] using hh
theorem mover_fixes : mover ∈ pathStabilizer family sixPath := by
  rcases mover_conjugates with ⟨h1,h2,h3,h4,h5⟩
  have hb (i : Fin 384) : (bElement i : Carrier) ∈ family true ∧
      (bElement i : Carrier) ∈ family false := ⟨B_le_p₂ (bElement i).property,B_le_l₁ (bElement i).property⟩
  have hm : mover ∈ family true ∧ mover ∈ family false := hb 83
  intro v hv
  rw [sixPath_vertices] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact fix_base hm.1
  · exact fix_base hm.2
  · exact fixes_translate (h1 ▸ (hb 26).1)
  · exact fixes_translate (h2 ▸ (hb 6).2)
  · exact fixes_translate (h3 ▸ (hb 6).1)
  · exact fixes_translate (h4 ▸ (hb 5).2)
  · exact fixes_translate (h5 ▸ (hb 121).1)

private theorem moved_translate {g w : Carrier} {i : Bool}
    (hg : w⁻¹*g*w ∉ family i) : g • (w • base family i) ≠ w • base family i := by
  intro he
  apply translate_ne hg
  have hh := congrArg (fun v : Vertex family => w⁻¹ • v) he
  simpa only [mul_smul,inv_smul_smul] using hh

set_option maxRecDepth 100000 in
private theorem mover_moves :
    mover • (u • base family false) ≠ u • base family false ∧
    mover • ((endWord*u) • base family false) ≠ (endWord*u) • base family false := by
  have check :
      ((oddTable 0)⁻¹ * bTable 83 * oddTable 0 * FirstFusion.tPerm) 0 ≠
        (FirstFusion.tPerm * ((oddTable 0)⁻¹ * bTable 83 * oddTable 0)) 0 ∧
      ((endTable * oddTable 0)⁻¹ * bTable 83 * (endTable * oddTable 0) * FirstFusion.tPerm) 0 ≠
        (FirstFusion.tPerm * ((endTable * oddTable 0)⁻¹ * bTable 83 * (endTable * oddTable 0))) 0 := by
    decide +kernel
  constructor
  · apply moved_translate
    intro hc
    have he := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp hc)
    change inclusion (u⁻¹ * mover * u * z) = inclusion (z * (u⁻¹ * mover * u)) at he
    simp only [map_mul,map_inv,mover,oddGenerator_inclusion,bElement_table] at he
    change _ * inclusion FirstFusion.t = inclusion FirstFusion.t * _ at he
    rw [FirstFusion.inclusion_t] at he
    exact check.1 (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) he)
  · apply moved_translate
    intro hc
    have he := congrArg inclusion (Subgroup.mem_centralizer_singleton_iff.mp hc)
    change inclusion ((endWord*u)⁻¹ * mover * (endWord*u) * z) =
      inclusion (z * ((endWord*u)⁻¹ * mover * (endWord*u))) at he
    simp only [map_mul,map_inv,mover,oddGenerator_inclusion,bElement_table,end_inclusion] at he
    change _ * inclusion FirstFusion.t = inclusion FirstFusion.t * _ at he
    rw [FirstFusion.inclusion_t] at he
    exact check.2 (congrArg (fun p : Equiv.Perm (Fin 100) => p 0) he)

private theorem first_choice_adj : (graph family).Adj (base family true)
    (u • base family false) := by
  have h := (Subgroup.CosetGeometry.translationGraphIso family u).toHom.map_adj
    (show (graph family).Adj (base family true) (base family false) from
      ⟨by decide,Subgroup.CosetGeometry.incident_base family true false⟩)
  change (graph family).Adj (u • base family true) (u • base family false) at h
  rw [fix_base odd_mem_alpha] at h
  exact h

private theorem right_choice_forward : Forward sixPath ((endWord*u) • base family false) := by
  refine ⟨?_,?_⟩
  · change (graph family).Adj (endWord • base family true) ((endWord*u) • base family false)
    have hh := (Subgroup.CosetGeometry.translationGraphIso family endWord).toHom.map_adj first_choice_adj
    change (graph family).Adj (endWord • base family true) (endWord • (u • base family false)) at hh
    simpa only [mul_smul] using hh
  · change (endWord*u) • base family false ≠ longWord • base family false
    have ht : endWord • base family false = longWord • base family false := by
      rw [endWord,mul_smul,fix_base (Subgroup.pow_mem _ turn_mem_l₁ 2)]
    rw [← ht,mul_smul]
    intro hh
    apply translate_ne (i := false) odd_not_beta
    have hh' := congrArg (fun v : Vertex family => endWord⁻¹ • v) hh
    simpa only [inv_smul_smul] using hh'

private theorem left_choice_backward : Backward sixPath (u • base family false) :=
  ⟨first_choice_adj,translate_ne odd_not_beta⟩

theorem sixPath_regular : Regular (A := Carrier) sixPath := by
  have ha : GraphAction (graph family) Carrier :=
    ⟨fun g _ _ h => (Subgroup.CosetGeometry.translationGraphIso family g).toHom.map_adj h⟩
  have hc := card_neighbors_of_indices family (fun i => if i then 3 else 5) family_indices
  have hright : Nat.card ((graph family).neighborSet sixPath.endpoint) = 3 := hc _
  have hleft : Nat.card ((graph family).neighborSet (base family true)) = 3 := hc _
  refine ⟨(rightRegular_reverse_iff sixPath).mp ?_,?_⟩
  · apply rightRegular_of_moved_forward ha (reverse sixPath)
      (by simpa only [endpoint_reverse] using hleft) mover
      (by intro y hy; exact mover_fixes y (by simpa only [vertices_reverse,List.mem_reverse] using hy))
      ((forward_reverse_iff_backward sixPath).mpr left_choice_backward) mover_moves.1
  · exact rightRegular_of_moved_forward ha sixPath hright mover mover_fixes
      right_choice_forward mover_moves.2
end Sporadic.LeechRelated.J2.ExceptionalParabolics.PathCertificates
