module
public import CFSG.Quasithin.ChapterJ.Section05.SourceAction.Graph
public import CFSG.Quasithin.ChapterJ.Section05.SourceGeometry.Coordinates
public import Theory.GroupAction.InvariantFiberCard

/-!
# The original J.5.5 graph parameters and local suborbits

The native five distance spheres partition the first source orbit into actual
parabolic suborbits. Double counting forces the nonneighbor subset to have size
divisible by256, and connectedness excludes zero. Among the possible sphere
unions this selects precisely the1024 opposites. Hence λ=730, μ=780, and the
three adjacent suborbits have sizes10,80,640. No graph parameters are assumed.

Source: Aschbacher–Smith J.5.5(1–3), printed p.446.
-/

public noncomputable section
open Subgroup MulAction
open scoped BigOperators
namespace CFSG.Quasithin.ChapterJ.Section05
variable {G:Type*} [Group G] [Finite G]
variable (F:Subgroup G) (q:G) (hq:q∉F) (hs:q•(q•basePoint F)=basePoint F)

@[expose] def localNonneighbors : Set (orbit F (q•basePoint F)) :=
  {v | v.val≠q•basePoint F ∧ ¬(sourceGraph F q hq hs).Adj (q•basePoint F) v.val}

omit [Finite G] in
theorem localNonneighbors_invariant (f:stabilizer F (q•basePoint F))
    (v:orbit F (q•basePoint F)) (hv:v∈localNonneighbors F q hq hs) :
    f•v∈localNonneighbors F q hq hs := by
  have hf:(f.val:G)•(q•basePoint F)=q•basePoint F:=f.property
  constructor
  · intro he
    apply hv.1
    exact (MulAction.injective (f.val:G)) (he.trans hf.symm)
  · intro he
    apply hv.2
    apply (sourceGraph_adj_smul F q hq hs (f.val:G) (q•basePoint F) v.val).mp
    change (sourceGraph F q hq hs).Adj (q•basePoint F) ((f.val:G)•v.val) at he
    rwa [hf]

theorem localNonneighbors_card_add :
    Nat.card (localNonneighbors F q hq hs)+
      Nat.card ((sourceGraph F q hq hs).commonNeighbors (basePoint F) (q•basePoint F))+1=
      Nat.card (orbit F (q•basePoint F)) := by
  let Δ:=orbit F (q•basePoint F)
  let δ:Δ:=⟨q•basePoint F,mem_orbit_self _⟩
  let N:Set Δ:={v|(sourceGraph F q hq hs).Adj (q•basePoint F) v.val}
  let E:N≃(sourceGraph F q hq hs).commonNeighbors (basePoint F) (q•basePoint F):=
    { toFun:=fun v=>⟨v.val.val,⟨(sourceGraph_neighbor_base F q hq hs).ge v.val.property,v.property⟩⟩
      invFun:=fun v=>⟨⟨v.val,(sourceGraph_neighbor_base F q hq hs).le v.property.1⟩,v.property.2⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  have hd:Disjoint ({δ}:Set Δ) N:=by
    apply Set.disjoint_singleton_left.mpr
    exact (sourceGraph F q hq hs).loopless.irrefl _
  have hc:=Set.ncard_add_ncard_compl (({δ}:Set Δ)∪N)
  have hcomp:(({δ}:Set Δ)∪N)ᶜ=localNonneighbors F q hq hs:=by
    ext v
    change ¬(v=δ ∨ (sourceGraph F q hq hs).Adj (q•basePoint F) v.val) ↔ _
    simp only [not_or,Subtype.ext_iff]
    rfl
  rw [Set.ncard_union_eq hd,Set.ncard_singleton,hcomp] at hc
  have hN:Nat.card N=Nat.card ((sourceGraph F q hq hs).commonNeighbors
      (basePoint F) (q•basePoint F)):=Nat.card_congr E
  change 1+Nat.card N+Nat.card (localNonneighbors F q hq hs)=Nat.card Δ at hc
  rw [hN] at hc
  have he:Nat.card (localNonneighbors F q hq hs)+
      Nat.card ((sourceGraph F q hq hs).commonNeighbors (basePoint F) (q•basePoint F))+1=Nat.card Δ:=by omega
  exact he

theorem RudvalisAction.localNonneighbors_pos_dvd {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    0<Nat.card (localNonneighbors F q hq hs) ∧
      256∣Nat.card (localNonneighbors F q hq hs) := by
  have hc:=localNonneighbors_card_add F q hq hs
  rw [h.first_length] at hc
  have hn:1755-Nat.card ((sourceGraph F q hq hs).commonNeighbors
      (basePoint F) (q•basePoint F))-1=Nat.card (localNonneighbors F q hq hs):=by omega
  have hp:=h.parameter_equation F q hq hs
  rw [hn] at hp
  have hm:=h.mu_pos F q hq hs
  constructor
  · nlinarith
  · have hd:256∣1755*Nat.card (localNonneighbors F q hq hs):=by
      rw [hp]; exact dvd_mul_of_dvd_left (by decide) _
    exact (show Nat.Coprime 256 1755 by decide).dvd_of_dvd_mul_left hd

/-- J.5.5(2): exactly the distance-eight points are locally nonadjacent. -/
theorem RudvalisAction.localNonneighbors_iff_opposite {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
    (v:orbit F (q•basePoint F)) :
    v∈localNonneighbors F q hq hs ↔
      h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=4 := by
  let δ:orbit F (q•basePoint F):=⟨q•basePoint F,mem_orbit_self _⟩
  let f:=h.localDistance δ
  obtain ⟨T,hT,hcard⟩:=invariant_set_fiber_sum (K:=stabilizer F (q•basePoint F)) f
    (fun x y hh=>h.first_stabilizer_transitive x y hh) (localNonneighbors F q hq hs)
    (localNonneighbors_invariant F q hq hs) (![1,10,80,640,1024]:Fin 5→ℕ)
    (h.localDistance_sphere_card δ)
  have h0:(0:Fin 5)∉T:=by
    intro he
    have hf:f δ=0:=(h.localDistance_zero δ δ).mpr rfl
    have hh:δ∈localNonneighbors F q hq hs:=(hT δ).mpr (hf.symm ▸ he)
    exact hh.1 rfl
  have hp:=h.localNonneighbors_pos_dvd F q hq hs
  rw [hcard] at hp
  have ht:=SimpleGraph.OctagonShortPaths.five_sphere_selection T h0 hp.1 hp.2
  rw [hT,ht,Finset.mem_singleton]

/-- The actual source graph has the parameters in J.5.5(1). -/
theorem RudvalisAction.parameters {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    Nat.card ((sourceGraph F q hq hs).commonNeighbors
      (basePoint F) (q•basePoint F))=730 ∧
    Nat.card ((sourceGraph F q hq hs).commonNeighbors
      (basePoint F) (g•basePoint F))=780 := by
  have hc:Nat.card (localNonneighbors F q hq hs)=1024:=by
    have he:localNonneighbors F q hq hs≃
        {v:orbit F (q•basePoint F) // h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=4}:=
      Equiv.subtypeEquivRight (h.localNonneighbors_iff_opposite F q hq hs)
    rw [Nat.card_congr he]
    exact h.localDistance_sphere_card _ 4
  have hsum:=localNonneighbors_card_add F q hq hs
  rw [hc,h.first_length] at hsum
  have hlam:Nat.card ((sourceGraph F q hq hs).commonNeighbors
      (basePoint F) (q•basePoint F))=730:=by omega
  have hp:=h.parameter_equation F q hq hs
  rw [hlam] at hp
  exact ⟨hlam,by omega⟩

/-- J.5.5(2–3): adjacent points in the first orbit are precisely spheres1–3. -/
theorem RudvalisAction.local_adj_iff {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F))
    (v:orbit F (q•basePoint F)) :
    (sourceGraph F q hq hs).Adj (q•basePoint F) v.val ↔
      h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v≠0 ∧
      h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v≠4 := by
  let δ:orbit F (q•basePoint F):=⟨q•basePoint F,mem_orbit_self _⟩
  have hz:h.localDistance δ v=0↔v.val=q•basePoint F:=by
    rw [h.localDistance_zero,Subtype.ext_iff]
    exact eq_comm
  have ho:=h.localNonneighbors_iff_opposite F q hq hs v
  change (v.val≠q•basePoint F ∧ ¬(sourceGraph F q hq hs).Adj (q•basePoint F) v.val) ↔ _ at ho
  constructor
  · intro ha
    have hv:v.val≠q•basePoint F:=ha.ne.symm
    exact ⟨fun he=>hv (hz.mp he),fun he=>(ho.mpr he).2 ha⟩
  · rintro ⟨hn0,hn4⟩
    by_contra hn
    exact hn4 (ho.mp ⟨fun he=>hn0 (hz.mpr he),hn⟩)

/-- Literal three adjacent suborbits, with their source cardinalities. -/
theorem RudvalisAction.source_J_5_5_three_suborbits {g:G}
    (h:RudvalisAction F (q•basePoint F) (g•basePoint F)) :
    (∀v:orbit F (q•basePoint F),
      (sourceGraph F q hq hs).Adj (q•basePoint F) v.val ↔
        h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=1 ∨
        h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=2 ∨
        h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=3) ∧
    (∀i:Fin 5,Nat.card {v:orbit F (q•basePoint F) //
      h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=i}=(![1,10,80,640,1024]:Fin 5→ℕ) i) ∧
    (∀v w:orbit F (q•basePoint F),
      h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=
        h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ w →
      ∃f:stabilizer F (q•basePoint F),f•v=w) := by
  refine ⟨?_,h.localDistance_sphere_card _,h.first_stabilizer_transitive⟩
  intro v
  rw [h.local_adj_iff F q hq hs]
  generalize h.localDistance ⟨q•basePoint F,mem_orbit_self _⟩ v=i
  fin_cases i <;> decide

end CFSG.Quasithin.ChapterJ.Section05
