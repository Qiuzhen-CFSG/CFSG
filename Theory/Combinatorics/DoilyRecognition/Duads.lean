module

public import Theory.Combinatorics.DoilyRecognition.Normalize
public import Theory.Combinatorics.PairGraphLocalGeometry
/-!
# The normalized frame as the fifteen duads

An explicit table identifies each normalized triangle frame with the two-sets
on six letters, adjacent when disjoint. Only the fixed table (fifteen vertices
and two signs) is kernel-checked; uniqueness follows from the preceding
structural matching and parity lemmas.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily

def modelAdj (k:Bool) : FrameVertex→FrameVertex→Prop
  | .inl i,.inl j=>i≠j
  | .inl i,.inr (j,_,_)=>i=j
  | .inr (i,_,_),.inl j=>i=j
  | .inr (i,a,b),.inr (j,c,d)=>
    match i,j with
    | 0,0 => a=c∧b≠d
    | 1,1 => a=c∧b≠d
    | 2,2 => a=c∧b≠d
    | 0,1 => d=b
    | 1,0 => b=d
    | 0,2 => d=Bool.xor b a
    | 2,0 => b=Bool.xor d c
    | 1,2 => d=Bool.xor b (Bool.xor a (Bool.xor c k))
    | _,_ => b=Bool.xor d (Bool.xor c (Bool.xor a k))
instance (k:Bool) : DecidableRel (modelAdj k):=fun x y=>by
  unfold modelAdj
  split <;> first | infer_instance | (split <;> infer_instance)

variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable {G:SimpleGraph Ω} [DecidableRel G.Adj]
namespace NormalFrame
variable (F:NormalFrame G)
omit [Fintype Ω] [DecidableEq Ω] [DecidableRel G.Adj] in
 theorem adj_iff (x y:FrameVertex) :
    G.Adj (F.vertex x) (F.vertex y) ↔ modelAdj F.sign x y := by
  rcases x with i|⟨i,a,b⟩ <;> rcases y with j|⟨j,c,d⟩
  · exact F.base_adj i j
  · exact F.mixed_adj i j (c,d)
  · exact (G.adj_comm _ _).trans ((F.mixed_adj j i (a,b)).trans eq_comm)
  · fin_cases i <;> fin_cases j
    · exact F.fiber_adj 0 (a,b) (c,d)
    · exact F.adj01 a b c d
    · exact F.adj02 a b c d
    · exact (G.adj_comm _ _).trans (F.adj01 c d a b)
    · exact F.fiber_adj 1 (a,b) (c,d)
    · exact F.adj12 a b c d
    · exact (G.adj_comm _ _).trans (F.adj02 c d a b)
    · exact (G.adj_comm _ _).trans (F.adj12 c d a b)
    · exact F.fiber_adj 2 (a,b) (c,d)
end NormalFrame

def duadTable (k:Bool) : FrameVertex→Finset (Fin 6)
  | .inl 0=>{0,1}
  | .inl 1=>{2,3}
  | .inl _=>{4,5}
  | .inr (0,false,false)=>{2,4}
  | .inr (0,false,true)=>{3,5}
  | .inr (0,true,false)=>{3,4}
  | .inr (0,true,true)=>{2,5}
  | .inr (1,a,b)=>
    if Bool.xor a (!k) then (if b then {0,4} else {1,5})
    else (if b then {1,4} else {0,5})
  | .inr (_,false,false)=>{0,3}
  | .inr (_,false,true)=>{1,2}
  | .inr (_,true,false)=>{1,3}
  | .inr (_,true,true)=>{0,2}

theorem duadTable_card : ∀k x,(duadTable k x).card=2 := by decide +kernel

def duadMap (k:Bool) (x:FrameVertex) : PairGraph.Vertex (Fin 6):=
  ⟨duadTable k x,duadTable_card k x⟩

theorem duadMap_injective : ∀k,Function.Injective (duadMap k) := by decide +kernel

theorem duadTable_adj : ∀k x y,
    Disjoint (duadTable k x) (duadTable k y) ↔ modelAdj k x y := by decide +kernel

noncomputable def duadEquiv (k:Bool) : FrameVertex≃PairGraph.Vertex (Fin 6):=
  Equiv.ofBijective (duadMap k)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨duadMap_injective k,by decide +kernel⟩)
end Theory.Combinatorics.Doily
