module

public import Theory.Combinatorics.DoilyRecognition.Parity
/-!
# Normalizing the doily matching coordinates

Switching the two endpoints independently in the six local matching edges
normalizes all three cross-block matchings. The remaining sign is harmless
and is retained explicitly for the final duad table. No graph enumeration
is used: the algebraic checks involve at most six Boolean variables.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily

private theorem xor_rectangle (a b c d e f:Bool)
    (h1:Bool.xor a e≠Bool.xor b f) (h2:Bool.xor c e≠Bool.xor d f) :
    Bool.xor (Bool.xor b d) (Bool.xor c a)=false := by
  revert h1 h2
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide
private theorem xor_diagonal (a b c d:Bool)
    (h:Bool.xor a b≠Bool.xor c d) :
    Bool.xor (Bool.xor c d) (Bool.xor a b)=true := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> decide
private theorem xor_ne_left (a b c d e:Bool)
    (h:Bool.xor b c ≠ Bool.xor d e) :
    Bool.xor a (Bool.xor c b) ≠ Bool.xor a (Bool.xor e d) := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide
private theorem xor_ne_right (a b c d e:Bool)
    (h:Bool.xor a b ≠ Bool.xor c d) :
    Bool.xor a (Bool.xor b e) ≠ Bool.xor c (Bool.xor d e) := by
  revert h
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

private theorem square_checker (r:Bool→Bool→Bool)
    (hr:∀a,r a false≠r a true) (hc:∀c,r false c≠r true c) (a c:Bool) :
    r a c = Bool.xor a (Bool.xor c (r false false)) := by
  have h0:=hr false
  have h1:=hr true
  have hv:=hc false
  cases a <;> cases c
  · simp
  · revert h0
    generalize r false false=x, r false true=y
    cases x <;> cases y <;> decide
  · revert hv
    generalize r false false=x, r true false=y
    cases x <;> cases y <;> decide
  · revert h1 hv
    generalize r false false=x, r true false=y, r true true=z
    cases x <;> cases y <;> cases z <;> decide

variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable {G:SimpleGraph Ω} [DecidableRel G.Adj]
namespace Pattern
variable {F:Frame G} (p:Pattern F)
def flip0 (a:Bool):Bool:=p.f a false
def flip1 (a:Bool):Bool:=Bool.xor (p.f false a) (p.f false false)
def flip2 (a:Bool):Bool:=Bool.xor (p.f false false) (p.g false a)
def sign :Bool:=Bool.xor (p.q false false) (Bool.xor (p.f false false) (p.g false false))

omit [DecidableEq Ω] in
 theorem normalized_bits (h:G.IsSRGWith 15 6 1 3) :
    (∀a c,Bool.xor (Bool.xor (p.flip0 a) (p.f a c)) (p.flip1 c)=false) ∧
    (∀a c,Bool.xor (Bool.xor (p.flip0 a) (p.g a c)) (p.flip2 c)=a) ∧
    (∀a c,Bool.xor (Bool.xor (p.flip1 a) (p.q a c)) (p.flip2 c)=
      Bool.xor a (Bool.xor c p.sign)) := by
  obtain ⟨h01,h02,h12⟩:=p.parity h
  refine ⟨?_,?_,?_⟩
  · intro a c
    cases a <;> cases c
    · simp [flip0,flip1]
    · simp [flip0,flip1]
    · simp [flip0,flip1]
    · exact xor_rectangle _ _ _ _ _ _ (h12 false false) (h12 true false)
  · intro a c
    cases a
    · simp [flip0,flip2]
    · exact xor_diagonal _ _ _ _ (h12 false c)
  · let r:Bool→Bool→Bool:=fun a c=>Bool.xor (p.f false a) (Bool.xor (p.q a c) (p.g false c))
    have hr:∀a,r a false≠r a true:=fun a=>xor_ne_left _ _ _ _ _ (h01 false a)
    have hc:∀c,r false c≠r true c:=fun c=>xor_ne_right _ _ _ _ _ (h02 false c)
    intro a c
    have he:=square_checker r hr hc a c
    have hl:Bool.xor (Bool.xor (p.flip1 a) (p.q a c)) (p.flip2 c)=r a c:=by
      dsimp [flip1,flip2,r]
      generalize p.f false a=x, p.f false false=y, p.q a c=z, p.g false c=w
      cases x <;> cases y <;> cases z <;> cases w <;> rfl
    have hs:r false false=p.sign:=by
      dsimp [r,sign]
      generalize p.f false false=x, p.q false false=y, p.g false false=z
      cases x <;> cases y <;> cases z <;> rfl
    exact hl.trans (he.trans (congrArg (fun z=>Bool.xor a (Bool.xor c z)) hs))
end Pattern

def coordinateFlip (ε:Fin 3→Bool→Bool) : FrameVertex≃FrameVertex where
  toFun x:=match x with
    | .inl i=>.inl i
    | .inr (i,a,b)=>.inr (i,a,Bool.xor b (ε i a))
  invFun x:=match x with
    | .inl i=>.inl i
    | .inr (i,a,b)=>.inr (i,a,Bool.xor b (ε i a))
  left_inv:=by rintro (i|⟨i,a,b⟩) <;> simp
  right_inv:=by rintro (i|⟨i,a,b⟩) <;> simp

namespace Frame
variable (F:Frame G)
def flip (ε:Fin 3→Bool→Bool) : Frame G where
  vertex := (coordinateFlip ε).trans F.vertex
  base_adj := F.base_adj
  mixed_adj := fun i j p=> F.mixed_adj i j (p.1,Bool.xor p.2 (ε j p.1))
  fiber_adj := by
    rintro i ⟨a,b⟩ ⟨c,d⟩
    change G.Adj (F.vertex (.inr (i,a,Bool.xor b (ε i a))))
      (F.vertex (.inr (i,c,Bool.xor d (ε i c)))) ↔ a=c∧b≠d
    rw [F.fiber_adj]
    by_cases hac:a=c
    · subst c
      simp only [true_and]
      generalize ε i a=e
      cases b <;> cases d <;> cases e <;> decide
    · simp only [hac,false_and]
end Frame

structure NormalFrame (G:SimpleGraph Ω) extends Frame G where
  sign : Bool
  adj01 : ∀a b c d,G.Adj (vertex (.inr (0,(a,b)))) (vertex (.inr (1,(c,d)))) ↔ d=b
  adj02 : ∀a b c d,G.Adj (vertex (.inr (0,(a,b)))) (vertex (.inr (2,(c,d)))) ↔ d=Bool.xor b a
  adj12 : ∀a b c d,G.Adj (vertex (.inr (1,(a,b)))) (vertex (.inr (2,(c,d)))) ↔ d=Bool.xor b (Bool.xor a (Bool.xor c sign))

private theorem flipped_equation (b d u v f:Bool) :
    (Bool.xor d v = Bool.xor (Bool.xor b u) f) ↔
      d=Bool.xor b (Bool.xor (Bool.xor u f) v) := by
  cases b <;> cases d <;> cases u <;> cases v <;> cases f <;> decide

omit [DecidableEq Ω] in
 theorem Pattern.normalFrame {F:Frame G} (p:Pattern F) (h:G.IsSRGWith 15 6 1 3) :
    Nonempty (NormalFrame G) := by
  let ε:Fin 3→Bool→Bool:=![p.flip0,p.flip1,p.flip2]
  obtain ⟨h01,h02,h12⟩:=p.normalized_bits h
  refine ⟨{toFrame:=F.flip ε,sign:=p.sign,adj01:=?_,adj02:=?_,adj12:=?_}⟩
  · intro a b c d
    change G.Adj (F.vertex (.inr (0,a,Bool.xor b (p.flip0 a))))
      (F.vertex (.inr (1,c,Bool.xor d (p.flip1 c)))) ↔ d=b
    rw [p.adj01,flipped_equation,h01]
    simp
  · intro a b c d
    change G.Adj (F.vertex (.inr (0,a,Bool.xor b (p.flip0 a))))
      (F.vertex (.inr (2,c,Bool.xor d (p.flip2 c)))) ↔ d=Bool.xor b a
    rw [p.adj02,flipped_equation,h02]
  · intro a b c d
    change G.Adj (F.vertex (.inr (1,a,Bool.xor b (p.flip1 a))))
      (F.vertex (.inr (2,c,Bool.xor d (p.flip2 c)))) ↔ d=Bool.xor b (Bool.xor a (Bool.xor c p.sign))
    rw [p.adj12,flipped_equation,h12]

 theorem exists_normalFrame (h:G.IsSRGWith 15 6 1 3) : Nonempty (NormalFrame G) := by
  obtain ⟨F⟩:=exists_frame h
  obtain ⟨p⟩:=F.exists_pattern h
  exact p.normalFrame h

end Theory.Combinatorics.Doily
