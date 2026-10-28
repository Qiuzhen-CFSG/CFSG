module

public import Theory.Combinatorics.DoilyRecognition.Cross
/-!
# Parity relations among the three matchings

Each cross-block edge has exactly one common neighbor. Encoding its two
possible third-block edges by bits gives the three parity relations used
to normalize a triangle frame. Only five-bit identities are checked here.
-/

@[expose] public section

namespace Theory.Combinatorics.Doily

theorem xor_unique_ne (u v:Bool→Bool) (b:Bool)
    (h:∃!c:Bool,u c = Bool.xor b (v c)) :
    Bool.xor (u false) (v false) ≠ Bool.xor (u true) (v true) := by
  obtain ⟨c,hc,hu⟩:=h
  intro he
  have hf:u false=Bool.xor b (v false):=by
    cases c
    · exact hc
    · revert he hc
      generalize u false=a, v false=d, u true=e, v true=f
      cases a <;> cases d <;> cases e <;> cases f <;> cases b <;> decide
  have ht:u true=Bool.xor b (v true):=by
    cases c
    · revert he hc
      generalize u false=a, v false=d, u true=e, v true=f
      cases a <;> cases d <;> cases e <;> cases f <;> cases b <;> decide
    · exact hc
  exact Bool.noConfusion ((hu false hf).trans (hu true ht).symm)

variable {Ω:Type*} [Fintype Ω] [DecidableEq Ω]
variable {G:SimpleGraph Ω} [DecidableRel G.Adj]
namespace Frame
variable (F:Frame G) (h:G.IsSRGWith 15 6 1 3)
include h
omit [DecidableEq Ω] in
 theorem matrix_parity (i j k:Fin 3) (hij:i≠j) (hik:i≠k) (hjk:j≠k)
    (f g q:Bool→Bool→Bool)
    (hf:∀a b c d,G.Adj (F.vertex (.inr (i,(a,b)))) (F.vertex (.inr (j,(c,d)))) ↔ d=Bool.xor b (f a c))
    (hg:∀a b c d,G.Adj (F.vertex (.inr (i,(a,b)))) (F.vertex (.inr (k,(c,d)))) ↔ d=Bool.xor b (g a c))
    (hq:∀a b c d,G.Adj (F.vertex (.inr (j,(a,b)))) (F.vertex (.inr (k,(c,d)))) ↔ d=Bool.xor b (q a c))
    (a b:Bool) :
    Bool.xor (g a false) (q b false) ≠ Bool.xor (g a true) (q b true) := by
  apply xor_unique_ne (g a) (q b) (f a b)
  have hab:G.Adj (F.vertex (.inr (i,(a,false)))) (F.vertex (.inr (j,(b,f a b)))) :=
    (hf a false b (f a b)).mpr (by simp)
  obtain ⟨⟨c,d⟩,hd,hu⟩:=F.common_third h i j k hij hik hjk (a,false) (b,f a b) hab
  have hdg:d=g a c:=by simpa only [Bool.false_xor] using (hg a false c d).mp hd.1
  subst d
  refine ⟨c,(hq b (f a b) c (g a c)).mp hd.2,?_⟩
  intro e he
  have he1:G.Adj (F.vertex (.inr (i,(a,false)))) (F.vertex (.inr (k,(e,g a e)))):=
    (hg a false e (g a e)).mpr (by simp)
  have he2:G.Adj (F.vertex (.inr (j,(b,f a b)))) (F.vertex (.inr (k,(e,g a e)))):=
    (hq b (f a b) e (g a e)).mpr he
  exact congrArg Prod.fst (hu (e,g a e) ⟨he1,he2⟩)
end Frame

structure Pattern (F:Frame G) where
  f : Bool→Bool→Bool
  g : Bool→Bool→Bool
  q : Bool→Bool→Bool
  adj01 : ∀a b c d,G.Adj (F.vertex (.inr (0,(a,b)))) (F.vertex (.inr (1,(c,d)))) ↔ d=Bool.xor b (f a c)
  adj02 : ∀a b c d,G.Adj (F.vertex (.inr (0,(a,b)))) (F.vertex (.inr (2,(c,d)))) ↔ d=Bool.xor b (g a c)
  adj12 : ∀a b c d,G.Adj (F.vertex (.inr (1,(a,b)))) (F.vertex (.inr (2,(c,d)))) ↔ d=Bool.xor b (q a c)

omit [DecidableEq Ω] in
 theorem Frame.exists_pattern (F:Frame G) (h:G.IsSRGWith 15 6 1 3) : Nonempty (Pattern F) := by
  obtain ⟨f,hf⟩:=F.cross_bits h 0 1 (by decide)
  obtain ⟨g,hg⟩:=F.cross_bits h 0 2 (by decide)
  obtain ⟨q,hq⟩:=F.cross_bits h 1 2 (by decide)
  exact ⟨⟨f,g,q,hf,hg,hq⟩⟩

namespace Pattern
variable {F:Frame G} (p:Pattern F) (h:G.IsSRGWith 15 6 1 3)
include h
omit [DecidableEq Ω] in
 theorem parity :
    (∀a b,Bool.xor (p.g a false) (p.q b false) ≠ Bool.xor (p.g a true) (p.q b true)) ∧
    (∀a c,Bool.xor (p.f a false) (p.q false c) ≠ Bool.xor (p.f a true) (p.q true c)) ∧
    (∀b c,Bool.xor (p.f false b) (p.g false c) ≠ Bool.xor (p.f true b) (p.g true c)) := by
  have hxor (a b c:Bool):(a=Bool.xor b c) ↔ (b=Bool.xor a c):=by
    cases a <;> cases b <;> cases c <;> decide
  have h10:∀a b c d,G.Adj (F.vertex (.inr (1,(a,b)))) (F.vertex (.inr (0,(c,d)))) ↔ d=Bool.xor b (p.f c a):=by
    intro a b c d
    rw [G.adj_comm,p.adj01,hxor]
  have h20:∀a b c d,G.Adj (F.vertex (.inr (2,(a,b)))) (F.vertex (.inr (0,(c,d)))) ↔ d=Bool.xor b (p.g c a):=by
    intro a b c d
    rw [G.adj_comm,p.adj02,hxor]
  have h21:∀a b c d,G.Adj (F.vertex (.inr (2,(a,b)))) (F.vertex (.inr (1,(c,d)))) ↔ d=Bool.xor b (p.q c a):=by
    intro a b c d
    rw [G.adj_comm,p.adj12,hxor]
  exact ⟨F.matrix_parity h 0 1 2 (by decide) (by decide) (by decide) p.f p.g p.q p.adj01 p.adj02 p.adj12,
    F.matrix_parity h 0 2 1 (by decide) (by decide) (by decide) p.g p.f (fun c b=>p.q b c) p.adj02 p.adj01 h21,
    F.matrix_parity h 1 2 0 (by decide) (by decide) (by decide) p.q (fun b a=>p.f a b) (fun c a=>p.g a c) p.adj12 h10 h20⟩
end Pattern
end Theory.Combinatorics.Doily
