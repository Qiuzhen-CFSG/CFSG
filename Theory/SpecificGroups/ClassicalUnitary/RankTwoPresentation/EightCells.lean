module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Complements
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.WeylWords
import Mathlib.Tactic.Group

/-!
# Abstract eight-cell Bruhat coverage for the unitary relations

A simple root and its positive complement give the ascending cell product.
The rank-one two-cell alternative gives the descending product. Enumerating
the four ascending roots for each reflection proves closure of the eight
cells under the Borel and both reflections. Induction on generated words
then gives Bruhat coverage without an ambient BN-pair or any injectivity
assumption. This is Steinberg, Lectures on Chevalley Groups, Lemma 25 and
Theorem 4(a), pp.34–36, applied to the relative C₂/BC₂ root order.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {G : Type*} [Group G]

/-- Membership in a literal Borel double coset. -/
def InCell (B : Subgroup G) (n x : G) : Prop := ∃ l∈B, ∃ v∈B, x=l*n*v
namespace InCell
variable {B : Subgroup G} {n x : G}
theorem of_mem (hx : x∈B) : InCell B 1 x := ⟨x,hx,1,B.one_mem,by simp⟩
theorem mem_of_one (hx : InCell B 1 x) : x∈B := by
  obtain ⟨l,hl,v,hv,rfl⟩ := hx
  simpa using B.mul_mem hl hv

theorem mul_right (hx : InCell B n x) {y : G} (hy : y∈B) : InCell B n (x*y) := by
  obtain ⟨l,hl,v,hv,rfl⟩ := hx
  exact ⟨l,hl,v*y,B.mul_mem hv hy,by simp only [mul_assoc]⟩
theorem mul_left (hx : InCell B n x) {y : G} (hy : y∈B) : InCell B n (y*x) := by
  obtain ⟨l,hl,v,hv,rfl⟩ := hx
  exact ⟨y*l,B.mul_mem hy hl,v,hv,by simp only [mul_assoc]⟩

theorem ascending {R : Type*} [Group R] (root : R →* G) {w : G} (hww : w*w=1)
    (hdec : ∀ x∈B, ∃ a z, x=root a*z ∧ w*z*w∈B)
    (hpos : ∀ a, n*root a*n⁻¹∈B) {b : G} (hb : b∈B) : InCell B (n*w) (n*b*w) := by
  obtain ⟨a,z,rfl,hz⟩ := hdec b hb
  refine ⟨n*root a*n⁻¹,hpos a,w*z*w,hz,?_⟩
  simp only [mul_assoc,inv_mul_cancel_left,←mul_assoc w w,hww,one_mul]

theorem step {R : Type*} [Group R] (root : R →* G) {w : G} (hww : w*w=1)
    (hdec : ∀ x∈B, ∃ a z, x=root a*z ∧ w*z*w∈B)
    (htwo : ∀ x∈B, w*x*w∈B ∨ InCell B w (w*x*w))
    (hpos : (∀ a, n*root a*n⁻¹∈B) ∨ (∀ a, (n*w)*root a*(n*w)⁻¹∈B))
    {b : G} (hb : b∈B) : InCell B (n*w) (n*b*w) ∨ InCell B n (n*b*w) := by
  rcases hpos with hp|hp
  · exact Or.inl (ascending root hww hdec hp hb)
  · rcases htwo b hb with hm|⟨l,hl,v,hv,he⟩
    · left
      refine ⟨1,B.one_mem,w*b*w,hm,?_⟩
      simp only [one_mul,mul_assoc,←mul_assoc w w,hww]
    · right
      have hcell := (ascending root hww hdec hp hl).mul_right hv
      have hnn : n*w*w=n := by rw [mul_assoc,hww,mul_one]
      rw [hnn] at hcell
      convert hcell using 1
      calc
        n*b*w = n*w*(w*b*w) := by simp only [mul_assoc,←mul_assoc w w,hww,one_mul]
        _ = n*w*(l*w*v) := by rw [he]
        _ = n*w*l*w*v := by simp only [mul_assoc]
end InCell

variable {RA RD RC RB H : Type*} [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
namespace ReflectionLaws
variable {r : PositiveMaps G RA RD RC RB} {h : H →* G} {s t : G}

private theorem positive_A (e : ReflectionLaws r h s t) (w : WeylWord) :
    (∀ a, w.eval s t*r.A a*(w.eval s t)⁻¹∈r.borel h) ∨
    (∀ a, w.rightS.eval s t*r.A a*(w.rightS.eval s t)⁻¹∈r.borel h) := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left e.ss
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left e.tt
  have he (a : RA) : WeylWord.one.eval s t*r.A a*(WeylWord.one.eval s t)⁻¹∈r.borel h := by
    simpa only [WeylWord.eval,inv_one,one_mul,mul_one] using r.A_mem_borel h a
  have ht (a : RA) : t*r.A a*t⁻¹∈r.borel h := by
    obtain ⟨c,hc⟩ := e.tA a
    rw [hti,hc]
    exact r.C_mem_borel h c
  have hst (a : RA) : (s*t)*r.A a*(s*t)⁻¹∈r.borel h := by
    obtain ⟨c,hc⟩ := e.tA a
    obtain ⟨c',hc'⟩ := e.sC c
    have heq : (s*t)*r.A a*(s*t)⁻¹=s*(t*r.A a*t)*s := by
      simp only [mul_inv_rev,hsi,hti,mul_assoc]
    rw [heq,hc,hc']
    exact r.C_mem_borel h c'
  have htst (a : RA) : (t*s*t)*r.A a*(t*s*t)⁻¹∈r.borel h := by
    obtain ⟨c,hc⟩ := e.tA a
    obtain ⟨c',hc'⟩ := e.sC c
    obtain ⟨a',ha'⟩ := e.tC c'
    have heq : (t*s*t)*r.A a*(t*s*t)⁻¹=t*(s*(t*r.A a*t)*s)*t := by
      simp only [mul_inv_rev,hsi,hti,mul_assoc]
    rw [heq,hc,hc',ha']
    exact r.A_mem_borel h a'
  cases w
  · exact Or.inl he
  · exact Or.inr he
  · exact Or.inl ht
  · exact Or.inl hst
  · exact Or.inr ht
  · exact Or.inr hst
  · exact Or.inl htst
  · exact Or.inr htst

private theorem positive_B (e : ReflectionLaws r h s t) (w : WeylWord) :
    (∀ b, w.eval s t*r.B b*(w.eval s t)⁻¹∈r.borel h) ∨
    (∀ b, w.rightT.eval s t*r.B b*(w.rightT.eval s t)⁻¹∈r.borel h) := by
  have hsi : s⁻¹=s := inv_eq_of_mul_eq_one_left e.ss
  have hti : t⁻¹=t := inv_eq_of_mul_eq_one_left e.tt
  have he (b : RB) : WeylWord.one.eval s t*r.B b*(WeylWord.one.eval s t)⁻¹∈r.borel h := by
    simpa only [WeylWord.eval,inv_one,one_mul,mul_one] using r.B_mem_borel h b
  have hs (b : RB) : s*r.B b*s⁻¹∈r.borel h := by
    obtain ⟨d,hd⟩ := e.sB b
    rw [hsi,hd]
    exact r.D_mem_borel h d
  have hts (b : RB) : (t*s)*r.B b*(t*s)⁻¹∈r.borel h := by
    obtain ⟨d,hd⟩ := e.sB b
    obtain ⟨d',hd'⟩ := e.tD d
    have heq : (t*s)*r.B b*(t*s)⁻¹=t*(s*r.B b*s)*t := by
      simp only [mul_inv_rev,hsi,hti,mul_assoc]
    rw [heq,hd,hd']
    exact r.D_mem_borel h d'
  have hsts (b : RB) : (s*t*s)*r.B b*(s*t*s)⁻¹∈r.borel h := by
    obtain ⟨d,hd⟩ := e.sB b
    obtain ⟨d',hd'⟩ := e.tD d
    obtain ⟨b',hb'⟩ := e.sD d'
    have heq : (s*t*s)*r.B b*(s*t*s)⁻¹=s*(t*(s*r.B b*s)*t)*s := by
      simp only [mul_inv_rev,hsi,hti,mul_assoc]
    rw [heq,hd,hd',hb']
    exact r.B_mem_borel h b'
  cases w
  · exact Or.inl he
  · exact Or.inl hs
  · exact Or.inr he
  · exact Or.inr hs
  · exact Or.inl hts
  · exact Or.inl hsts
  · exact Or.inr hts
  · exact Or.inr hsts

theorem cell_mul_s (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hsh : ∀ k, ∃ l, s*h k*s=h l) (hst : (s*t)^4=1)
    (w : WeylWord) {x : G} (hx : InCell (r.borel h) (w.eval s t) x) :
    InCell (r.borel h) (w.rightS.eval s t) (x*s) ∨ InCell (r.borel h) (w.eval s t) (x*s) := by
  obtain ⟨l,hl,v,hv,rfl⟩ := hx
  have hp := e.positive_A w
  rw [WeylWord.eval_rightS e.ss e.tt hst] at hp ⊢
  have hs := InCell.step r.A e.ss (fun x hx => e.s_complement hc ht hsh hx)
    (fun x hx => e.s_borel hc ht hsh hx) hp hv
  rcases hs with hs|hs
  · exact Or.inl (by simpa only [mul_assoc] using hs.mul_left hl)
  · exact Or.inr (by simpa only [mul_assoc] using hs.mul_left hl)

theorem cell_mul_t (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hth : ∀ k, ∃ l, t*h k*t=h l)
    (w : WeylWord) {x : G} (hx : InCell (r.borel h) (w.eval s t) x) :
    InCell (r.borel h) (w.rightT.eval s t) (x*t) ∨ InCell (r.borel h) (w.eval s t) (x*t) := by
  obtain ⟨l,hl,v,hv,rfl⟩ := hx
  have hp := e.positive_B w
  rw [WeylWord.eval_rightT e.tt] at hp ⊢
  have hs := InCell.step r.B e.tt (fun x hx => e.t_complement hc ht hth hx)
    (fun x hx => e.t_borel hc ht hth hx) hp hv
  rcases hs with hs|hs
  · exact Or.inl (by simpa only [mul_assoc] using hs.mul_left hl)
  · exact Or.inr (by simpa only [mul_assoc] using hs.mul_left hl)

/-- The subgroup generated by the full Borel and the two marked reflections. -/
def fullGenerated (r : PositiveMaps G RA RD RC RB) (h : H →* G) (s t : G) : Subgroup G :=
  Subgroup.closure ((r.borel h : Set G) ∪ {s,t})

/-- Bruhat coverage derived only from the root, torus, and Weyl equations. -/
theorem exists_cell (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hsh : ∀ k, ∃ l, s*h k*s=h l) (hth : ∀ k, ∃ l, t*h k*t=h l) (hst : (s*t)^4=1)
    {x : G} (hx : x∈fullGenerated r h s t) :
    ∃ w : WeylWord, InCell (r.borel h) (w.eval s t) x := by
  have hmul {x y : G} (hy : y∈(r.borel h : Set G) ∪ {s,t})
      (hx : ∃ w : WeylWord, InCell (r.borel h) (w.eval s t) x) :
      ∃ w : WeylWord, InCell (r.borel h) (w.eval s t) (x*y) := by
    obtain ⟨w,hw⟩ := hx
    rcases hy with hy|hy
    · exact ⟨w,hw.mul_right hy⟩
    · rcases hy with rfl|⟨rfl⟩
      · rcases e.cell_mul_s hc ht hsh hst w hw with hs|hs
        · exact ⟨w.rightS,hs⟩
        · exact ⟨w,hs⟩
      · rcases e.cell_mul_t hc ht hth w hw with hs|hs
        · exact ⟨w.rightT,hs⟩
        · exact ⟨w,hs⟩
  induction hx using Subgroup.closure_induction_right with
  | one => exact ⟨.one,InCell.of_mem (r.borel h).one_mem⟩
  | mul_right x hx y hy ih => exact hmul hy ih
  | mul_inv_cancel x hx y hy ih =>
    apply hmul _ ih
    rcases hy with hy|hy
    · exact Or.inl ((r.borel h).inv_mem hy)
    · right
      rcases hy with rfl|⟨rfl⟩
      · exact Or.inl (inv_eq_of_mul_eq_one_left e.ss)
      · exact Or.inr (Set.mem_singleton_iff.mpr (inv_eq_of_mul_eq_one_left e.tt))
end ReflectionLaws
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
