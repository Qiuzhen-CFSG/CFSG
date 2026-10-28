module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.BorelCells
import Mathlib.Tactic.Group

/-!
# Simple roots and their positive complements

Each element of the generated Borel factors as one simple-root element
followed by a factor whose simple-reflection conjugate remains in the Borel.
For the nonabelian B root this follows by collecting the inverse word and
moving the torus past that root. This is the missing factorization used in
Steinberg, Lectures on Chevalley Groups, Lemma 25(a), pp.34–35.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {G RA RD RC RB H : Type*} [Group G] [Group RA] [Group RD] [Group RC] [Group RB] [Group H]
namespace PositiveMaps
variable (r : PositiveMaps G RA RD RC RB) (h : H →* G)

theorem A_mem_borel (a : RA) : r.A a ∈ r.borel h :=
  (le_sup_left : r.generated ≤ r.borel h) (Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩))))
theorem D_mem_borel (d : RD) : r.D d ∈ r.borel h :=
  (le_sup_left : r.generated ≤ r.borel h) (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨d,rfl⟩))))
theorem C_mem_borel (c : RC) : r.C c ∈ r.borel h :=
  (le_sup_left : r.generated ≤ r.borel h) (Subgroup.subset_closure (Or.inl (Or.inr ⟨c,rfl⟩)))
theorem B_mem_borel (b : RB) : r.B b ∈ r.borel h :=
  (le_sup_left : r.generated ≤ r.borel h) (Subgroup.subset_closure (Or.inr ⟨b,rfl⟩))
theorem torus_mem_borel (k : H) : h k ∈ r.borel h :=
  (le_sup_right : h.range ≤ r.borel h) ⟨k,rfl⟩
end PositiveMaps
namespace ReflectionLaws
variable {r : PositiveMaps G RA RD RC RB} {h : H →* G} {s t : G}

theorem s_complement (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hsh : ∀ k, ∃ l, s*h k*s=h l) {x : G} (hx : x∈r.borel h) :
    ∃ a z, x=r.A a*z ∧ s*z*s∈r.borel h := by
  obtain ⟨a,d,c,b,k,rfl⟩ := ht.exists_word hc hx
  obtain ⟨b',hb'⟩ := e.sD d
  obtain ⟨c',hc'⟩ := e.sC c
  obtain ⟨d',hd'⟩ := e.sB b
  obtain ⟨k',hk'⟩ := hsh k
  refine ⟨a,r.D d*r.C c*r.B b*h k,by simp only [PositiveMaps.word,mul_assoc],?_⟩
  have hs (y : G) : s*(s*y)=y := by rw [←mul_assoc,e.ss,one_mul]
  have he : s*(r.D d*r.C c*r.B b*h k)*s=r.B b'*r.C c'*r.D d'*h k' := by
    rw [←hb',←hc',←hd',←hk']
    simp only [mul_assoc,hs]
  rw [he]
  exact (r.borel h).mul_mem ((r.borel h).mul_mem ((r.borel h).mul_mem
    (r.B_mem_borel h _) (r.C_mem_borel h _)) (r.D_mem_borel h _)) (r.torus_mem_borel h _)

theorem t_complement (e : ReflectionLaws r h s t) (hc : r.Collects) (ht : r.TorusLaws h)
    (hth : ∀ k, ∃ l, t*h k*t=h l) {x : G} (hx : x∈r.borel h) :
    ∃ b z, x=r.B b*z ∧ t*z*t∈r.borel h := by
  obtain ⟨a,d,c,b,k,hx'⟩ := ht.exists_word hc ((r.borel h).inv_mem hx)
  obtain ⟨b',hb'⟩ := ht.B k⁻¹ b⁻¹
  obtain ⟨k',hk'⟩ := hth k⁻¹
  obtain ⟨a',ha'⟩ := e.tC c⁻¹
  obtain ⟨d',hd'⟩ := e.tD d⁻¹
  obtain ⟨c',hc'⟩ := e.tA a⁻¹
  refine ⟨b',h k⁻¹*r.C c⁻¹*r.D d⁻¹*r.A a⁻¹,?_,?_⟩
  · have hi := congrArg Inv.inv hx'
    simp only [inv_inv,PositiveMaps.word,mul_inv_rev,←map_inv] at hi
    rw [hi,←hb']
    group
  · have ht' (y : G) : t*(t*y)=y := by rw [←mul_assoc,e.tt,one_mul]
    have he : t*(h k⁻¹*r.C c⁻¹*r.D d⁻¹*r.A a⁻¹)*t=h k'*r.A a'*r.D d'*r.C c' := by
      rw [←hk',←ha',←hd',←hc']
      simp only [mul_assoc,ht']
    rw [he]
    exact (r.borel h).mul_mem ((r.borel h).mul_mem ((r.borel h).mul_mem
      (r.torus_mem_borel h _) (r.A_mem_borel h _)) (r.D_mem_borel h _)) (r.C_mem_borel h _)
end ReflectionLaws
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
