module
public import Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation.Collection
import Mathlib.Tactic.Group

/-!
# The rank-one two-cell step from root equations

Conjugate an ordered A,D,C,B word by a simple reflection. All complementary
roots remain positive. The remaining simple root is either trivial or has
its explicit rank-one Bruhat word. Thus its conjugate is in B or B w B.
This argument works in an arbitrary group, before presentation faithfulness.
Source: Steinberg, Lectures on Chevalley Groups, Lemma 24, pp.33–34.
-/
@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
variable {G RA RD RC RB H : Type*} [Group G] [Group RA] [Group RD] [Group RC] [Group RB] [Group H]

/-- Equations used by the two rank-one collection steps. The dimension-specific
identities supply the actual parameters; no ambient Bruhat decomposition is an input. -/
structure ReflectionLaws (r : PositiveMaps G RA RD RC RB) (h : H →* G) (s t : G) : Prop where
  ss : s*s=1
  tt : t*t=1
  sD : ∀ d, ∃ b, s*r.D d*s=r.B b
  sC : ∀ c, ∃ c', s*r.C c*s=r.C c'
  sB : ∀ b, ∃ d, s*r.B b*s=r.D d
  tA : ∀ a, ∃ c, t*r.A a*t=r.C c
  tD : ∀ d, ∃ d', t*r.D d*t=r.D d'
  tC : ∀ c, ∃ a, t*r.C c*t=r.A a
  sA : ∀ a, s*r.A a*s=1 ∨ ∃ a' k a'',
    s*r.A a*s=r.A a'*h k*s*r.A a''
  tB : ∀ b, t*r.B b*t=1 ∨ ∃ b' k b'',
    t*r.B b*t=r.B b'*h k*t*r.B b''

namespace ReflectionLaws
variable {r : PositiveMaps G RA RD RC RB} {h : H →* G} {s t : G}



/-- The plane reflection gives exactly the rank-one two-cell alternative. -/
theorem s_word (e : ReflectionLaws r h s t) (B : Subgroup G) (hr : r.generated≤B) (hh : h.range≤B) (a : RA) (d : RD) (c : RC) (b : RB) :
    s*r.word a d c b*s∈B ∨
      ∃ l∈B, ∃ v∈B, s*r.word a d c b*s=l*s*v := by
  have hA (a : RA) : r.A a∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩))))
  have hD (d : RD) : r.D d∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨d,rfl⟩))))
  have hC (c : RC) : r.C c∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inr ⟨c,rfl⟩)))
  have hB (b : RB) : r.B b∈B := show _∈B from hr (Subgroup.subset_closure (Or.inr ⟨b,rfl⟩))
  have hH (k : H) : h k∈B := hh ⟨k,rfl⟩
  obtain ⟨b',hb'⟩ := e.sD d
  obtain ⟨c',hc'⟩ := e.sC c
  obtain ⟨d',hd'⟩ := e.sB b
  have hs (x : G) : s*(s*x)=x := by rw [←mul_assoc,e.ss,one_mul]
  have he : s*r.word a d c b*s = (s*r.A a*s)*(r.B b'*r.C c'*r.D d') := by
    rw [←hb',←hc',←hd']
    simp only [PositiveMaps.word]
    simp only [mul_assoc,hs]
  rw [he]
  rcases e.sA a with ha | ⟨a',k,a'',ha⟩
  · left
    rw [ha,one_mul]
    exact B.mul_mem (B.mul_mem (hB _) (hC _)) (hD _)
  · right
    refine ⟨r.A a'*h k,B.mul_mem (hA _) (hH _),
      r.A a''*(r.B b'*r.C c'*r.D d'),
      B.mul_mem (hA _) (B.mul_mem (B.mul_mem (hB _) (hC _)) (hD _)),?_⟩
    rw [ha]
    simp only [mul_assoc]

/-- The point reflection retains the entire (possibly nonabelian) B root group. -/
theorem t_word (e : ReflectionLaws r h s t) (B : Subgroup G) (hr : r.generated≤B) (hh : h.range≤B) (a : RA) (d : RD) (c : RC) (b : RB) :
    t*r.word a d c b*t∈B ∨
      ∃ l∈B, ∃ v∈B, t*r.word a d c b*t=l*t*v := by
  have hA (a : RA) : r.A a∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩))))
  have hD (d : RD) : r.D d∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨d,rfl⟩))))
  have hC (c : RC) : r.C c∈B := show _∈B from hr (Subgroup.subset_closure (Or.inl (Or.inr ⟨c,rfl⟩)))
  have hB (b : RB) : r.B b∈B := show _∈B from hr (Subgroup.subset_closure (Or.inr ⟨b,rfl⟩))
  have hH (k : H) : h k∈B := hh ⟨k,rfl⟩
  obtain ⟨c',hc'⟩ := e.tA a
  obtain ⟨d',hd'⟩ := e.tD d
  obtain ⟨a',ha'⟩ := e.tC c
  have ht (x : G) : t*(t*x)=x := by rw [←mul_assoc,e.tt,one_mul]
  have he : t*r.word a d c b*t = (r.C c'*r.D d'*r.A a')*(t*r.B b*t) := by
    rw [←hc',←hd',←ha']
    simp only [PositiveMaps.word]
    simp only [mul_assoc,ht]
  rw [he]
  rcases e.tB b with hb | ⟨b',k,b'',hb⟩
  · left
    rw [hb,mul_one]
    exact B.mul_mem (B.mul_mem (hC _) (hD _)) (hA _)
  · right
    refine ⟨(r.C c'*r.D d'*r.A a')*r.B b'*h k,
      B.mul_mem (B.mul_mem (B.mul_mem (B.mul_mem (hC _) (hD _)) (hA _)) (hB _)) (hH _),
      r.B b'',hB _,?_⟩
    rw [hb]
    simp only [mul_assoc]

end ReflectionLaws
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
