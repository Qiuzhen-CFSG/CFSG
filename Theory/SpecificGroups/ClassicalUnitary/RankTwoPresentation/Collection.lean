module
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Collection of the four positive relative unitary roots

The order is A,D,C,B. The parameter groups for B and D need not be abelian:
this includes the Hermitian root groups in relative type BC₂. The six
crossing rules give collection by induction on a word and its inverses.
No ambient Tits system, injectivity or presentation faithfulness is assumed.

This is the positive-word step in Steinberg's Bruhat mechanism, Lectures on
Chevalley Groups, Lemma 17 and Theorem 33 / Lemma 64 (twisted groups).
-/

@[expose] public section
namespace Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation

variable {G RA RD RC RB : Type*} [Group G] [Group RA] [Group RD] [Group RC] [Group RB]

/-- Four actual parameter homomorphisms, in positive-root order. -/
structure PositiveMaps (G RA RD RC RB : Type*) [Group G]
    [Group RA] [Group RD] [Group RC] [Group RB] where
  A : RA →* G
  D : RD →* G
  C : RC →* G
  B : RB →* G

namespace PositiveMaps
variable (r : PositiveMaps G RA RD RC RB)

/-- The ordered positive product; no uniqueness is built into this definition. -/
def word (a : RA) (d : RD) (c : RC) (b : RB) : G := r.A a * r.D d * r.C c * r.B b

def generators : Set G := Set.range r.A ∪ Set.range r.D ∪ Set.range r.C ∪ Set.range r.B

def generated : Subgroup G := Subgroup.closure r.generators

/-- The six crossing laws needed for collection. Their parameter formulas
are supplied separately by the dimension-specific unitary equations. -/
structure Collects : Prop where
  AD : ∀ a d, Commute (r.A a) (r.D d)
  CD : ∀ c d, Commute (r.C c) (r.D d)
  BC : ∀ b c, Commute (r.B b) (r.C c)
  CA : ∀ c a, ∃ d, r.C c * r.A a = r.A a * r.D d * r.C c
  BD : ∀ b d, ∃ c, r.B b * r.D d = r.D d * r.C c * r.B b
  BA : ∀ b a, ∃ d c, r.B b * r.A a = r.A a * r.D d * r.C c * r.B b

variable {r}

private theorem left_A (a' a : RA) (d : RD) (c : RC) (b : RB) :
    r.A a' * r.word a d c b = r.word (a' * a) d c b := by
  simp only [word, map_mul, mul_assoc]

private theorem left_D (h : r.Collects) (d' : RD) (a : RA) (d : RD) (c : RC) (b : RB) :
    r.D d' * r.word a d c b = r.word a (d' * d) c b := by
  calc
    _ = (r.D d' * r.A a) * r.D d * r.C c * r.B b := by simp only [word, mul_assoc]
    _ = (r.A a * r.D d') * r.D d * r.C c * r.B b := by rw [(h.AD a d').eq.symm]
    _ = _ := by simp only [word, map_mul, mul_assoc]

private theorem left_C (h : r.Collects) (c' : RC) (a : RA) (d : RD) (c : RC) (b : RB) :
    ∃ d', r.C c' * r.word a d c b = r.word a d' (c' * c) b := by
  obtain ⟨e, he⟩ := h.CA c' a
  refine ⟨e * d, ?_⟩
  calc
    _ = (r.C c' * r.A a) * r.D d * r.C c * r.B b := by simp only [word, mul_assoc]
    _ = (r.A a * r.D e) * (r.C c' * r.D d) * r.C c * r.B b := by rw [he]; simp only [mul_assoc]
    _ = (r.A a * r.D e) * (r.D d * r.C c') * r.C c * r.B b := by rw [(h.CD c' d).eq]
    _ = _ := by simp only [word, map_mul, mul_assoc]

private theorem left_B (h : r.Collects) (b' : RB) (a : RA) (d : RD) (c : RC) (b : RB) :
    ∃ d' c', r.B b' * r.word a d c b = r.word a d' c' (b' * b) := by
  obtain ⟨e, f, he⟩ := h.BA b' a
  obtain ⟨k, hk⟩ := h.BD b' d
  refine ⟨e * d, f * k * c, ?_⟩
  calc
    _ = (r.B b' * r.A a) * r.D d * r.C c * r.B b := by simp only [word, mul_assoc]
    _ = (r.A a * r.D e) * r.C f * (r.B b' * r.D d) * r.C c * r.B b := by
      rw [he]; simp only [mul_assoc]
    _ = (r.A a * r.D e) * (r.C f * r.D d) * r.C k * (r.B b' * r.C c) * r.B b := by
      rw [hk]; simp only [mul_assoc]
    _ = (r.A a * r.D e) * (r.D d * r.C f) * r.C k * (r.C c * r.B b') * r.B b := by
      rw [(h.CD f d).eq, (h.BC b' c).eq]
    _ = _ := by simp only [word, map_mul, mul_assoc]

private theorem left_generator (h : r.Collects) {x y : G} (hx : x ∈ r.generators)
    (hy : ∃ a d c b, y = r.word a d c b) : ∃ a d c b, x * y = r.word a d c b := by
  obtain ⟨a,d,c,b,rfl⟩ := hy
  rcases hx with ((⟨a',rfl⟩ | ⟨d',rfl⟩) | ⟨c',rfl⟩) | ⟨b',rfl⟩
  · exact ⟨_,_,_,_,left_A a' a d c b⟩
  · exact ⟨_,_,_,_,left_D h d' a d c b⟩
  · obtain ⟨d',he⟩ := left_C h c' a d c b
    exact ⟨_,_,_,_,he⟩
  · obtain ⟨d',c',he⟩ := left_B h b' a d c b
    exact ⟨_,_,_,_,he⟩

private theorem inv_generator {x : G} (hx : x ∈ r.generators) : x⁻¹ ∈ r.generators := by
  rcases hx with ((⟨a,rfl⟩ | ⟨d,rfl⟩) | ⟨c,rfl⟩) | ⟨b,rfl⟩
  · exact Or.inl (Or.inl (Or.inl ⟨a⁻¹,map_inv _ _⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨d⁻¹,map_inv _ _⟩))
  · exact Or.inl (Or.inr ⟨c⁻¹,map_inv _ _⟩)
  · exact Or.inr ⟨b⁻¹,map_inv _ _⟩

/-- Collection in any abstract group satisfying the six positive relations. -/
theorem exists_word (h : r.Collects) {x : G} (hx : x ∈ r.generated) :
    ∃ a d c b, x = r.word a d c b := by
  induction hx using Subgroup.closure_induction_left with
  | one => exact ⟨1,1,1,1,by simp [word]⟩
  | mul_left x hx y _ ih => exact left_generator h hx ih
  | inv_mul_cancel x hx y _ ih => exact left_generator h (inv_generator hx) ih

/-- The reverse containment uses just the four homomorphisms. -/
theorem word_mem (a : RA) (d : RD) (c : RC) (b : RB) : r.word a d c b ∈ r.generated := by
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inl ⟨a,rfl⟩)))
      · exact Subgroup.subset_closure (Or.inl (Or.inl (Or.inr ⟨d,rfl⟩)))
    · exact Subgroup.subset_closure (Or.inl (Or.inr ⟨c,rfl⟩))
  · exact Subgroup.subset_closure (Or.inr ⟨b,rfl⟩)

/-- A coordinate separation calculation makes evaluation faithful on the
positive subgroup. This is only the positive part of a Bruhat presentation. -/
theorem injective_on_generated {M : Type*} [Group M] (h : r.Collects) (f : G →* M)
    (hf : Function.Injective (fun p : RA × RD × RC × RB =>
      f (r.word p.1 p.2.1 p.2.2.1 p.2.2.2))) :
    Function.Injective (f.comp r.generated.subtype) := by
  intro x y hxy
  obtain ⟨a,d,c,b,hx⟩ := exists_word h x.property
  obtain ⟨a',d',c',b',hy⟩ := exists_word h y.property
  have he : (a,d,c,b) = (a',d',c',b') := hf (by simpa only [MonoidHom.comp_apply,
    Subgroup.coe_subtype, hx,hy] using hxy)
  cases he
  exact Subtype.ext (hx.trans hy.symm)

end PositiveMaps
end Theory.SpecificGroups.ClassicalUnitary.RankTwoPresentation
