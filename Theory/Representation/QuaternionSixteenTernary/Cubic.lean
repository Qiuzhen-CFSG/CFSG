module
public import Theory.Representation.QuaternionSixteenTernary.Certificate
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Tactic

/-!
# The actual cubic normalizing the ternary quaternion subgroup

An additive automorphism normalizing the marked Q₈ induces a permutation of
its eight operators. Its cube and the reflection inversion relation force
one of five pairs of generator images. These equations determine all four
columns from a single vector. The small checked certificate then gives the
four possible cubic matrices. Every hypothesis is an equation on the actual
action, rather than an asserted placement in a finite catalogue.

Source: Aschbacher, *Sporadic Groups* (1994), 45.11, p.248.
-/

public section
namespace Theory.Representation.QuaternionSixteenTernary

private def coordA : V →+ V where
  toFun := a
  map_zero' := by decide
  map_add' x y := by ext <;> simp [a] <;> ring
private def coordR : V →+ V where
  toFun := r
  map_zero' := by decide
  map_add' x y := by ext <;> simp [r] <;> ring

private theorem q_add (i : Fin 8) (x y : V) : q i (x+y)=q i x+q i y := by
  fin_cases i <;> ext <;> simp [q,qi,qj,a,r] <;> ring

private theorem q_zero : ∀ i : Fin 8, q i (0:V)=0 := by decide +kernel

def qHom (i : Fin 8) : V →+ V where
  toFun := q i
  map_zero' := q_zero i
  map_add' := q_add i

def linHom (m : Mat) : V →+ V where
  toFun := lin m
  map_zero' := by ext <;> simp [lin]
  map_add' x y := by ext <;> simp [lin] <;> ring

@[simp] theorem linHom_apply (m : Mat) (v : V) : linHom m v=lin m v := by rfl

@[simp] theorem qHom_apply (i : Fin 8) (v : V) : qHom i v=q i v := by rfl

private theorem expansion (x : V) :
    x = x.1.val • e 0+x.2.1.val • e 1+x.2.2.1.val • e 2+x.2.2.2.val • e 3 := by
  ext <;> simp [e,nsmul_eq_mul]

private theorem lin_nsmul (m : Mat) (x : V) :
    lin m x = x.1.val • m.1+x.2.1.val • m.2.1+x.2.2.1.val • m.2.2.1+x.2.2.2.val • m.2.2.2 := by
  ext <;> simp [lin,nsmul_eq_mul]

private theorem action_coordinates (f : V →+ V) (x : V) :
    f x = lin (f (e 0),f (e 1),f (e 2),f (e 3)) x := by
  conv_lhs => rw [expansion x]
  simp only [map_add,map_nsmul,lin_nsmul]

theorem coordinates_of_quaternion_images (f : V →+ V) (i j : Fin 8)
    (hi : ∀ v, f (qi v)=q i (f v)) (hj : ∀ v, f (qj v)=q j (f v)) :
    ∀ v, f v=lin (candidate i j (f (e 0))) v := by
  have he1 : f (e 1)=q i (f (e 0))-f (e 0) := by
    have hh := hi (e 0)
    have hrel : qi (e 0)=e 0+e 1 := by decide +kernel
    rw [hrel,map_add] at hh
    exact eq_sub_of_add_eq' hh
  have he3 : f (e 3)=q j (f (e 0)) := by
    have hh := hj (e 0)
    have hrel : qj (e 0)=e 3 := by decide +kernel
    rwa [hrel] at hh
  have he2 : f (e 2)= -q i (q j (f (e 0)))-q j (f (e 0)) := by
    have hh := hi (e 3)
    have hrel : qi (e 3)= -(e 2+e 3) := by decide +kernel
    rw [hrel,map_neg,map_add,he3] at hh
    exact eq_sub_of_add_eq (neg_eq_iff_eq_neg.mp hh)
  intro v
  rw [action_coordinates f v,he1,he2,he3]
  rfl

theorem imageCode_intertwines (f : V →+ V) (i j : Fin 8)
    (hi : ∀ v, f (qi v)=q i (f v)) (hj : ∀ v, f (qj v)=q j (f v)) :
    ∀ k v, f (q k v)=q (imageCode i j k) (f v) := by
  intro k v
  fin_cases k
  · rfl
  · change f (-v)= -f v
    exact map_neg f v
  · exact hi v
  · change f (-(qi v))=q (negativeCode i) (f v)
    rw [map_neg,hi,q_negative]
  · exact hj v
  · change f (-(qj v))=q (negativeCode j) (f v)
    rw [map_neg,hj,q_negative]
  · change f (qi (qj v))=q (codeMul i j) (f v)
    rw [hi,hj,q_mul]
  · change f (-(qi (qj v)))=q (negativeCode (codeMul i j)) (f v)
    rw [map_neg,hi,hj,q_negative,q_mul]

theorem imageCode_relations (f : V →+ V) (i j : Fin 8)
    (hi : ∀ v, f (qi v)=q i (f v)) (hj : ∀ v, f (qj v)=q j (f v))
    (hc : ∀ v, f (f (f v))=v)
    (hr : ∀ v, r (f v)=f (f (r v))) : possibleImages i j := by
  have ht := imageCode_intertwines f i j hi hj
  have hs : Function.Surjective f := fun v=>⟨f (f v),hc v⟩
  have hrs : Function.Surjective r := by
    intro v
    refine ⟨-r v,?_⟩
    change coordR (-coordR v)=v
    rw [map_neg]
    have hh : r (r v)= -v := by ext <;> simp [r]
    change -r (r v)=v
    rw [hh,neg_neg]
  apply possibleImages_of_relations i j
  · intro k
    apply q_faithful
    have hh := hc (q k (e 0))
    rw [ht,ht,ht,hc] at hh
    exact hh
  · intro k
    apply q_faithful
    obtain ⟨v,hv⟩ := hrs (e 0)
    obtain ⟨w,hw⟩ := hs v
    have hh := hr (q k w)
    rw [ht,q_reflection,q_reflection,ht,ht] at hh
    rw [←hr w,hw,hv] at hh
    exact hh

/-- Every actual cubic with the marked quaternion/reflection relations is one
of the four explicit linear actions. -/
theorem cubic_classification (f : V →+ V)
    (hc : ∀ v, f (f (f v))=v) (hr : ∀ v, r (f v)=f (f (r v)))
    (hne : ∃ v, f v≠v)
    (hn : ∀ k : Fin 8, ∃ j : Fin 8, ∀ v, f (q k v)=q j (f v)) :
    f=linHom y0 ∨ f=linHom y1 ∨ f=linHom y2 ∨ f=linHom y3 := by
  obtain ⟨i,hi⟩ := hn 2
  obtain ⟨j,hj⟩ := hn 4
  have hi' : ∀ v, f (qi v)=q i (f v) := hi
  have hj' : ∀ v, f (qj v)=q j (f v) := hj
  have hcoords := coordinates_of_quaternion_images f i j hi' hj'
  have hgood : good i j (candidate i j (f (e 0))) := by
    constructor
    · intro t
      simpa only [←hcoords] using hi' (e t)
    constructor
    · intro t
      simpa only [←hcoords] using hj' (e t)
    constructor
    · intro t
      simpa only [←hcoords] using hc (e t)
    constructor
    · intro t
      simpa only [←hcoords] using hr (e t)
    · by_contra he
      push Not at he
      obtain ⟨v,hv⟩ := hne
      apply hv
      have he' : ∀ t, f (e t)=e t := by simpa only [←hcoords] using he
      have hid := action_coordinates (AddMonoidHom.id V) v
      have heval := action_coordinates f v
      simpa only [he',AddMonoidHom.id_apply] using heval.trans (by simpa only [he',AddMonoidHom.id_apply] using hid.symm)
  have hlist := cubic_candidates i j (imageCode_relations f i j hi' hj' hc hr) _ hgood
  have hf : f=linHom (candidate i j (f (e 0))) := AddMonoidHom.ext hcoords
  rcases hlist with he | he | he | he
  · exact Or.inl (hf.trans (congrArg linHom he))
  · exact Or.inr (Or.inl (hf.trans (congrArg linHom he)))
  · exact Or.inr (Or.inr (Or.inl (hf.trans (congrArg linHom he))))
  · exact Or.inr (Or.inr (Or.inr (hf.trans (congrArg linHom he))))
end Theory.Representation.QuaternionSixteenTernary
