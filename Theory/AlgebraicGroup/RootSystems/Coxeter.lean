module

public import Mathlib.GroupTheory.Coxeter.Basic

/-! Coxeter presentations and deletion moves used by Weyl-group constructions. -/

namespace Theory.AlgebraicGroup

/-- A bijective homomorphism from a Coxeter presentation onto a group equips the
target with the corresponding Coxeter system, and identifies its generators
with the images of the presented generators. -/
public theorem coxeterSystem_of_bijective_presentedGroup_hom
    {B G : Type*} [Group G] (C : CoxeterMatrix B)
    (φ : C.Group →* G) (hφ : Function.Bijective φ) :
    ∃ cs : CoxeterSystem C G,
      ∀ i : B, CoxeterSystem.simple cs i = φ (C.simple i) := by
  let e : C.Group ≃* G := MulEquiv.ofBijective φ hφ
  let cs : CoxeterSystem C G := ⟨e.symm⟩
  refine ⟨cs, ?_⟩
  intro i
  change e (C.simple i) = φ (C.simple i)
  rfl

@[expose] public def CoxeterMove {B : Type*} (C : CoxeterMatrix B)
    (source result : List B) : Prop :=
  (∃ left right i,
      source = left ++ [i, i] ++ right ∧ result = left ++ right) ∨
    (∃ left right i j,
      source = left ++ CoxeterSystem.braidWord C i j ++ right ∧
        result = left ++ CoxeterSystem.braidWord C j i ++ right)

public lemma coxeterMove_cancel
    {B : Type*} (C : CoxeterMatrix B) (left right : List B) (i : B) :
    CoxeterMove C (left ++ [i, i] ++ right) (left ++ right) :=
  Or.inl ⟨left, right, i, rfl, rfl⟩

public lemma coxeterMove_braid
    {B : Type*} (C : CoxeterMatrix B) (left right : List B) (i j : B) :
    CoxeterMove C
      (left ++ CoxeterSystem.braidWord C i j ++ right)
      (left ++ CoxeterSystem.braidWord C j i ++ right) :=
  Or.inr ⟨left, right, i, j, rfl, rfl⟩

public lemma coxeterMove_append_right
    {B : Type*} (C : CoxeterMatrix B) {source result : List B}
    (suffix : List B) (h : CoxeterMove C source result) :
    CoxeterMove C (source ++ suffix) (result ++ suffix) := by
  rcases h with hcancel | hbraid
  · rcases hcancel with ⟨left, right, i, rfl, rfl⟩
    exact Or.inl ⟨left, right ++ suffix, i, by simp, by simp⟩
  · rcases hbraid with ⟨left, right, i, j, rfl, rfl⟩
    exact Or.inr ⟨left, right ++ suffix, i, j, by simp, by simp⟩

public lemma coxeterMove_reflTransGen_append_right
    {B : Type*} (C : CoxeterMatrix B) {source result : List B}
    (suffix : List B)
    (h : Relation.ReflTransGen (CoxeterMove C) source result) :
    Relation.ReflTransGen (CoxeterMove C)
      (source ++ suffix) (result ++ suffix) := by
  exact Relation.ReflTransGen.lift (fun l => l ++ suffix)
    (fun _ _ hmove => coxeterMove_append_right C suffix hmove)
    source result h

public lemma coxeterMove_preserves_wordProd
    {B : Type*} {C : CoxeterMatrix B} (source result : List B)
    (h : CoxeterMove C source result) :
    C.toCoxeterSystem.wordProd source = C.toCoxeterSystem.wordProd result := by
  rcases h with hcancel | hbraid
  · rcases hcancel with ⟨left, right, i, rfl, rfl⟩
    simp only [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_cons]
    have hi : C.simple i * C.simple i = (1 : C.Group) :=
      C.toCoxeterSystem.simple_mul_simple_self i
    simp [hi]
  · rcases hbraid with ⟨left, right, i, j, rfl, rfl⟩
    simp only [CoxeterSystem.wordProd_append]
    rw [CoxeterSystem.wordProd_braidWord_eq]

public lemma coxeterMove_reflTransGen_preserves_wordProd
    {B : Type*} {C : CoxeterMatrix B} {source result : List B}
    (h : Relation.ReflTransGen (CoxeterMove C) source result) :
    C.toCoxeterSystem.wordProd source = C.toCoxeterSystem.wordProd result := by
  induction h with
  | refl => rfl
  | tail hstep hmove ih =>
      exact ih.trans (coxeterMove_preserves_wordProd _ _ hmove)

public theorem coxeterHom_injective_of_deletion
    {B G : Type*} [Group G] (C : CoxeterMatrix B)
    (φ : C.Group →* G) (wprod : List B → G)
    (hword : ∀ l : List B,
      φ (C.toCoxeterSystem.wordProd l) = wprod l)
    (hinv : ∀ l : List B,
      wprod l.reverse = (wprod l)⁻¹)
    (happend : ∀ l m : List B,
      wprod (l ++ m) = wprod l * wprod m)
    (hdel : ∀ l : List B, wprod l = 1 →
      Relation.ReflTransGen (CoxeterMove C) l []) :
    Function.Injective φ := by
  intro x y hxy
  obtain ⟨l, rfl⟩ := C.toCoxeterSystem.wordProd_surjective x
  obtain ⟨m, rfl⟩ := C.toCoxeterSystem.wordProd_surjective y
  have hxy' : wprod l = wprod m :=
    (hword l).symm.trans (hxy.trans (hword m))
  have hprod : wprod (l ++ m.reverse) = 1 := by
    rw [happend, hinv]
    rw [hxy']
    simp
  have hreach := hdel (l ++ m.reverse) hprod
  have hword_eq := coxeterMove_reflTransGen_preserves_wordProd hreach
  have hsource_prod :
      C.toCoxeterSystem.wordProd (l ++ m.reverse) = 1 := by
    simpa using hword_eq
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_reverse] at hsource_prod
  exact mul_inv_eq_one.mp hsource_prod

end Theory.AlgebraicGroup
