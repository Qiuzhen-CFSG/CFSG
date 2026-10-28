module
public import Theory.GroupTheory.Amalgam.RankTwoCompletion
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Common conjugation of a marked endpoint pair

Conjugate the two endpoint preimages by the images of one middle element.
The commuting square identifies both ambient conjugations. This preserves
the involution equations, escape from the whole middle image, the product
relation and its exact order. Normalization transports to the conjugated
middle subgroup through the same homomorphism.

This abstract proof avoids repeatedly checking the conjugation identities
inside a concrete matrix-group carrier. Its consumer aligns the order-seven
apartment fixer in binary triality. Source: Aschbacher--Smith F.2.1 and
F.4.16, printed pp.265 and282.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
variable {L B R G : Type*} [Group L] [Group B] [Group R] [Group G]
variable {α : RankTwoAmalgam L B R} (c : FaithfulCompletion α (G := G))

private theorem map_conjugate_middle (Q : Subgroup B) (b : B) :
    (Q.map (MulAut.conj b).toMonoidHom).map c.middle =
      (Q.map c.middle).map (MulAut.conj (c.middle b)).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

/-- Conjugating both endpoints by one marked middle element preserves an
involution pair, its product relation and order, and normalization of the
conjugated middle subgroup. -/
theorem conjugate_endpoint_pair (Q : Subgroup B) (b : B)
    (s : L) (t : R) (n : ℕ) (hs : s^2=1) (ht : t^2=1)
    (hsout : c.left s∉c.middle.range) (htout : c.right t∉c.middle.range)
    (hpow : (c.left s*c.right t)^n=1)
    (hsQ : c.left s ∈ normalizer (Q.map c.middle : Set G))
    (htQ : c.right t ∈ normalizer (Q.map c.middle : Set G)) :
    ∃ s' : L, ∃ t' : R,
      s'^2=1 ∧ t'^2=1 ∧ c.left s'∉c.middle.range ∧ c.right t'∉c.middle.range ∧
        (c.left s'*c.right t')^n=1 ∧
        orderOf (c.left s'*c.right t')=orderOf (c.left s*c.right t) ∧
        c.left s' ∈ normalizer ((Q.map (MulAut.conj b).toMonoidHom).map c.middle : Set G) ∧
        c.right t' ∈ normalizer ((Q.map (MulAut.conj b).toMonoidHom).map c.middle : Set G) := by
  let a := MulAut.conj (α.left b)
  let d := MulAut.conj (α.right b)
  let A := MulAut.conj (c.middle b)
  have ha (x : L) : c.left (a x) = A (c.left x) := by
    simp only [a,A,MulAut.conj_apply,map_mul,map_inv]
    rfl
  have hd (x : R) : c.right (d x) = A (c.right x) := by
    have hb' : c.right (α.right b) = c.middle b :=
      (DFunLike.congr_fun c.compatible b).symm
    simp only [d,A,MulAut.conj_apply,map_mul,map_inv,hb']
  have hnorm (x : G) (hx : x ∈ normalizer (Q.map c.middle : Set G)) :
      A x ∈ normalizer ((Q.map (MulAut.conj b).toMonoidHom).map c.middle : Set G) := by
    rw [c.map_conjugate_middle]
    exact le_normalizer_map A.toMonoidHom ⟨x,hx,rfl⟩
  refine ⟨a s,d t,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←map_pow,hs,map_one]
  · rw [←map_pow,ht,map_one]
  · rw [ha]
    intro h
    exact hsout ((mem_normalizer_iff.mp
      (c.middle.range.le_normalizer ⟨b,rfl⟩) (c.left s)).mpr h)
  · rw [hd]
    intro h
    exact htout ((mem_normalizer_iff.mp
      (c.middle.range.le_normalizer ⟨b,rfl⟩) (c.right t)).mpr h)
  · rw [ha,hd,←map_mul,←map_pow,hpow,map_one]
  · rw [ha,hd,←map_mul,A.orderOf_eq]
  · rw [ha]
    exact hnorm _ hsQ
  · rw [hd]
    exact hnorm _ htQ

end Theory.GroupTheory.RankTwoAmalgam.FaithfulCompletion
