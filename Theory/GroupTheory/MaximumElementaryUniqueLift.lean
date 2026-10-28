module

public import Stellmacher.ElementaryAbelianMaxPair
public import Stellmacher.ElementaryAbelianMaxOddPair
public import Stellmacher.MaxElementaryOffenderEquality
public import Theory.ElementaryAbelian.UniqueLift

/-!
# Two maximum elementary subgroups from a unique nonzero image

Let Q and W be elementary subgroups of equal order. Suppose a homomorphism
has kernel Q, W contains its centralizer in Q, and one element of W has
the same fixed subgroup in Q as W. If every maximum elementary subgroup
outside Q has the image of W, elementary lift uniqueness places it in W.
Thus the maximum family is exactly {Q,W}; neither maximality of Q nor
maximality of W is an extra premise.

The automorphism specialization obtains the order and centralizer premises
when W is an automorphic image of self-centralizing Q. An odd actor then
fixes both members of the family in the literal ambient subgroup.

Source: Aschbacher--Smith, B.2.21, printed pp.82--83, and the final paragraph
of 3.3.28, printed p.601. The intended application takes Q=O₂(LT) and
W=Qᵈ inside R=O₂(O²(C_L(Ω₁Z(T)))T).
-/

public section
open Subgroup
namespace Stellmacher
variable {G H : Type*} [Group G] [Group H] [Finite G]

/-- A common nonzero image and a detecting element give the full pair family,
without assuming in advance that either displayed member has maximum order. -/
theorem maxFamily_pair_of_unique_lift
    (Q W : Subgroup G) [IsElementaryAbelian 2 Q] [IsElementaryAbelian 2 W]
    (q : G →* H) (hker : q.ker = Q) (hcard : Nat.card Q = Nat.card W)
    (hCW : Q ⊓ centralizer (W : Set G) ≤ W)
    (a : G) (ha : a ∈ W)
    (hfix : Q ⊓ centralizer (W : Set G) = Q ⊓ centralizer ({a} : Set G))
    (hcommon : ∀ A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G),
      ¬ A ≤ Q → A.map q = W.map q) :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup G) = {Q,W} := by
  apply maxFamily_eq_pair_of_cover ⊤ Q W le_top le_top hcard
  intro A hA
  by_cases hAQ : A ≤ Q
  · exact Or.inl hAQ
  · let _ : IsElementaryAbelian 2 A := hA.2.1
    let _ : IsElementaryAbelian 2 (Q ⊓ centralizer (A : Set G) : Subgroup G) :=
      IsElementaryAbelian.of_le inf_le_left
    exact Or.inr (IsElementaryAbelian.le_of_same_image_of_centralizer_singleton
      q Q W A hker hCW
      (maxElementary_contains_elementary_centralizer ⊤ A _ hA le_top inf_le_right)
      (hcommon A hA hAQ).symm a ha hfix)

/-- For an automorphic image of self-centralizing Q, lift uniqueness alone
supplies the two-member maximum family. -/
theorem maxFamily_pair_of_automorphism_image
    (Q : Subgroup G) [IsElementaryAbelian 2 Q] (e : MulAut G)
    (q : G →* H) (hker : q.ker = Q)
    (hself : centralizer (Q : Set G) = Q)
    (a : G) (ha : a ∈ Q.map e.toMonoidHom)
    (hfix : Q ⊓ centralizer (Q.map e.toMonoidHom : Set G) =
      Q ⊓ centralizer ({a} : Set G))
    (hcommon : ∀ A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup G),
      ¬ A ≤ Q → A.map q = (Q.map e.toMonoidHom).map q) :
    elementaryAbelianMaxSubgroups (⊤ : Subgroup G) = {Q,Q.map e.toMonoidHom} := by
  let _ : IsElementaryAbelian 2 (Q.map e.toMonoidHom) := IsElementaryAbelian.map _
  apply maxFamily_pair_of_unique_lift Q _ q hker
    (card_map_of_injective e.injective).symm _ a ha hfix hcommon
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  rw [← hself]
  intro y hy
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hx.2 (e y) (mem_map_of_mem e.toMonoidHom hy)

/-- Transport the pair to the original subgroup and apply the odd-order
normalizer action. The quotient and automorphism remain maps on that subgroup. -/
theorem odd_normalizes_automorphism_pair
    (R D : Subgroup G) (Q : Subgroup R) [IsElementaryAbelian 2 Q]
    (e : MulAut R) (q : R →* H) (hker : q.ker = Q)
    (hself : centralizer (Q : Set R) = Q)
    (a : R) (ha : a ∈ Q.map e.toMonoidHom)
    (hfix : Q ⊓ centralizer (Q.map e.toMonoidHom : Set R) =
      Q ⊓ centralizer ({a} : Set R))
    (hcommon : ∀ A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R),
      ¬ A ≤ Q → A.map q = (Q.map e.toMonoidHom).map q)
    (hDR : D ≤ normalizer (R : Set G)) (hodd : Odd (Nat.card D)) :
    elementaryAbelianMaxSubgroups R =
        {Q.map R.subtype,(Q.map e.toMonoidHom).map R.subtype} ∧
      D ≤ normalizer (Q.map R.subtype : Set G) := by
  have hp := maxFamily_pair_of_automorphism_image Q e q hker hself a ha hfix hcommon
  have hpair := maxFamily_pair_equiv R (MulEquiv.refl R) Q (Q.map e.toMonoidHom) hp
  have hpair' : elementaryAbelianMaxSubgroups R =
      {Q.map R.subtype,(Q.map e.toMonoidHom).map R.subtype} := by
    have hi : R.subtype.comp (MulEquiv.refl R).toMonoidHom = R.subtype := by
      ext x
      rfl
    simpa only [hi] using hpair
  refine ⟨hpair', (odd_normalizes_maximum_pair R D _ _ hpair' ?_ hodd).1⟩
  intro d hd
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (elementaryAbelianMaxJ R).map (MulAut.conj d).toMonoidHom = _
  have hdR : R.map (MulAut.conj d).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp (hDR hd)
  exact (elementaryAbelianMaxJ_map_equiv (MulAut.conj d) R).symm.trans
    (congrArg elementaryAbelianMaxJ hdR)

/-- The same conclusion for literal ambient conjugation by d. All family
members and the quotient map are restricted to the original R. -/
theorem odd_normalizes_conjugate_pair
    (R D Q : Subgroup G) [IsElementaryAbelian 2 Q] (hQR : Q ≤ R)
    (d : G) (hdR : d ∈ normalizer (R : Set G))
    (q : R →* H) (hker : q.ker = Q.subgroupOf R)
    (hself : centralizer (Q.subgroupOf R : Set R) = Q.subgroupOf R)
    (a : R) (ha : a ∈ (Q.map (MulAut.conj d).toMonoidHom).subgroupOf R)
    (hfix : Q.subgroupOf R ⊓
        centralizer ((Q.map (MulAut.conj d).toMonoidHom).subgroupOf R : Set R) =
      Q.subgroupOf R ⊓ centralizer ({a} : Set R))
    (hcommon : ∀ A ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup R),
      ¬ A ≤ Q.subgroupOf R →
        A.map q = ((Q.map (MulAut.conj d).toMonoidHom).subgroupOf R).map q)
    (hDR : D ≤ normalizer (R : Set G)) (hodd : Odd (Nat.card D)) :
    elementaryAbelianMaxSubgroups R = {Q,Q.map (MulAut.conj d).toMonoidHom} ∧
      D ≤ normalizer (Q : Set G) := by
  let e := R.normalizerMonoidHom ⟨d,hdR⟩
  let _ : IsElementaryAbelian 2 (Q.subgroupOf R) :=
    IsElementaryAbelian.subgroupOf hQR
  have hmap : ((Q.subgroupOf R).map e.toMonoidHom).map R.subtype =
      Q.map (MulAut.conj d).toMonoidHom := by
    have he : R.subtype.comp e.toMonoidHom =
        (MulAut.conj d).toMonoidHom.comp R.subtype := by
      ext x
      rfl
    rw [map_map,he,← map_map,map_subgroupOf_eq_of_le hQR]
  have he : (Q.subgroupOf R).map e.toMonoidHom =
      (Q.map (MulAut.conj d).toMonoidHom).subgroupOf R := by
    rw [← hmap]
    exact (comap_map_eq_self_of_injective R.subtype_injective _).symm
  have hp := odd_normalizes_automorphism_pair R D (Q.subgroupOf R) e q hker hself
    a (he.symm ▸ ha) (by rw [he]; exact hfix)
    (by intro A hA hn; rw [he]; exact hcommon A hA hn) hDR hodd
  simpa only [map_subgroupOf_eq_of_le hQR,hmap] using hp

end Stellmacher
