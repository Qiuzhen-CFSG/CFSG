module

public import Theory.GroupTheory.DisjointCommutingProduct
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Mathlib.GroupTheory.Solvable

/-!
# Solvable projections in two interchanged factors

Fix multiplication coordinates `A × B ≃* (A ⊔ B)`. For an ambient subgroup
`H`, project `H ∩ (A ⊔ B)` onto each factor, retaining both the intrinsic
subgroups and their ambient images. An element belongs to an ambient projection
exactly when it can be completed by an element of the other factor to lie in
`H`. This characterization makes the projections covariant under automorphisms
that preserve `H` and fix or interchange the factors.

For `H = U ⊔ S`, with `S` Sylow, solvability descends to both projections.
Subnormality of the factors supplies contained Sylow subgroups. A specified
factor-interchanging element of `S` exchanges the actual projections, so either
projection being a two-group would force both, and then `U`, to be two-groups.

This is the group-theoretic projection step used to choose compatible
parabolics in the PSL₃(2) case of Aschbacher–Smith, combined manuscript of
1 March 2004, 13.8.16(1), printed p.952 (PDF p.969). No model recognition or
parabolic classification is assumed here. The supplied multiplication
equivalence already encodes disjointness of the factors.
-/

@[expose] public section

open Subgroup
namespace Subgroup.MultiplicationProjections
variable {G : Type*} [Group G] {A B : Subgroup G}

/-- The actual first coordinate image of the restriction of `H` to `A ⊔ B`. -/
abbrev left (e : A × B ≃* ↥(A ⊔ B)) (H : Subgroup G) : Subgroup A :=
  (H.subgroupOf (A ⊔ B)).map ((MonoidHom.fst A B).comp e.symm.toMonoidHom)

/-- The actual second coordinate image of the restriction of `H` to `A ⊔ B`. -/
abbrev right (e : A × B ≃* ↥(A ⊔ B)) (H : Subgroup G) : Subgroup B :=
  (H.subgroupOf (A ⊔ B)).map ((MonoidHom.snd A B).comp e.symm.toMonoidHom)

/-- The first projection with its specified embedding into the ambient group. -/
abbrev leftAmbient (e : A × B ≃* ↥(A ⊔ B)) (H : Subgroup G) : Subgroup G :=
  (left e H).map A.subtype

/-- The second projection with its specified embedding into the ambient group. -/
abbrev rightAmbient (e : A × B ≃* ↥(A ⊔ B)) (H : Subgroup G) : Subgroup G :=
  (right e H).map B.subtype

variable (e : A × B ≃* ↥(A ⊔ B))
  (he : ∀ a b, (e (a, b) : G) = (a : G) * (b : G))

include he

private theorem coordinates_mul (x : ↥(A ⊔ B)) :
    ((e.symm x).1 : G) * ((e.symm x).2 : G) = (x : G) := by
  calc
    _ = (e (e.symm x) : G) := (he _ _).symm
    _ = (x : G) := congrArg Subtype.val (e.apply_symm_apply x)

/-- Membership in the first projection is witnessed by completing a product in `H`. -/
theorem mem_leftAmbient_iff (H : Subgroup G) (x : G) :
    x ∈ leftAmbient e H ↔ x ∈ A ∧ ∃ b ∈ B, x * b ∈ H := by
  constructor
  · rintro ⟨a, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(e.symm y).1.property, (e.symm y).2, (e.symm y).2.property, ?_⟩
    change ((e.symm y).1 : G) * ((e.symm y).2 : G) ∈ H
    rwa [coordinates_mul e he]
  · rintro ⟨ha, b, hb, hab⟩
    refine ⟨⟨x, ha⟩, ⟨e (⟨x, ha⟩, ⟨b, hb⟩), ?_, ?_⟩, rfl⟩
    · change (e (⟨x, ha⟩, ⟨b, hb⟩) : G) ∈ H
      rwa [he]
    · exact congrArg Prod.fst (e.symm_apply_apply (⟨x, ha⟩, ⟨b, hb⟩))

/-- Commutation gives the same product-witness description for the second projection. -/
theorem mem_rightAmbient_iff (hc : A ≤ centralizer (B : Set G))
    (H : Subgroup G) (x : G) :
    x ∈ rightAmbient e H ↔ x ∈ B ∧ ∃ a ∈ A, x * a ∈ H := by
  constructor
  · rintro ⟨b, ⟨y, hy, rfl⟩, rfl⟩
    refine ⟨(e.symm y).2.property, (e.symm y).1, (e.symm y).1.property, ?_⟩
    change ((e.symm y).2 : G) * ((e.symm y).1 : G) ∈ H
    rw [hc (e.symm y).1.property _ (e.symm y).2.property, coordinates_mul e he]
    exact hy
  · rintro ⟨hb, a, ha, hba⟩
    refine ⟨⟨x, hb⟩, ⟨e (⟨a, ha⟩, ⟨x, hb⟩), ?_, ?_⟩, rfl⟩
    · change (e (⟨a, ha⟩, ⟨x, hb⟩) : G) ∈ H
      rw [he, ← hc ha x hb]
      exact hba
    · exact congrArg Prod.snd (e.symm_apply_apply (⟨a, ha⟩, ⟨x, hb⟩))

omit he in
private theorem map_eq_of_factor_witnesses
    (H D E D' E' P Q : Subgroup G) (f : G ≃* G)
    (hP : ∀ x, x ∈ P ↔ x ∈ D ∧ ∃ y ∈ E, x * y ∈ H)
    (hQ : ∀ x, x ∈ Q ↔ x ∈ D' ∧ ∃ y ∈ E', x * y ∈ H)
    (hH : H.map f.toMonoidHom = H)
    (hD : D.map f.toMonoidHom = D') (hE : E.map f.toMonoidHom = E') :
    P.map f.toMonoidHom = Q := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hzD, y, hyE, hzy⟩ := (hP z).mp hz
    apply (hQ (f z)).mpr
    refine ⟨hD ▸ mem_map_of_mem f.toMonoidHom hzD, f y,
      hE ▸ mem_map_of_mem f.toMonoidHom hyE, ?_⟩
    rw [← map_mul]
    exact hH ▸ mem_map_of_mem f.toMonoidHom hzy
  · intro hx
    obtain ⟨hxD, y, hyE, hxy⟩ := (hQ x).mp hx
    obtain ⟨z, hz, rfl⟩ := hD.symm ▸ hxD
    obtain ⟨w, hw, rfl⟩ := hE.symm ▸ hyE
    refine ⟨z, (hP z).mpr ⟨hz, w, hw, ?_⟩, rfl⟩
    have hm : f (z * w) ∈ H.map f.toMonoidHom := by
      rw [hH, map_mul]
      exact hxy
    obtain ⟨v, hv, hvw⟩ := hm
    exact f.injective hvw ▸ hv

/-- An automorphism preserving the overgroup and each factor preserves both projections. -/
theorem map_eq_self_of_fixed_factors (hc : A ≤ centralizer (B : Set G)) (H : Subgroup G)
    (f : G ≃* G) (hH : H.map f.toMonoidHom = H)
    (hA : A.map f.toMonoidHom = A) (hB : B.map f.toMonoidHom = B) :
    (leftAmbient e H).map f.toMonoidHom = leftAmbient e H ∧
      (rightAmbient e H).map f.toMonoidHom = rightAmbient e H := by
  constructor
  · exact map_eq_of_factor_witnesses H A B A B _ _ f
      (mem_leftAmbient_iff e he H) (mem_leftAmbient_iff e he H) hH hA hB
  · exact map_eq_of_factor_witnesses H B A B A _ _ f
      (mem_rightAmbient_iff e he hc H) (mem_rightAmbient_iff e he hc H) hH hB hA

/-- An automorphism preserving the overgroup and exchanging the factors exchanges their
actual projected subgroups. -/
theorem map_eq_of_swapped_factors (hc : A ≤ centralizer (B : Set G)) (H : Subgroup G)
    (f : G ≃* G) (hH : H.map f.toMonoidHom = H)
    (hA : A.map f.toMonoidHom = B) (hB : B.map f.toMonoidHom = A) :
    (leftAmbient e H).map f.toMonoidHom = rightAmbient e H ∧
      (rightAmbient e H).map f.toMonoidHom = leftAmbient e H := by
  constructor
  · exact map_eq_of_factor_witnesses H A B B A _ _ f
      (mem_leftAmbient_iff e he H) (mem_rightAmbient_iff e he hc H) hH hA hB
  · exact map_eq_of_factor_witnesses H B A A B _ _ f
      (mem_rightAmbient_iff e he hc H) (mem_leftAmbient_iff e he H) hH hB hA
/-- The part of `H` already in the first factor lies in its projection. -/
theorem subgroupOf_le_left (H : Subgroup G) : H.subgroupOf A ≤ left e H := by
  intro a ha
  change (a : G) ∈ H at ha
  refine ⟨e (a, 1), ?_, ?_⟩
  · change (e (a, 1) : G) ∈ H
    simpa only [he, coe_one, mul_one] using ha
  · exact congrArg Prod.fst (e.symm_apply_apply (a, 1))

/-- The part of `H` already in the second factor lies in its projection. -/
theorem subgroupOf_le_right (H : Subgroup G) : H.subgroupOf B ≤ right e H := by
  intro b hb
  change (b : G) ∈ H at hb
  refine ⟨e (1, b), ?_, ?_⟩
  · change (e (1, b) : G) ∈ H
    simpa only [he, coe_one, one_mul] using hb
  · exact congrArg Prod.snd (e.symm_apply_apply (1, b))

/-- Every subgroup of both `H` and the factor product lies in the join of the projections. -/
theorem le_sup_projections (H U : Subgroup G) (hUN : U ≤ A ⊔ B) (hUH : U ≤ H) :
    U ≤ leftAmbient e H ⊔ rightAmbient e H := by
  intro x hx
  let y : ↥(A ⊔ B) := ⟨x, hUN hx⟩
  have hy : y ∈ H.subgroupOf (A ⊔ B) := hUH hx
  have hleft : ((e.symm y).1 : G) ∈ leftAmbient e H :=
    mem_map_of_mem A.subtype (mem_map_of_mem _ hy)
  have hright : ((e.symm y).2 : G) ∈ rightAmbient e H :=
    mem_map_of_mem B.subtype (mem_map_of_mem _ hy)
  have hm := (leftAmbient e H ⊔ rightAmbient e H).mul_mem
    ((show leftAmbient e H ≤ leftAmbient e H ⊔ rightAmbient e H from le_sup_left) hleft)
    ((show rightAmbient e H ≤ leftAmbient e H ⊔ rightAmbient e H from le_sup_right) hright)
  rwa [coordinates_mul e he y] at hm

omit he in
/-- Solvability passes from the overgroup to both actual coordinate images. -/
theorem solvable (H : Subgroup G) [Group.IsSolvable H] :
    Group.IsSolvable (left e H) ∧ Group.IsSolvable (right e H) := by
  let i : H.subgroupOf (A ⊔ B) →* H :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : H => (z : G)) h
  let : Group.IsSolvable (H.subgroupOf (A ⊔ B)) :=
    Group.isSolvable_of_isSolvable_injective hi
  exact ⟨Group.isSolvable_of_surjective
      (((MonoidHom.fst A B).comp e.symm.toMonoidHom).subgroupMap_surjective _),
    Group.isSolvable_of_surjective
      (((MonoidHom.snd A B).comp e.symm.toMonoidHom).subgroupMap_surjective _)⟩

/-- A non-p-subgroup in an invariant overgroup rules out p-group projections when an
automorphism exchanges the factors. Normalization of the projected product is proved
from commutation, rather than assumed. -/
theorem not_isPGroup_of_swapped_factors {p : ℕ} (hc : A ≤ centralizer (B : Set G))
    (H U : Subgroup G) (hUN : U ≤ A ⊔ B) (hUH : U ≤ H) (hU : ¬ IsPGroup p U)
    (f : G ≃* G) (hH : H.map f.toMonoidHom = H)
    (hA : A.map f.toMonoidHom = B) (hB : B.map f.toMonoidHom = A) :
    ¬ IsPGroup p (left e H) ∧ ¬ IsPGroup p (right e H) := by
  have hs := map_eq_of_swapped_factors e he hc H f hH hA hB
  have hn : leftAmbient e H ≤ normalizer (rightAmbient e H : Set G) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro x hx y hy
    exact hc (map_subtype_le _ hx) y (map_subtype_le _ hy)
  have hbad (hP : IsPGroup p (leftAmbient e H))
      (hQ : IsPGroup p (rightAmbient e H)) : False :=
    hU ((hP.to_sup_of_normal_right' hQ hn).to_le (le_sup_projections e he H U hUN hUH))
  constructor
  · intro hP
    have hQ := (hP.map A.subtype).map f.toMonoidHom
    rw [hs.1] at hQ
    exact hbad (hP.map A.subtype) hQ
  · intro hQ
    have hP := (hQ.map B.subtype).map f.toMonoidHom
    rw [hs.2] at hP
    exact hbad hP (hQ.map B.subtype)

end Subgroup.MultiplicationProjections

namespace Subgroup
open MultiplicationProjections
variable {G : Type*} [Group G] [Finite G]

/-- The actual projections of `(U ⊔ S) ∩ (A ⊔ B)` are solvable non-two-groups
containing Sylow subgroups of the subnormal factors. They contain `U` in their
ambient join and transform according to the action of `S` on the factors, with
the specified mover exchanging both projections. -/
theorem solvable_projections_of_swapped_factors
    (A B : Subgroup G) (hc : A ≤ centralizer (B : Set G))
    (hAn : A.IsSubnormal) (hBn : B.IsSubnormal)
    (S : Sylow 2 G) (U : Subgroup G)
    (hUN : U ≤ A ⊔ B) (hU : ¬ IsPGroup 2 U)
    (hsol : Group.IsSolvable (U ⊔ (S : Subgroup G) : Subgroup G))
    (e : A × B ≃* ↥(A ⊔ B))
    (he : ∀ a b, (e (a, b) : G) = (a : G) * (b : G))
    (hperm : ∀ s ∈ (S : Subgroup G),
      (A.map (MulAut.conj s).toMonoidHom = A ∧
        B.map (MulAut.conj s).toMonoidHom = B) ∨
      (A.map (MulAut.conj s).toMonoidHom = B ∧
        B.map (MulAut.conj s).toMonoidHom = A))
    (t : G) (ht : t ∈ (S : Subgroup G))
    (hAt : A.map (MulAut.conj t).toMonoidHom = B)
    (hBt : B.map (MulAut.conj t).toMonoidHom = A) :
    let H := U ⊔ (S : Subgroup G)
    let P := left e H
    let Q := right e H
    let P₀ := P.map A.subtype
    let Q₀ := Q.map B.subtype
    Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ¬ IsPGroup 2 P ∧ ¬ IsPGroup 2 Q ∧
      (∃ SA : Sylow 2 A, ∃ SB : Sylow 2 B,
        (SA : Subgroup A) ≤ P ∧ (SB : Subgroup B) ≤ Q) ∧
      U ≤ P₀ ⊔ Q₀ ∧
      (∀ s ∈ (S : Subgroup G),
        (A.map (MulAut.conj s).toMonoidHom = A ∧
          B.map (MulAut.conj s).toMonoidHom = B ∧
          P₀.map (MulAut.conj s).toMonoidHom = P₀ ∧
          Q₀.map (MulAut.conj s).toMonoidHom = Q₀) ∨
        (A.map (MulAut.conj s).toMonoidHom = B ∧
          B.map (MulAut.conj s).toMonoidHom = A ∧
          P₀.map (MulAut.conj s).toMonoidHom = Q₀ ∧
          Q₀.map (MulAut.conj s).toMonoidHom = P₀)) ∧
      P₀.map (MulAut.conj t).toMonoidHom = Q₀ ∧
      Q₀.map (MulAut.conj t).toMonoidHom = P₀ := by
  let H := U ⊔ (S : Subgroup G)
  have hH (s : G) (hs : s ∈ (S : Subgroup G)) :
      H.map (MulAut.conj s).toMonoidHom = H :=
    mem_normalizer_iff_map_conj_eq.mp
      (le_normalizer ((show (S : Subgroup G) ≤ H from le_sup_right) hs))
  let : Group.IsSolvable H := hsol
  have hsols := solvable e H
  have hnot := not_isPGroup_of_swapped_factors e he hc H U hUN le_sup_left hU
    (MulAut.conj t) (hH t ht) hAt hBt
  have hmoves := map_eq_of_swapped_factors e he hc H (MulAut.conj t) (hH t ht) hAt hBt
  obtain ⟨SA, hSA⟩ := S.exists_subgroupOf_eq_of_subnormal A hAn
  obtain ⟨SB, hSB⟩ := S.exists_subgroupOf_eq_of_subnormal B hBn
  refine ⟨hsols.1, hsols.2, hnot.1, hnot.2, ⟨SA, SB, ?_, ?_⟩,
    MultiplicationProjections.le_sup_projections e he H U hUN le_sup_left, ?_, hmoves.1, hmoves.2⟩
  · rw [hSA]
    exact (subgroupOf_mono A (show (S : Subgroup G) ≤ H from le_sup_right)).trans
      (subgroupOf_le_left e he H)
  · rw [hSB]
    exact (subgroupOf_mono B (show (S : Subgroup G) ≤ H from le_sup_right)).trans
      (subgroupOf_le_right e he H)
  · intro s hs
    rcases hperm s hs with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · exact Or.inl ⟨hA, hB, map_eq_self_of_fixed_factors e he hc H (MulAut.conj s) (hH s hs) hA hB⟩
    · exact Or.inr ⟨hA, hB, map_eq_of_swapped_factors e he hc H (MulAut.conj s) (hH s hs) hA hB⟩

end Subgroup

end
