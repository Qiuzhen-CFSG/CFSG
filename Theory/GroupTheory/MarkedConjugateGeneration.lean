module
public import Theory.GroupTheory.SmallMoverFamily
/-!
# Lift a marked pair of conjugate generators through the full kernel

Generation in a marked component lifts to the original residual by choosing
both conjugators in that residual. The first subgroup contains the full
homomorphism kernel, which is retained by conjugation, so image containment
implies actual containment. No complement or central-extension splitting
is required.

Source application: MS93 (5.6)(c), printed p.917, in
Sp4Four.SourceComparison.OriginalSelectedGeneration.
-/

public section
open Subgroup
namespace Subgroup
variable {D J S : Type*} [Group D] [Group J] [Group S]
theorem image_conjugate (q : D →* J) (A : Subgroup D) (g : D) :
    (A.map (MulAut.conj g).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q g)).toMonoidHom := by
  rw [map_map,map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

/-- Lift the chosen pair, retaining both exact quotient images for further
properties of the same marked conjugators. -/
theorem lift_two_conjugate_generators_with_marking
    (q : D →* J) (B : Subgroup J) (e : B ≃* S)
    (L E A : Subgroup D) (hL : L.map q = B) (hE : E.map q ≤ B) (hA : A.map q ≤ B)
    (hker : q.ker ≤ E)
    (g x : S)
    (hgen :
      (((E.map q).subgroupOf B).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ⊔
        ((A.map q).subgroupOf B).map e.toMonoidHom ⊔
        (((A.map q).subgroupOf B).map e.toMonoidHom).map (MulAut.conj x).toMonoidHom = ⊤) :
    ∃ g' ∈ L, ∃ x' ∈ L,
      q g' = (e.symm g).val ∧ q x' = (e.symm x).val ∧
      L ≤ (E.map (MulAut.conj g').toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x').toMonoidHom := by
  obtain ⟨g',hg',hgq⟩ := (show (e.symm g).val ∈ L.map q from hL.symm ▸ (e.symm g).property)
  obtain ⟨x',hx',hxq⟩ := (show (e.symm x).val ∈ L.map q from hL.symm ▸ (e.symm x).property)
  let f := B.subtype.comp e.symm.toMonoidHom
  have heE : (((E.map q).subgroupOf B).map e.toMonoidHom).map f = E.map q := by
    rw [map_map]
    have hf : f.comp e.toMonoidHom = B.subtype := by ext z; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hE]
  have heA : (((A.map q).subgroupOf B).map e.toMonoidHom).map f = A.map q := by
    rw [map_map]
    have hf : f.comp e.toMonoidHom = B.subtype := by ext z; simp [f]
    rw [hf,map_subgroupOf_eq_of_le hA]
  have hf : f.range = B := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr e.symm.surjective,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgen' := congrArg (Subgroup.map f) hgen
  rw [map_sup,map_sup,image_conjugate,image_conjugate,heE,heA,←MonoidHom.range_eq_map,hf] at hgen'
  have hmap : L.map q ≤
      ((E.map (MulAut.conj g').toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x').toMonoidHom).map q := by
    rw [map_sup,map_sup,image_conjugate,image_conjugate,hgq,hxq,hL]
    exact hgen'.ge
  have hk : q.ker ≤ E.map (MulAut.conj g').toMonoidHom := by
    intro y hy
    refine ⟨g'⁻¹*y*g',hker ?_,?_⟩
    · change q (g'⁻¹*y*g') = 1
      simp [show q y=1 from hy]
    · change g'*(g'⁻¹*y*g')*g'⁻¹=y
      simp [mul_assoc]
  refine ⟨g',hg',x',hx',hgq,hxq,?_⟩
  have h := map_le_map_iff.mp hmap
  rwa [sup_eq_left.mpr (hk.trans (le_sup_left.trans le_sup_left))] at h
theorem lift_two_conjugate_generators
    (q : D →* J) (B : Subgroup J) (e : B ≃* S)
    (L E A : Subgroup D) (hL : L.map q = B) (hE : E.map q ≤ B) (hA : A.map q ≤ B)
    (hker : q.ker ≤ E)
    (hg : ∃ g x : S,
      (((E.map q).subgroupOf B).map e.toMonoidHom).map (MulAut.conj g).toMonoidHom ⊔
        ((A.map q).subgroupOf B).map e.toMonoidHom ⊔
        (((A.map q).subgroupOf B).map e.toMonoidHom).map (MulAut.conj x).toMonoidHom = ⊤) :
    ∃ g ∈ L, ∃ x ∈ L,
      L ≤ (E.map (MulAut.conj g).toMonoidHom ⊔ A) ⊔ A.map (MulAut.conj x).toMonoidHom := by
  obtain ⟨g,x,hgen⟩ := hg
  obtain ⟨g',hg',x',hx',_,_,h⟩ := lift_two_conjugate_generators_with_marking
    q B e L E A hL hE hA hker g x hgen
  exact ⟨g',hg',x',hx',h⟩
end Subgroup
