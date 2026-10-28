module
public import Theory.GroupTheory.Centralizer
public import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Conjugating a section of an actual subgroup image

A homomorphic section from the image of P under a fixed homomorphism q
to P transports to every prescribed conjugate of P. The image and source
are conjugated simultaneously, so the original map q is retained. No
surjectivity of q on the ambient group is required. For a normal N, this
applies directly to N ∩ C(A) and N ∩ C(Aᵗ).

Source application: the two actual factor centralizers in
Aschbacher–Smith 10.2.1, pp.742–743.
-/

public noncomputable section
open Subgroup
namespace Theory.GroupTheory
variable {G H : Type*} [Group G] [Group H]

/-- Transport an actual image section along the prescribed ambient
conjugator while preserving the original quotient map. -/
theorem exists_image_section_conjugate
    (q : G →* H) (P : Subgroup G) (t : G)
    (σ : P.map q →* P)
    (hσ : (q.comp P.subtype).comp σ = (P.map q).subtype) :
    let P' := P.map (MulAut.conj t).toMonoidHom
    ∃ σ' : P'.map q →* P', (q.comp P'.subtype).comp σ' = (P'.map q).subtype := by
  let P' := P.map (MulAut.conj t).toMonoidHom
  have him : P'.map q = (P.map q).map (MulAut.conj (q t)).toMonoidHom := by
    change (P.map (MulAut.conj t).toMonoidHom).map q = _
    rw [map_map,map_map]
    congr 1
    ext x
    change q (t*x*t⁻¹) = q t*q x*(q t)⁻¹
    rw [map_mul,map_mul,map_inv]
  let α : P ≃* P' := (MulAut.conj t).subgroupMap P
  let β : P.map q ≃* P'.map q :=
    ((MulAut.conj (q t)).subgroupMap (P.map q)).trans (MulEquiv.subgroupCongr him.symm)
  have hβ (y : P.map q) : (β y : H) = q t * (y : H) * (q t)⁻¹ := rfl
  have hσval (y : P.map q) : q ((σ y : P) : G) = (y : H) := DFunLike.congr_fun hσ y
  refine ⟨α.toMonoidHom.comp (σ.comp β.symm.toMonoidHom),?_⟩
  apply MonoidHom.ext
  intro x
  change q (t * ((σ (β.symm x) : P) : G) * t⁻¹) = (x : H)
  rw [map_mul,map_mul,map_inv,hσval]
  exact (hβ (β.symm x)).symm.trans (congrArg Subtype.val (β.apply_symm_apply x))

/-- Intersecting a normal subgroup with an actual centralizer commutes
with the prescribed conjugation. -/
theorem inf_centralizer_conjugate (N A : Subgroup G) [N.Normal] (t : G) :
    (N ⊓ centralizer (A : Set G)).map (MulAut.conj t).toMonoidHom =
      N ⊓ centralizer (A.map (MulAut.conj t).toMonoidHom : Set G) := by
  have hn : N.map (MulAut.conj t).toMonoidHom = N :=
    normal_iff_map_conj_eq.mp (inferInstance : N.Normal) t
  rw [map_inf _ _ _ (MulAut.conj t).injective,hn]
  congr 1
  let e := MulAut.conj t
  change (centralizer (A : Set G)).map e.toMonoidHom = centralizer (A.map e.toMonoidHom : Set G)
  ext g
  rw [mem_map_equiv]
  constructor
  · intro hg a ha
    obtain ⟨b,hb,rfl⟩ := ha
    have hh := congrArg e (hg b hb)
    change e b * g = g * e b
    simpa only [map_mul,e.apply_symm_apply] using hh
  · intro hg a ha
    apply e.injective
    have hh := hg (e a) (mem_map_of_mem e.toMonoidHom ha)
    simpa only [map_mul,e.apply_symm_apply] using hh

/-- The same intersection identity when normality is replaced by the exact
map equality for the subgroup being transported. -/
theorem inf_centralizer_conjugate_of_map_eq
    (N A : Subgroup G) (t : G) (hN : N.map (MulAut.conj t).toMonoidHom = N) :
    (N ⊓ centralizer (A : Set G)).map (MulAut.conj t).toMonoidHom =
      N ⊓ centralizer (A.map (MulAut.conj t).toMonoidHom : Set G) := by
  rw [map_inf _ _ _ (MulAut.conj t).injective,hN]
  congr 1
  let e := MulAut.conj t
  change (centralizer (A : Set G)).map e.toMonoidHom =
    centralizer (A.map e.toMonoidHom : Set G)
  ext g
  rw [mem_map_equiv]
  constructor
  · intro hg a ha
    obtain ⟨b,hb,rfl⟩ := ha
    have hh := congrArg e (hg b hb)
    change e b * g = g * e b
    simpa only [map_mul,e.apply_symm_apply] using hh
  · intro hg a ha
    apply e.injective
    have hh := hg (e a) (mem_map_of_mem e.toMonoidHom ha)
    simpa only [map_mul,e.apply_symm_apply] using hh

/-- A section for one factor centralizer supplies the section for its
prescribed conjugate, with both literal image subgroups retained. -/
theorem exists_centralizer_image_section_conjugate
    (q : G →* H) (N A : Subgroup G) [N.Normal] (t : G)
    (σ : (N ⊓ centralizer (A : Set G)).map q →* ↥(N ⊓ centralizer (A : Set G)))
    (hσ : (q.comp (N ⊓ centralizer (A : Set G)).subtype).comp σ =
      ((N ⊓ centralizer (A : Set G)).map q).subtype) :
    let P' := N ⊓ centralizer (A.map (MulAut.conj t).toMonoidHom : Set G)
    ∃ σ' : P'.map q →* P', (q.comp P'.subtype).comp σ' = (P'.map q).subtype := by
  have h := exists_image_section_conjugate q (N ⊓ centralizer (A : Set G)) t σ hσ
  dsimp only at h ⊢
  rw [inf_centralizer_conjugate N A t] at h
  exact h

end Theory.GroupTheory
