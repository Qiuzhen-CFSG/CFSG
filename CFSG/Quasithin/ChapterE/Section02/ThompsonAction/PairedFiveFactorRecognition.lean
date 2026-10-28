module
public import Theory.GroupTheory.MarkedProductAxisPreimage
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FiveSectionRecognition

/-!
# Dihedral recognition of the actual marked factor intersections

A full-preimage subgroup marked by a pair of transposition four-groups
intersects either full symmetric factor in its exact four-group preimage.
Faithful natural-kernel recognition identifies that actual intersection
with two dihedral groups of order eight, retaining the original quotient.
Source: Aschbacher–Smith10.2.1,p.743.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open BinaryPermutation.AlternatingFiveExtension
variable {G H : Type*} [Group G] [Finite G] [Group H]
set_option backward.isDefEq.respectTransparency false

theorem marked_first_baumann_factor
    (q : G →* H) (Y : Subgroup H)
    (em : Y ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))
    (P R : Subgroup G) (a b : Equiv.Perm (Fin 5))
    (hP : P.map q = ((⊤ : Subgroup (Equiv.Perm (Fin 5))).prod ⊥).map
      (Y.subtype.comp em.symm.toMonoidHom))
    (hR : R = ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp em.symm.toMonoidHom)).comap q)
    (f : P →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hfcoord : ∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (em ⟨q (g:G),hg⟩).1)
    (ek : f.ker ≃* V)
    (he : ∀ g v, ek (MulAut.conjNormal g v) = coreAction (f g) (ek v)) :
    Nonempty ((R ⊓ P : Subgroup G) ≃* DihedralGroup 4 × DihedralGroup 4) := by
  have hp : R.subgroupOf P = ((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).comap f := by
    rw [hR]
    exact marked_first_axis_preimage q Y em P hP f hfcoord _ _
  obtain ⟨e⟩ := ChapterB.Offenders.conjugate_D_five_preimage_dihedral_square f hf ek he a
  have hRP : (R ⊓ P).subgroupOf P = R.subgroupOf P := by ext x; simp
  exact ⟨(subgroupOfEquivOfLe (show R ⊓ P ≤ P from inf_le_right)).symm.trans
    ((MulEquiv.subgroupCongr (hRP.trans hp)).trans e)⟩
theorem marked_second_baumann_factor
    (q : G →* H) (Y : Subgroup H)
    (em : Y ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 5))
    (P R : Subgroup G) (a b : Equiv.Perm (Fin 5))
    (hP : P.map q = ((⊥ : Subgroup (Equiv.Perm (Fin 5))).prod ⊤).map
      (Y.subtype.comp em.symm.toMonoidHom))
    (hR : R = ((((ChapterB.Offenders.D 5).map (MulAut.conj a).toMonoidHom).prod
      ((ChapterB.Offenders.D 5).map (MulAut.conj b).toMonoidHom)).map
        (Y.subtype.comp em.symm.toMonoidHom)).comap q)
    (f : P →* Equiv.Perm (Fin 5)) (hf : Function.Surjective f)
    (hfcoord : ∀ g : P, ∀ hg : q (g:G) ∈ Y, f g = (em ⟨q (g:G),hg⟩).2)
    (ek : f.ker ≃* V)
    (he : ∀ g v, ek (MulAut.conjNormal g v) = coreAction (f g) (ek v)) :
    Nonempty ((R ⊓ P : Subgroup G) ≃* DihedralGroup 4 × DihedralGroup 4) := by
  apply marked_first_baumann_factor q Y (em.trans MulEquiv.prodComm) P R b a _ _ f hf hfcoord ek he
  · rw [hP]
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩
  · rw [hR]
    congr 1
    ext x
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v.2,v.1),⟨hv.2,hv.1⟩,rfl⟩

end CFSG.Quasithin.ChapterE.ThompsonAction
