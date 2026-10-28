module
public import Theory.GroupTheory.DisjointCommutingProduct

/-!
# Projection from an internal direct product

For commuting, disjoint subgroups spanning a subgroup S, multiplication identifies
S with their external product. The first projection is surjective, has the second
factor as its literal kernel, and fixes the first factor.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G]

theorem exists_projection_of_disjoint_commuting_product
    (S F D : Subgroup G) (hspan : S = F ⊔ D) (hdisj : Disjoint F D)
    (hcomm : F ≤ centralizer (D : Set G)) :
    ∃ f : S →* F, Function.Surjective f ∧ f.ker = D.subgroupOf S ∧
      ∀ s : S, (s : G) ∈ F → (f s : G) = (s : G) := by
  obtain ⟨e, he⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting F D hdisj hcomm
  let eS : F × D ≃* S := e.trans (MulEquiv.subgroupCongr hspan.symm)
  have heS (a : F) (b : D) : (eS (a,b) : G) = (a : G) * (b : G) := he a b
  let f : S →* F := (MonoidHom.fst F D).comp eS.symm.toMonoidHom
  have hf (a : F) (b : D) : f (eS (a,b)) = a := by
    change (eS.symm (eS (a,b))).1 = a
    rw [eS.symm_apply_apply]
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    exact ⟨eS (a,1), hf a 1⟩
  · ext s
    obtain ⟨⟨a,b⟩, rfl⟩ := eS.surjective s
    change f (eS (a,b)) = 1 ↔ (eS (a,b) : G) ∈ D
    rw [hf, heS]
    constructor
    · rintro rfl
      simp
    · intro hab
      have haD : (a : G) ∈ D := by simpa using D.mul_mem hab (D.inv_mem b.property)
      apply Subtype.ext
      exact (show (a : G) ∈ (⊥ : Subgroup G) from hdisj.eq_bot ▸ ⟨a.property, haD⟩)
  · intro s hs
    obtain ⟨⟨a,b⟩, rfl⟩ := eS.surjective s
    rw [heS] at hs ⊢
    rw [hf]
    have hbF : (b : G) ∈ F := by simpa using F.mul_mem (F.inv_mem a.property) hs
    have hb1 : (b : G) = 1 :=
      (show (b : G) ∈ (⊥ : Subgroup G) from hdisj.eq_bot ▸ ⟨hbF, b.property⟩)
    rw [hb1, mul_one]
end Subgroup
