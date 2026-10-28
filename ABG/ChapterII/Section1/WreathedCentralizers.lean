module
public import ABG.ChapterII.Section1.WreathedOuterFour

/-!
# Centralizers in a wreathed group

For the chosen wreathed presentation, every noncentral element has abelian
centralizer. These coordinate facts support ABG Chapter II §1 Lemma 2(ii)
and (xii), article pp.9–10, on the distinguished abelian base and centers of
nonabelian subgroups.

A base element commuting with an outer element commutes with the swapping
involution after cancelling the outer element's base factor. It therefore
commutes with all normal forms and is central. For two outer elements their
quotient lies in the base. Consequently elements centralizing a fixed outer
element differ from its powers by central elements, and commute with each
other. A noncentral base element has its centralizer contained in the abelian
base. These arguments use the exact chosen presentation and base coordinates.
-/

namespace ABG.Wreathed.Presentation
variable {S : Type*} [Group S] {n : ℕ} (P : Presentation S n)

private theorem normal_base_mem (i j : ℕ) : P.s ^ i * P.t ^ j ∈ P.U :=
  (P.mem_U_iff _).mpr ⟨i,j,by simp⟩

private theorem central_of_base_commute_z {a : S} (ha : a ∈ P.U)
    (hz : Commute a P.z) : a ∈ Subgroup.center S := by
  rw [Subgroup.mem_center_iff]
  intro g
  rcases P.exists_normal_form g with ⟨i,j,b,rfl⟩
  exact ((P.commute_of_mem_U (P.normal_base_mem i.val j.val) ha).mul_left
    (hz.symm.pow_left b.val)).eq

public theorem base_commute_outer_mem_center {a b : S} (ha : a ∈ P.U)
    (hb : b ∉ P.U) (hab : Commute a b) : a ∈ Subgroup.center S := by
  apply P.central_of_base_commute_z ha
  rcases P.exists_outer_normal_form hb with ⟨i,j,rfl⟩
  have hav := P.commute_of_mem_U ha (P.normal_base_mem i j)
  change a * P.z = P.z * a
  apply mul_left_cancel (a := P.s ^ i * P.t ^ j)
  calc
    _ = a * (P.s ^ i * P.t ^ j * P.z) := by rw [← mul_assoc, ← hav.eq, mul_assoc]
    _ = _ := by rw [hab.eq]; group

public theorem outer_mul_inv_mem_base {a b : S} (ha : a ∉ P.U)
    (hb : b ∉ P.U) : a * b⁻¹ ∈ P.U := by
  rcases P.exists_outer_normal_form ha with ⟨i,j,rfl⟩
  rcases P.exists_outer_normal_form hb with ⟨k,l,rfl⟩
  have he : (P.s ^ i * P.t ^ j * P.z) * (P.s ^ k * P.t ^ l * P.z)⁻¹ =
      (P.s ^ i * P.t ^ j) * (P.s ^ k * P.t ^ l)⁻¹ := by group
  rw [he]
  exact P.U.mul_mem (P.normal_base_mem i j) (P.U.inv_mem (P.normal_base_mem k l))

public theorem commute_of_commute_outer {a b c : S} (ha : a ∉ P.U)
    (hab : Commute a b) (hac : Commute a c) : Commute b c := by
  by_cases hb : b ∈ P.U
  · exact ((Subgroup.mem_center_iff.mp (P.base_commute_outer_mem_center hb ha hab.symm)) c).symm
  have hba : b * a⁻¹ ∈ Subgroup.center S :=
    P.base_commute_outer_mem_center (P.outer_mul_inv_mem_base hb ha) ha
      ((hab.symm).mul_left (Commute.refl a).inv_left)
  have hbc : Commute (b * a⁻¹) c := ((Subgroup.mem_center_iff.mp hba) c).symm
  simpa using hbc.mul_left hac

include P in
public theorem commute_of_commute_noncentral {a b c : S}
    (ha : a ∉ Subgroup.center S) (hab : Commute a b) (hac : Commute a c) :
    Commute b c := by
  by_cases hau : a ∈ P.U
  · have hb : b ∈ P.U := by
      by_contra h
      exact ha (P.base_commute_outer_mem_center hau h hab)
    have hc : c ∈ P.U := by
      by_contra h
      exact ha (P.base_commute_outer_mem_center hau h hac)
    exact P.commute_of_mem_U hb hc
  · exact P.commute_of_commute_outer hau hab hac

end ABG.Wreathed.Presentation
