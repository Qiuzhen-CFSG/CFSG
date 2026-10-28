module

public import Theory.ElementaryAbelian.Join
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.IndexNormal

/-!
# Elementary fours exchanged across an index-two subgroup

Let E be an elementary four in an index-two subgroup C, normalized by C.
If E is disjoint from its conjugate by an element outside C, the two fours
commute: both are normal in C. Their join has order sixteen and is normal
in the ambient group, since the outer element exchanges the two factors.

This is the elementary orbit obstruction for the split-inversion alternative
in the C₄-square action calculation of Janko–Thompson, Math. Z. 113 (1970),
Theorem 1.3(a), printed p.386; MacWilliams, Trans. AMS 150 (1970),
DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
namespace Subgroup

/-- Disjoint conjugate elementary fours, normal in a common index-two subgroup,
generate a normal elementary sixteen. -/
public theorem exists_normal_elementary_sixteen_of_disjoint_conjugate_four {P : Type*} [Group P] [Finite P]
    (C E : Subgroup P) (hC : C.index = 2) (hEC : E ≤ C)
    (hCE : C ≤ normalizer (E : Set P)) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 4) (t : P) (ht : t ∉ C)
    (hdis : Disjoint E (E.map (MulAut.conj t).toMonoidHom)) :
    ∃ N : Subgroup P, N.Normal ∧ IsElementaryAbelian 2 N ∧ Nat.card N = 16 := by
  let : C.Normal := C.normal_of_index_eq_two hC
  let F := E.map (MulAut.conj t).toMonoidHom
  have hFC : F ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact (inferInstance : C.Normal).conj_mem x (hEC hx) t
  have hCF : C ≤ normalizer (F : Set P) := by
    rw [show F = E.map (MulAut.conj t).toMonoidHom from rfl,
      ← E.map_equiv_normalizer_eq (MulAut.conj t)]
    intro c hc
    refine ⟨(MulAut.conj t).symm c, hCE ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
    simpa using (inferInstance : C.Normal).conj_mem c hc t⁻¹
  have hcomm : F ≤ centralizer (E : Set P) := by
    intro y hy x hx
    have hc : x * y * x⁻¹ * y⁻¹ = 1 := by
      apply hdis.le_bot
      constructor
      · have hh := (le_normalizer_iff.mp hCE) y (hFC hy) x⁻¹ (E.inv_mem hx)
        simpa [mul_assoc] using E.mul_mem hx hh
      · exact F.mul_mem ((le_normalizer_iff.mp hCF) x (hEC hx) y hy) (F.inv_mem hy)
    have hc' : Commute x y := by
      apply mul_inv_eq_one.mp
      simpa [mul_inv_rev, mul_assoc] using hc
    exact hc'.eq
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.map (MulAut.conj t).toMonoidHom
  let N := E ⊔ F
  let : IsElementaryAbelian 2 N := IsElementaryAbelian.sup_of_le_centralizer hcomm
  have hCN : C ≤ normalizer (N : Set P) :=
    (le_inf hCE hCF).trans (normalizer_inf_normalizer_le_normalizer_sup E F)
  have htN : t ∈ normalizer (N : Set P) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (E ⊔ F).map (MulAut.conj t).toMonoidHom = E ⊔ F
    rw [Subgroup.map_sup]
    have ht2 : E.map (MulAut.conj (t * t)).toMonoidHom = E :=
      mem_normalizer_iff_map_conj_eq.mp (hCE (C.mul_self_mem_of_index_two hC t))
    have hFF : F.map (MulAut.conj t).toMonoidHom = E := by
      rw [show F = E.map (MulAut.conj t).toMonoidHom from rfl, map_map]
      convert ht2 using 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [hFF]
    exact sup_comm _ _
  have hN : N.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    by_cases hg : g ∈ C
    · exact hCN hg
    · have hgt : g * t⁻¹ ∈ C := (C.mul_mem_iff_of_index_two hC).mpr (by
        simp [hg, show t⁻¹ ∉ C by simpa using ht])
      simpa using (normalizer (N : Set P)).mul_mem (hCN hgt) htN
  refine ⟨N, hN, inferInstance, ?_⟩
  have hF : Nat.card F = 4 := by
    rw [show F = E.map (MulAut.conj t).toMonoidHom from rfl,
      card_map_of_injective (MulAut.conj t).injective, hE]
  have hp := card_mul_eq_card_inf_mul_card_sup_of_normalizes E F (hFC.trans hCE)
  rw [hE, hF, hdis.eq_bot, Nat.card_eq_fintype_card] at hp
  simpa using hp.symm

end Subgroup
