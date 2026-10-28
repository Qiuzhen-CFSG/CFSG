module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction

/-!
# Sylow conjugacy preserving an odd Hall subgroup

Suppose N normalizes a solvable subgroup C, and a Sylow two-subgroup R
of C lies in the target Sylow U. Conjugate T to U inside N. Hall
conjugacy factors this conjugator as r x, with r in R and x normalizing
the specified odd Hall subgroup A of C. Since r lies in U, x still
conjugates T to U.

Source application: the changed-Sylow argument of Aschbacher--Smith
5.2.2, printed p.648, with N=N_G(T₀) and C=N_L(T∩L).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

/-- Sylow conjugacy can preserve a specified odd Hall subgroup of a normalized
solvable subgroup whose Sylow image lies in the target Sylow. -/
theorem sylow_conjugate_fixing_hall
    (N C R A : Subgroup G) (T U : Sylow 2 G)
    (hTN : (T : Subgroup G) ≤ N) (hUN : (U : Subgroup G) ≤ N)
    (hRU : R ≤ (U : Subgroup G))
    (hNC : N ≤ normalizer (C : Set G))
    (hsolv : Group.IsSolvable C)
    (P : Sylow 2 C) (hP : (P : Subgroup C).map C.subtype = R)
    (hAC : A ≤ C) (hA : IsHallSubgroup oddPrimes (A.subgroupOf C)) :
    ∃ x : G, x ∈ N ∧ x ∈ normalizer (A : Set G) ∧
      (T : Subgroup G).map (MulAut.conj x).toMonoidHom = (U : Subgroup G) := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq N (T.subtype hTN) (U.subtype hUN)
  have hmap : (T : Subgroup G).map (MulAut.conj (g : G)).toMonoidHom =
      (U : Subgroup G) := by
    have hh := congrArg (fun Q : Sylow 2 N => (Q : Subgroup N).map N.subtype) hg
    change (((T : Subgroup G).subgroupOf N).map (MulAut.conj g).toMonoidHom).map
      N.subtype = ((U : Subgroup G).subgroupOf N).map N.subtype at hh
    rw [map_map] at hh
    have he : N.subtype.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (g : G)).toMonoidHom.comp N.subtype := rfl
    rw [he,←map_map,map_subgroupOf_eq_of_le hTN,map_subgroupOf_eq_of_le hUN] at hh
    exact hh
  have hfr := normal_sylow_frattini C R N A hsolv (hRU.trans hUN) hNC P hP hAC hA
  obtain ⟨r,hr,x,hx,hgx⟩ := (congrArg (fun S : Set G => (g : G) ∈ S) hfr).mp g.property
  refine ⟨x,hx.1,hx.2,?_⟩
  have he := congrArg (map (MulAut.conj r⁻¹).toMonoidHom) hmap
  rw [map_map] at he
  have hc : (MulAut.conj r⁻¹).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom =
      (MulAut.conj x).toMonoidHom := by
    rw [←hgx]
    ext y
    simp [MulAut.conj_apply,mul_assoc]
  rw [hc] at he
  exact he.trans (mem_normalizer_iff_map_conj_eq.mp
    ((U : Subgroup G).le_normalizer ((U : Subgroup G).inv_mem (hRU hr))))

end Subgroup.OddHall
