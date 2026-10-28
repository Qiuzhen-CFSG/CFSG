module
public import Theory.SpecificGroups.SymmetricEight.FourPointComplement
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Tactic

/-!
# A three-letter overgroup of a transposition in S8

The permutations supported on three selected letters form an actual S3.
Adjoining the centralizer of a transposition on two of those letters gives
all adjacent transpositions, hence S8. Conjugacy transports the construction
to any prescribed transposition, retaining its cyclic subgroup.

This is the quotient overgroup used to begin the block argument in
Aschbacher--Smith12.6.18, printed p.827, combined manuscript of1 March2004.
-/

public noncomputable section
open Subgroup Equiv Equiv.Perm
namespace Theory.SpecificGroups.SymmetricEight.TranspositionThree

private def triple : Subgroup (Perm (Fin 8)) :=
  FourPointComplement.symmetric ({0,1,2} : Finset (Fin 8))

private def tripleEquiv : triple ≃* Perm (Fin 3) :=
  (MonoidHom.ofInjective (ofSubtype_injective (p := (· ∈ ({0,1,2} : Finset (Fin 8)))))).symm.trans
    (Fintype.equivFinOfCardEq (by decide : Fintype.card ({0,1,2} : Finset (Fin 8)) = 3)).permCongrHom

private theorem swap_mem_triple : swap (0 : Fin 8) 1 ∈ triple :=
  FourPointComplement.swap_mem_symmetric _ (by simp) (by simp)

private theorem triple_generates :
    triple ⊔ centralizer ({swap (0 : Fin 8) 1} : Set (Perm (Fin 8))) = ⊤ := by
  have hgen := Subgroup.closure_eq_top_of_mclosure_eq_top (mclosure_swap_castSucc_succ 7)
  rw [eq_top_iff,←hgen,Subgroup.closure_le]
  rintro _ ⟨i,rfl⟩
  fin_cases i
  · exact mem_sup_left swap_mem_triple
  · exact mem_sup_left (FourPointComplement.swap_mem_symmetric _ (by simp) (by simp))
  all_goals
    exact mem_sup_right (mem_centralizer_singleton_iff.mpr (by decide))

/-- A transposition lies in an actual S3 which generates S8 together with
its full centralizer. -/
theorem exists_three_overgroup (t : Perm (Fin 8)) (ht : t.IsSwap) :
    ∃ X : Subgroup (Perm (Fin 8)), Nonempty (X ≃* Perm (Fin 3)) ∧
      zpowers t ≤ X ∧ X ⊔ centralizer ({t} : Set (Perm (Fin 8))) = ⊤ := by
  have hconj : IsConj (swap (0 : Fin 8) 1) t :=
    isConj_iff_cycleType_eq.mpr
      ((isSwap_iff_cycleType.mp (swap_isSwap_iff.mpr (by decide : (0 : Fin 8) ≠ 1))).trans
        (isSwap_iff_cycleType.mp ht).symm)
  obtain ⟨c,hc⟩ := isConj_iff.mp hconj
  let f := (MulAut.conj c).toMonoidHom
  let X := triple.map f
  have hf : f (swap (0 : Fin 8) 1) = t := hc
  have hcent : (centralizer ({swap (0 : Fin 8) 1} : Set (Perm (Fin 8)))).map f ≤
      centralizer ({t} : Set (Perm (Fin 8))) := by
    rintro _ ⟨x,hx,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    rw [←hf,←map_mul,←map_mul]
    exact congrArg f (mem_centralizer_singleton_iff.mp hx)
  refine ⟨X,⟨(triple.equivMapOfInjective f (MulAut.conj c).injective).symm.trans tripleEquiv⟩,
    zpowers_le.mpr (hf ▸ mem_map_of_mem f swap_mem_triple),?_⟩
  have hh := congrArg (Subgroup.map f) triple_generates
  rw [Subgroup.map_sup,map_top_of_surjective f (MulAut.conj c).surjective] at hh
  exact top_unique (hh ▸ sup_le_sup_left hcent _)
end Theory.SpecificGroups.SymmetricEight.TranspositionThree
