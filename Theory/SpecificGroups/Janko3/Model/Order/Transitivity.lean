module

public import Theory.SpecificGroups.Janko3.Model.Order.Level0Data
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Transitivity of the concrete J₃ model

The certified transversal sends zero to every letter: its point map is an
injective self-map of `Fin 6156`, hence is surjective. Every representative is
a word in the original generators, so the concrete model acts transitively.
Source: ATLAS J3G1-p6156B0, retained under `Model/data/`.
-/

namespace Sporadic.Janko3
open OrderCertificate

public theorem exists_model_apply_zero (x : Fin 6156) :
    ∃ g : Model, (g : Equiv.Perm (Fin 6156)) 0 = x := by
  obtain ⟨r, hr⟩ := Finite.surjective_of_injective L0Point_injective x
  have hm : L0Rep r ∈ modelSubgroup := by
    rw [← H0_eq_modelSubgroup]
    exact L0Rep_mem r
  refine ⟨⟨L0Rep r, hm⟩, ?_⟩
  exact (L0Rep_point r).trans hr

public instance model_isPretransitive : MulAction.IsPretransitive Model (Fin 6156) :=
  (MulAction.isPretransitive_iff_base (0 : Fin 6156)).mpr exists_model_apply_zero

end Sporadic.Janko3
