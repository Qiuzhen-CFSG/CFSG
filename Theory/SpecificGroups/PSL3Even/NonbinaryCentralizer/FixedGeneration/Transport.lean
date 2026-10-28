module

public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.StandardGeneration

/-!
# Generation under conjugacy preserving the marked unipotent subgroup

An automorphism conjugator carries the actual fixed subgroup to the fixed
subgroup of the transported actor. If it also preserves the specified upper
unipotent subgroup, the standard generation theorem pulls back with exactly
that marking. The graph representative used here is `oppositionGraph`, which
preserves the upper Borel; inverse transpose itself exchanges the Borels.

Constructing such a compatible conjugator is a separate mathematical
obligation. These lemmas provide its literal generation application and
make no claim that arbitrary conjugacy preserves the marking.

Sources: the matrix generation step for Aschbacher–Smith E.1.14(1),
printed p.214, and the matrix actions in GLS3, §2.7.
-/

public section
open Subgroup Matrix.PSL3.LinearThree Matrix.PSL3.OuterSolvable
open Matrix.PSL3.OuterSolvable.OddPrimeCoverage
open scoped MatrixGroups
namespace Matrix.PSL3Even.NonbinaryCentralizer

private theorem fixed_map_congr {G : Type*} [Group G] (a c : MulAut G) :
    a.fixedSubgroup.map c.toMonoidHom = (MulAut.congr c a).fixedSubgroup := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' := (MulAut.mem_fixedSubgroup a y).mp hy
    apply (MulAut.mem_fixedSubgroup _ _).mpr
    change c (a (c.symm (c y))) = c y
    rw [c.symm_apply_apply, hy']
  · intro hx
    refine ⟨c.symm x, ?_, c.apply_symm_apply x⟩
    rw [MulAut.mem_fixedSubgroup] at hx
    apply (MulAut.mem_fixedSubgroup a _).mpr
    apply c.injective
    change c (a (c.symm x)) = x at hx
    simpa only [c.apply_symm_apply] using hx

private theorem fixed_sup_eq_top_of_congr {G : Type*} [Group G]
    (U : Subgroup G) (a b c : MulAut G)
    (hc : MulAut.congr c a = b) (hU : U.map c.toMonoidHom = U)
    (hgen : b.fixedSubgroup ⊔ U = ⊤) : a.fixedSubgroup ⊔ U = ⊤ := by
  have hm : (a.fixedSubgroup ⊔ U).map c.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, fixed_map_congr, hc, hU, hgen]
  apply top_unique
  intro x _
  obtain ⟨y, hy, hxy⟩ := hm.symm ▸ (mem_top (c x))
  exact c.injective hxy ▸ hy

variable {F : Type*} [Field F] [CharP F 2]

/-- A compatible graph conjugator transfers generation while retaining the
original upper-unipotent subgroup. -/
theorem graph_fixed_sup_unipotent_of_marked_congr (a c : MulAut PSL(3,F))
    (hc : MulAut.congr c a = oppositionGraph F)
    (hU : (unipotent F).map c.toMonoidHom = unipotent F) :
    a.fixedSubgroup ⊔ unipotent F = ⊤ :=
  fixed_sup_eq_top_of_congr (unipotent F) a (oppositionGraph F) c hc hU
    oppositionGraph_fixed_sup_unipotent

/-- A compatible field conjugator transfers generation with the same marked
upper-unipotent subgroup. -/
theorem field_fixed_sup_unipotent_of_marked_congr
    (a c : MulAut PSL(3,F)) (σ : F ≃+* F)
    (hc : MulAut.congr c a = fieldAction F σ)
    (hU : (unipotent F).map c.toMonoidHom = unipotent F) :
    a.fixedSubgroup ⊔ unipotent F = ⊤ :=
  fixed_sup_eq_top_of_congr (unipotent F) a (fieldAction F σ) c hc hU
    (field_fixed_sup_unipotent σ)

end Matrix.PSL3Even.NonbinaryCentralizer
