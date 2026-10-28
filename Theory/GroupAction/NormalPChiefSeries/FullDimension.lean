module
public import Theory.GroupAction.NormalPChiefSeries.Linear
public import Theory.Representation.RepEquiv

/-!
# A full-dimensional chief factor is the original representation

A chief factor has dimension at most its upper term, which has dimension
at most the original elementary normal subgroup. Equality forces the
upper term to be all of the original module and the factor projection
to be a linear isomorphism. Its literal conjugation equivariance then
transfers irreducibility. This is the equality step in the minimum-degree
argument used by Aschbacher–Smith E.2.15, printed p.228.
-/

public section
open Representation Subgroup
open scoped IsMulCommutative
namespace NoncentralChiefRefinement.SeriesOn
variable {H : Type*} [Group H] [Finite H]
  {U : Subgroup H} [U.Normal] [IsElementaryAbelian 2 U]

theorem normalRepresentation_irreducible_of_factor_full_dimension
    (s : SeriesOn U) (i : Fin s.series.length)
    (hd : Module.finrank (ZMod 2) (Additive (s.Factor i)) =
      Module.finrank (ZMod 2) (Additive U)) :
    (normalRepresentation U).IsIrreducible := by
  have hp := LinearMap.finrank_le_finrank_of_surjective (s.factorProjection_surjective i)
  have ht : Module.finrank (ZMod 2) (s.linearTerm i.succ).toSubmodule =
      Module.finrank (ZMod 2) (Additive U) :=
    le_antisymm (Submodule.finrank_le _) (hd ▸ hp)
  have htop := Submodule.eq_top_of_finrank_eq ht
  let a := LinearEquiv.ofTop (s.linearTerm i.succ).toSubmodule htop
  let b := LinearEquiv.ofBijective (s.factorProjection i)
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (ht.trans hd.symm)).mpr
      (s.factorProjection_surjective i),s.factorProjection_surjective i⟩
  let c := a.symm.trans b
  let e : (normalRepresentation U).Equiv (s.factorRepresentation i) :=
    Representation.Equiv.mk c (by
      intro h
      apply LinearMap.ext
      intro x
      change s.factorProjection i
          ⟨normalRepresentation U h x, _⟩ =
        s.factorRepresentation i h (s.factorProjection i ⟨x, _⟩)
      have hx : (x.toMul : H) ∈ (s.upper i).val := by
        change x ∈ (s.linearTerm i.succ).toSubmodule
        rw [htop]
        trivial
      change Additive.ofMul (QuotientGroup.mk' ((s.lower i).val.subgroupOf (s.upper i).val)
        (MulAut.conjNormal h ⟨x.toMul,hx⟩)) =
          Additive.ofMul (s.action i h (QuotientGroup.mk'
            ((s.lower i).val.subgroupOf (s.upper i).val) ⟨x.toMul,hx⟩))
      rw [s.action_mk])
  exact (RepEquiv.ofRepresentationEquiv e).irreducible_of_euqiv
    (s.factorRepresentation_irreducible i)
end NoncentralChiefRefinement.SeriesOn
