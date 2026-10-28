module

public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.LinearModels
public import CFSG.Quasithin.MainConverse.AlternatingSections.SymmetricEight.AlternatingOvergroups

/-!
# Structural interfaces for primitive degree eight

These predicates describe actual subgroups, normality in the group under
consideration, and an isomorphism to the matrix PSL₂(7). In particular the
second predicate does not identify a group by its order. Its quotient condition
is solvability of the quotient by that same normal subgroup.

A supplied PSL₂(7) normal layer gives constructed simple quotients by the
normal-image alternative. This is a conditional model lemma for condition K in
Aschbacher–Smith, Theorem 0.1.2(3), printed pp.4 and 482. Existence of this layer
for the remaining primitive groups is a separate assertion still to be proved.
-/

namespace CFSG.Quasithin.MainConverse

open CFSG.KnownSimple

namespace PrimitiveEight

/-- Existence of an actual nontrivial abelian normal subgroup. -/
@[expose] public def HasAbelianNormal (G : Type*) [Group G] : Prop :=
  ∃ N : Subgroup G, N.Normal ∧ IsMulCommutative N ∧ N ≠ ⊥

/-- An actual PSL₂(7) normal subgroup and solvable quotient. -/
@[expose] public def HasPSL2SevenLayer (G : Type*) [Group G] : Prop :=
  ∃ (N : Subgroup G) (hN : N.Normal),
    letI := hN
    Nonempty (N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) ∧
      Group.IsSolvable (G ⧸ N)

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- A supplied PSL₂(7) normal layer controls simple quotients of the whole group. -/
public theorem simple_quotient_constructed_of_psl2Seven_layer {G S : Type*}
    [Group G] [Group S] [IsSimpleGroup S]
    (hG : HasPSL2SevenLayer G) (f : G →* S) (hf : Function.Surjective f) :
    IsConstructedCarrier S := by
  obtain ⟨N, hN, ⟨e⟩, hQ⟩ := hG
  let := hN
  let := hQ
  let : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    Atlas.Comparisons.Exceptional.sl3Two_simple
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    Atlas.Comparisons.Exceptional.psl2SevenEquivSl3Two.isSimpleGroup
  let : IsSimpleGroup N := e.isSimpleGroup
  have hmodel : IsConstructedCarrier N := by
    exact SymmetricEight.constructed_section_of_isKGroup psl2Seven_isKGroup_constructed
      ⊤ (e.symm.toMonoidHom.comp
        (Subgroup.topEquiv (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7))).toMonoidHom)
      (e.symm.surjective.comp Subgroup.topEquiv.surjective)
  exact SymmetricEight.simple_quotient_constructed_of_simple_normal N hmodel f hf

end PrimitiveEight

end CFSG.Quasithin.MainConverse
