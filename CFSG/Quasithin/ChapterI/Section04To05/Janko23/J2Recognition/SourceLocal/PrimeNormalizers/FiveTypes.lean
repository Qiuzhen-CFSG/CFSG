module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The five-normalizer interface consumed by the J₂ edge construction

This predicate records just the two normalizer types needed by the edge
centralizer argument. It is an output required from Aschbacher,
*Sporadic Groups* (1994), 47.2(1)–(3), printed p.261. It does not assert
that these alternatives follow from a source seed, distinguish the two
conjugacy classes, or replace the component and Sylow assertions of 47.2.
-/

@[expose] public section

namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers

/-- Every order-five subgroup has one of the two genuine product normalizers. -/
def FiveNormalizerTypes (G : Type*) [Group G] : Prop :=
  ∀ E : Subgroup G, Nat.card E = 5 →
    Nonempty (Subgroup.normalizer (E : Set G) ≃*
      DihedralGroup 5 × alternatingGroup (Fin 5)) ∨
    Nonempty (Subgroup.normalizer (E : Set G) ≃* DihedralGroup 5 × DihedralGroup 5)

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers
