module

public import Theory.Representation.SymplecticConjugatePair.ElementaryGeometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Module

/-!
# The local calculations in H.7

The other parabolic radical attains rank 3n with paired codimension 5n.
The binary Sylow center has rank two and codimension four. More generally,
a member of E.3.8 at k=2n cannot lie in the Sylow center: the rank bound
would force the whole center, while a coordinate root has corank n and a
strictly larger fixed space.

These are the local cases in Aschbacher–Smith, combined manuscript of
1 March 2004, H.7, printed pp.388–389. General elementary-subgroup placement,
the complete family bound, and the involution-type calculation are separate
obligations; no parameter equality for an acting overgroup is asserted here.
-/

public section

namespace CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
open Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair
variable {F : Type*} [Field F] [CharP F 2] [Finite F] [Algebra (ZMod 2) F]

theorem point_radical_witness {n : ℕ} (hF : Nat.card F = 2^n) :
    IsElementaryAbelian 2 (SymplecticConjugatePair.pointRadical (F := F)) ∧
      rank (SymplecticConjugatePair.pointRadical (F := F)) = 3*n ∧
      fixedCodim (graphPair (F := F)) SymplecticConjugatePair.pointRadical = 5*n :=
  ⟨pointRadical_elementary,rank_pointRadical hF,pointRadical_fixedCodim hF⟩

theorem central_binary_witness (hF : Nat.card F = 2) :
    rank (sylowCenter (F := F)) = 2 ∧
      fixedCodim (graphPair (F := F)) sylowCenter = 4 := by
  have h : Nat.card F = 2^1 := by simpa using hF
  exact ⟨rank_sylowCenter h, sylowCenter_fixedCodim h⟩

theorem central_not_mem_fixedSpaceFamily {n : ℕ} (hF : Nat.card F = 2^n)
    (hn : 0 < n) {A : Subgroup (Sp F)} (hAZ : A ≤ sylowCenter) :
    A ∉ ChapterE.fixedSpaceFamily (graphPair (F := F)) (2*n) := by
  intro hA
  have heq := central_eq_of_rank_ge hF hAZ hA.2.1
    (ChapterE.parameter_le_rank_of_mem_fixedSpaceFamily graphPair
      (binaryPair_injective _) hA)
  subst A
  have he := hA.2.2 (RootSubgroup.group 0) root_zero_le_sylowCenter (by
    rw [root_log_relIndex_sylowCenter hF 0 (Or.inl rfl)]
    omega)
  have hc : fixedCodim (graphPair (F := F)) sylowCenter =
      fixedCodim graphPair (RootSubgroup.group 0) := congrArg
    (fun U : Submodule (ZMod 2) (Space F) => Module.finrank (ZMod 2) (Space F ⧸ U)) he
  rw [sylowCenter_fixedCodim hF,root_subgroup_fixedCodim hF 0 _ le_rfl
    (root_group_ne_bot 0)] at hc
  omega
end CFSG.Quasithin.ChapterH.Section05To09.SymplecticPair
