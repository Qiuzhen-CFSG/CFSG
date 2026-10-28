module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.SylowCore
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex

/-!
# Normal elementary bounds in a full J₄ Sylow subgroup

An elementary subgroup normalized by a full Sylow two-subgroup lies in it.
Conjugate that Sylow into the literal max1 subgroup, whose index is odd.
The checked quotient-action bound makes its normal elementary kernel of
order 2048 the unique normal elementary subgroup of at least that order.
Transport back gives the same bound in the actual J₄ carrier.

This uses only the normal-elementary calculation, rather than the general
two-rank theorem. The application in Aschbacher--Smith 10.2.9, printed p.750,
excludes a moved image with four natural binary-three constituents.
Model sources: Kleidman--Wilson, *The maximal subgroups of J₄* (1988),
pp.484--510; GLS3 Table 5.3i and the imported ATLAS word certificates.
-/

public section

open Subgroup
namespace Janko4.LocalStructure
open Cardinality SylowCore
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup

/-- A full Sylow normalizer forces an elementary subgroup to have order at most 2048. -/
theorem normal_elementary_card_le_2048 (S : Sylow 2 Model) (A : Subgroup Model)
    [IsElementaryAbelian 2 A] (hn : (S : Subgroup Model) ≤ normalizer (A : Set Model)) :
    Nat.card A ≤ 2048 := by
  let P : Sylow 2 Local := default
  let Q : Sylow 2 Model := (P.isPGroup'.map Local.subtype).toSylow (by
    rw [index_map_subtype]
    exact Nat.prime_two.not_dvd_mul P.not_dvd_index
      OuterReduction.max1_odd_index_unconditional)
  have hAS : A ≤ (S : Subgroup Model) := sup_eq_left.mp (S.is_maximal'
    (S.isPGroup'.to_sup_of_normal_right' (IsElementaryAbelian.isPGroup 2 A) hn)
    le_sup_left)
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq Model S Q
  let f := MulAut.conj g
  have hS : (S : Subgroup Model).map f.toMonoidHom = (Q : Subgroup Model) :=
    congrArg Sylow.toSubgroup hg
  let B := A.map f.toMonoidHom
  have hBQ : B ≤ (Q : Subgroup Model) := by
    simpa only [hS] using map_mono (f := f.toMonoidHom) hAS
  have hQN : (Q : Subgroup Model) ≤ normalizer (B : Set Model) := by
    rw [← hS]
    exact (map_mono hn).trans (le_normalizer_map f.toMonoidHom)
  let C := B.subgroupOf (Q : Subgroup Model)
  let : C.Normal := normal_subgroupOf_of_le_normalizer hQN
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map f.toMonoidHom
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.subgroupOf hBQ
  let e : Q ≃* P :=
    (P.toSubgroup.equivMapOfInjective Local.subtype Subtype.val_injective).symm
  let U := C.map e.toMonoidHom
  let : U.Normal := (inferInstance : C.Normal).map e.toMonoidHom e.surjective
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map e.toMonoidHom
  have hU : Nat.card U ≤ 2048 := by
    by_cases hc : 2048 ≤ Nat.card U
    · have he := localKernel_sylow_unique_of_quotientCentralizerBound
        (quotientCentralizerBound_of_fixedBound normalElementaryFixedBound) P U hc
      rw [he,localKernel_sylow_card]
    · omega
  have hc : Nat.card U = Nat.card A := by
    rw [card_map_of_injective e.injective]
    rw [Nat.card_congr (subgroupOfEquivOfLe hBQ).toEquiv]
    exact card_map_of_injective f.injective
  rwa [hc] at hU
end Janko4.LocalStructure
