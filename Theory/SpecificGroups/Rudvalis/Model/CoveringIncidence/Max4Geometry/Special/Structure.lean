module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Basic
public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Special.Relations
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.CommutatorPreimageFrattini

/-!
# Derived and Frattini structure from the fixed max4 words

The checked generators centralize the marked basis and therefore lie in
C_max4(E_8)=O_2(max4), using the literal ambient embedding. Three of their
commutators span the marked eight-group. If the eleven words generate the
core, their square and commutator relations make the quotient by that
marked subgroup elementary; the finite two-group Frattini criterion then
identifies both the derived and Frattini subgroups with the marked subgroup.

Generation remains an explicit independent premise. Equality of the core
center with the marked eight-group is not used or asserted in this module.
Source: GLS3 Table 5.3r, pp.291--292; Aschbacher--Smith I.2.2(7), pp.412--413.
-/

namespace Rudvalis.CoveringIncidence.Max4Special
open Subgroup SylowOvergroups.RadicalCoverage.LocalCover
open Collection
open scoped commutatorElement

@[expose] public def centerIndex : Fin 3 → Fin 11 := ![10, 9, 8]

public theorem basis_eq_generator (i : Fin 3) :
    RankOneEightCharacteristic.basis i = Max4Words.generator (centerIndex i) := by
  fin_cases i
  · exact (center_word_eq_basis 0).symm.trans (generator_eq 10).symm
  · exact (center_word_eq_basis 1).symm.trans (generator_eq 9).symm
  · exact (center_word_eq_basis 2).symm.trans (generator_eq 8).symm

public theorem generator_commute_basis (i : Fin 11) (j : Fin 3) :
    Commute (Max4Words.generator i) (RankOneEightCharacteristic.basis j) := by
  rw [basis_eq_generator]
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [generator_commutator]
  have ht : ∀ i : Fin 11, ∀ j : Fin 3, commutatorCode i (centerIndex j) = 0 := by decide +kernel
  rw [ht, centralValue_zero]

public theorem generator_mem_core (i : Fin 11) : Max4Words.generator i ∈ max4Core := by
  rw [max4Core_eq_centralizer]
  refine ⟨Max4Words.generator_mem_max4 i, ?_⟩
  rw [← RankOneEightCharacteristic.closure_basis, centralizer_closure]
  rintro _ ⟨j, rfl⟩
  exact (generator_commute_basis i j).eq.symm

public theorem closure_generators_le_core : closure (Set.range Max4Words.generator) ≤ max4Core := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  exact generator_mem_core i

/-- The 2048 proposed binary products, with the first word on the left. -/
@[expose] public def binaryProduct (n : Fin 2048) : Model :=
  (List.ofFn (fun i : Fin 11 => Max4Words.generator i ^ (n.val / 2 ^ i.val % 2))).prod

public theorem binaryProduct_mem_generated (n : Fin 2048) :
    binaryProduct n ∈ closure (Set.range Max4Words.generator) := by
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  apply Subgroup.pow_mem
  exact subset_closure ⟨i, rfl⟩

@[expose] public def intrinsicGenerator (i : Fin 11) : max4Core :=
  ⟨Max4Words.generator i, generator_mem_core i⟩

@[expose] public def markedCore : Subgroup max4Core := (elementary 2).subgroupOf max4Core

public instance markedCore_normal : markedCore.Normal :=
  (normal_subgroupOf_iff_le_normalizer marked_eight_le_core).mpr
    (max4Core_le_max4.trans RankOneEightAction.max4_le_normalizer_eight)

public theorem markedCore_map : markedCore.map max4Core.subtype = elementary 2 :=
  map_subgroupOf_eq_of_le marked_eight_le_core

public theorem markedCore_le_center : markedCore ≤ center max4Core := by
  intro x hx
  obtain ⟨y, hy, he⟩ := marked_eight_le_core_center hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

public theorem centralValue_mem_mapped_derived (i j : Fin 11) :
    centralValue (commutatorCode i j) ∈ (_root_.commutator max4Core).map max4Core.subtype := by
  have h := mem_map_of_mem max4Core.subtype
    (commutator_mem_commutator (mem_top (intrinsicGenerator i)) (mem_top (intrinsicGenerator j)))
  change ⁅Max4Words.generator i, Max4Words.generator j⁆ ∈
    (_root_.commutator max4Core).map max4Core.subtype at h
  rwa [generator_commutator] at h

public theorem marked_eight_le_mapped_derived :
    elementary 2 ≤ (_root_.commutator max4Core).map max4Core.subtype := by
  rw [← RankOneEightCharacteristic.closure_basis]
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · simpa [commutatorCode, centralValue_eq] using centralValue_mem_mapped_derived 1 5
  · simpa [commutatorCode, centralValue_eq] using centralValue_mem_mapped_derived 0 4
  · simpa [commutatorCode, centralValue_eq] using centralValue_mem_mapped_derived 0 2

public theorem markedCore_le_derived : markedCore ≤ _root_.commutator max4Core := by
  intro x hx
  obtain ⟨y, hy, he⟩ := marked_eight_le_mapped_derived hx
  have hyx : y = x := Subtype.ext he
  exact hyx ▸ hy

public theorem intrinsic_generation_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    closure (Set.range intrinsicGenerator) = ⊤ := by
  apply map_injective max4Core.subtype_injective
  rw [MonoidHom.map_closure, ← Set.range_comp]
  rw [← MonoidHom.range_eq_map, range_subtype]
  exact hgen

/-- Generation is the only outstanding premise for this elementary quotient. -/
public theorem markedQuotient_elementary_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    IsElementaryAbelian 2 (max4Core ⧸ markedCore) := by
  let q := QuotientGroup.mk' markedCore
  let u : Fin 11 → max4Core ⧸ markedCore := fun i => q (intrinsicGenerator i)
  have htop : closure (Set.range u) = ⊤ := by
    have hm := congrArg (Subgroup.map q) (intrinsic_generation_of_generation hgen)
    rw [MonoidHom.map_closure, ← Set.range_comp, ← MonoidHom.range_eq_map,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective markedCore)] at hm
    exact hm
  let : IsMulCommutative (closure (Set.range u)) := isMulCommutative_closure (by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    apply commutatorElement_eq_one_iff_mul_comm.mp
    change ⁅q (intrinsicGenerator i), q (intrinsicGenerator j)⁆ = 1
    rw [← map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    change ⁅Max4Words.generator i, Max4Words.generator j⁆ ∈ elementary 2
    rw [generator_commutator]
    exact centralValue_mem _)
  let : IsElementaryAbelian 2 (closure (Set.range u)) :=
    IsElementaryAbelian.closure_of_isMulCommutative _ (by
      rintro _ ⟨i, rfl⟩
      change q (intrinsicGenerator i) ^ 2 = 1
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      change Max4Words.generator i ^ 2 ∈ elementary 2
      rw [pow_two, generator_square]
      exact centralValue_mem _)
  apply IsElementaryAbelian.of_surjective (closure (Set.range u)).subtype
  intro x
  exact ⟨⟨x, htop.symm ▸ mem_top x⟩, rfl⟩

public theorem derived_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    _root_.commutator max4Core = markedCore := by
  have he := markedQuotient_elementary_of_generation hgen
  exact le_antisymm
    (Normal.quotient_commutative_iff_commutator_le.mp he.toIsMulCommutative)
    markedCore_le_derived

public theorem frattini_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    frattini max4Core = markedCore := by
  let : Fact (IsPGroup 2 max4Core) := ⟨max4Core_isPGroup⟩
  apply le_antisymm
  · exact frattini_le_of_elementary_quotient max4Core_isPGroup markedCore
      (markedQuotient_elementary_of_generation hgen)
  · rw [← derived_eq_marked_of_generation hgen]
    exact commutator_le_frattini_of_isPGroup (p := 2)

public theorem mapped_derived_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    (_root_.commutator max4Core).map max4Core.subtype = elementary 2 := by
  rw [derived_eq_marked_of_generation hgen, markedCore_map]

public theorem mapped_frattini_eq_marked_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    (frattini max4Core).map max4Core.subtype = elementary 2 := by
  rw [frattini_eq_marked_of_generation hgen, markedCore_map]

public theorem centralQuotient_elementary_of_generation
    (hgen : closure (Set.range Max4Words.generator) = max4Core) :
    IsElementaryAbelian 2 Max4CentralQuotient := by
  apply elementary_quotient_of_frattini_le max4Core_isPGroup
  rw [frattini_eq_marked_of_generation hgen]
  exact markedCore_le_center

end Rudvalis.CoveringIncidence.Max4Special
