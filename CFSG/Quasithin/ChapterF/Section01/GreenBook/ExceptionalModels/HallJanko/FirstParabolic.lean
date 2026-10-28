module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.IntrinsicStructure
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.ExceptionalModels.HallJanko

/-!
# First-local calculations for the fixed Hall--Janko candidates

The actual PSL₂(4)--A₅ equivalence converts the concrete five-point action
into the source matrix-group predicate. An equivalence of the raw radical
with the intrinsic core transports its two commuting factors, their common
order-two intersection, and their generation statement. The literal carrier
inclusion then gives the same description for `Seed.outerL 0`.

The checked radical factors and five-block actions now discharge every input
of the four first-side structural clauses. The orders 1920 and 3840 are also
proved unconditionally in the underlying Theory module.
The concrete permutation extension is not identified here with the full
automorphism group.

Source: Aschbacher--Smith F.1.12(I)(10)--(11), printed p.263 (PDF p.274).
-/

public section
namespace CFSG.Quasithin.ChapterF.GreenBook.HallJanko.FirstParabolic
open Theory.GroupTheory
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

private theorem quaternionDihedral_of_equiv {G H : Type*} [Group G] [Group H]
    {K : Subgroup G} {K' : Subgroup H} (e : K ≃* K')
    (h : IsQuaternionDihedralCore K) : IsQuaternionDihedralCore K' := by
  obtain ⟨B, C, ⟨eB⟩, ⟨eC⟩, hI, hcomm, hgen, hcard⟩ := h
  refine ⟨B.map e.toMonoidHom, C.map e.toMonoidHom,
    ⟨(e.subgroupMap B).symm.trans eB⟩, ⟨(e.subgroupMap C).symm.trans eC⟩,
    ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_inf _ _ e.toMonoidHom e.injective]
    exact (Nat.card_congr (e.subgroupMap (B ⊓ C)).toEquiv).symm.trans hI
  · intro b hb c hc
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hc
    simpa only [map_mul, MulEquiv.coe_toMonoidHom] using congrArg e (hcomm x hx y hy)
  · rw [← Subgroup.map_sup, hgen, Subgroup.map_top_of_surjective _ e.surjective]
  · rw [← Nat.card_congr e.toEquiv, hcard]

/-- The source L₂(4) is the actual projective matrix group over four elements. -/
theorem isPSL_two_four_of_alternating_five {G : Type*} [Group G]
    (h : Nonempty (G ≃* alternatingGroup (Fin 5))) : ClassicalGroup.IsPSL G 2 4 := by
  obtain ⟨e⟩ := h
  have hc : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]
    norm_num
  obtain ⟨f⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hc, ⟨e.trans f.symm⟩⟩

/-- Both numerical inputs for the independent whole-overlap marking calculation. -/
theorem first_local_orders : Nat.card Seed.l₁ = 1920 ∧ Nat.card Seed.l₁s = 3840 :=
  ⟨ExceptionalParabolics.FirstParabolic.card_l₁,
    ExceptionalParabolics.FirstParabolic.card_l₁s⟩

/-- Conditional assembly of precisely the four first-side source clauses.
The unconditional results below use the constructed factors and action maps. -/
theorem first_local_calculations_of_radical_actions
    (hstructure : IsQuaternionDihedralCore ExceptionalParabolics.FirstParabolic.radical)
    (f : Seed.l₁ →* alternatingGroup (Fin 5)) (hf : Function.Surjective f)
    (hk : f.ker = ExceptionalParabolics.FirstParabolic.radical.subgroupOf Seed.l₁)
    (f' : Seed.l₁s →* Equiv.Perm (Fin 5)) (hf' : Function.Surjective f')
    (hk' : f'.ker = ExceptionalParabolics.FirstParabolic.outerRadical.subgroupOf Seed.l₁s) :
    IsQuaternionDihedralCore (pCore 2 Seed.l₁) ∧
      ClassicalGroup.IsPSL (Seed.l₁ ⧸ pCore 2 Seed.l₁) 2 4 ∧
      IsQuaternionDihedralCore (pCore 2 (Seed.outerL 0)) ∧
      Nonempty ((Seed.l₁s ⧸ pCore 2 Seed.l₁s) ≃* Equiv.Perm (Fin 5)) := by
  have hc := hstructure.card
  have hinner := quaternionDihedral_of_equiv
    (ExceptionalParabolics.FirstParabolic.radicalCoreEquiv_of_action hc f hf hk) hstructure
  exact ⟨hinner,
    isPSL_two_four_of_alternating_five
      (ExceptionalParabolics.FirstParabolic.l₁_quotient_of_radical_action hc f hf hk),
    quaternionDihedral_of_equiv ExceptionalParabolics.FirstParabolic.firstCoreEquiv hinner,
    ExceptionalParabolics.FirstParabolic.l₁s_quotient_of_radical_action hc f' hf' hk'⟩

/-- The constructed factors give the source central-product predicate on the radical. -/
theorem radical_isQuaternionDihedralCore :
    IsQuaternionDihedralCore ExceptionalParabolics.FirstParabolic.radical := by
  obtain ⟨hc, B, C, hB, hC, hI, hcomm, hgen⟩ :=
    ExceptionalParabolics.FirstParabolic.radical_structure
  exact ⟨B, C, hB, hC, hI, hcomm, hgen, hc⟩

/-- The first intrinsic core has commuting Q₈ and D₈ factors with common order two. -/
theorem l₁_core_isQuaternionDihedralCore : IsQuaternionDihedralCore (pCore 2 Seed.l₁) :=
  quaternionDihedral_of_equiv ExceptionalParabolics.FirstParabolic.radicalCoreEquiv
    radical_isQuaternionDihedralCore

/-- The literal centralizer quotient is the actual source matrix group PSL₂(4). -/
theorem l₁_quotient_isPSL : ClassicalGroup.IsPSL (Seed.l₁ ⧸ pCore 2 Seed.l₁) 2 4 :=
  isPSL_two_four_of_alternating_five ExceptionalParabolics.FirstParabolic.l₁_quotient

/-- The same core description holds for the first factor included in the extension. -/
theorem outerL₁_core_isQuaternionDihedralCore :
    IsQuaternionDihedralCore (pCore 2 (Seed.outerL 0)) :=
  quaternionDihedral_of_equiv ExceptionalParabolics.FirstParabolic.firstCoreEquiv
    l₁_core_isQuaternionDihedralCore

/-- The source outer quotient uses the full numerator L₁S and its own two-core. -/
theorem l₁s_quotient_equiv :
    Nonempty ((Seed.l₁s ⧸ pCore 2 Seed.l₁s) ≃* Equiv.Perm (Fin 5)) :=
  ExceptionalParabolics.FirstParabolic.l₁s_quotient

/-- All four first-side clauses of F.1.12(I)(10)--(11), with every local input proved. -/
theorem first_local_calculations :
    IsQuaternionDihedralCore (pCore 2 Seed.l₁) ∧
      ClassicalGroup.IsPSL (Seed.l₁ ⧸ pCore 2 Seed.l₁) 2 4 ∧
      IsQuaternionDihedralCore (pCore 2 (Seed.outerL 0)) ∧
      Nonempty ((Seed.l₁s ⧸ pCore 2 Seed.l₁s) ≃* Equiv.Perm (Fin 5)) :=
  ⟨l₁_core_isQuaternionDihedralCore, l₁_quotient_isPSL,
    outerL₁_core_isQuaternionDihedralCore, l₁s_quotient_equiv⟩

end CFSG.Quasithin.ChapterF.GreenBook.HallJanko.FirstParabolic
