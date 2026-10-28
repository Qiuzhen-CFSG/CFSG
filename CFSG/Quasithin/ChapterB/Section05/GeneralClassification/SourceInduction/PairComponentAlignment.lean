module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.BinaryComponentRows
public import Theory.GroupTheory.CComponent.QuasisimpleFactors
/-!
# Aligning the native B.5 factors with an actual component pair

Every component of an internal product lies in a factor. Each native B.5
factor has at most one component: its group is S₃, S₅, or simple and perfect.
For S₅, perfectness puts a component in A₅; for a simple factor subnormality
forces equality. Thus two distinct components occupy opposite actual factors.
The conclusion retains the supplied source factors and their original maps.

Source: Aschbacher–Smith B.5.6(3), printed p.105, applied in 13.6.14,
printed p.929, using ordinary component calculus.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SourceInduction
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}

private theorem component_unique_of_model {E : Type*} [Group E]
    (hm : Nonempty (E ≃* Equiv.Perm (Fin 3)) ∨ Nonempty (E ≃* Equiv.Perm (Fin 5)) ∨
      (IsSimpleGroup E ∧ Group.IsPerfect E))
    {A B : Subgroup E} (hA : IsComponent E A) (hB : IsComponent E B) : A = B := by
  rcases hm with he | he | ⟨hs,hp⟩
  · obtain ⟨e⟩ := he
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
      let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
      apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
      rw [Subgroup.range_subtype, ← alternatingGroup_eq_sign_ker]
    let : Group.IsSolvable E := Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective
    let := hA.2
    let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.isCComponent.ne_bot
    exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
  · obtain ⟨e⟩ := he
    let N := alternatingGroup (Fin 5)
    let : IsSimpleGroup N := alternatingGroup.isSimpleGroup (by simp)
    let : IsQuasisimple N :=
      { toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
        simple := ((QuotientGroup.quotientMulEquivOfEq
          (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup }
    have hN : IsComponent (Equiv.Perm (Fin 5)) N := ⟨(inferInstance : N.Normal).isSubnormal,inferInstance⟩
    have heq {C : Subgroup E} (hC : IsComponent E C) : C.map e.toMonoidHom = N := by
      have hc := hC.map_equiv e
      let := hc.2
      apply hc.eq_of_le hN
      rw [← commutator_eq_self (H := C.map e.toMonoidHom)]
      exact (commutator_mono le_top le_top).trans alternatingGroup.commutator_perm_le
    exact map_injective e.injective ((heq hA).trans (heq hB).symm)
  · let := hs
    let := hp
    have ha := hA.1.eq_bot_or_top_of_isSimpleGroup hs
    have hb := hB.1.eq_bot_or_top_of_isSimpleGroup hs
    exact (ha.resolve_left hA.isCComponent.ne_bot).trans (hb.resolve_left hB.isCComponent.ne_bot).symm

omit [Finite D] in
private theorem component_le_source_factor {A B C : Subgroup D}
    (h : InternalProduct A B) (hC : IsComponent D C) : C ≤ A ∨ C ≤ B := by
  let := h.swap.second_normal
  let := h.second_normal
  rcases hC.normal_dichotomy A with ha | ha
  · exact Or.inl ha
  rcases hC.normal_dichotomy B with hb | hb
  · exact Or.inr hb
  have hc : C ≤ centralizer ((A ⊔ B : Subgroup D) : Set D) := by
    apply le_centralizer_iff.mp
    exact sup_le (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp ha))
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hb))
  rw [h.sup_eq_top] at hc
  have hcc : ⁅C,C⁆ = ⊥ := commutator_eq_bot_iff_le_centralizer.mpr
    (hc.trans (centralizer_le (show (C : Set D) ⊆ (⊤ : Subgroup D) from Set.subset_univ _)))
  let := hC.2
  rw [commutator_eq_self] at hcc
  exact (hC.isCComponent.ne_bot hcc).elim

omit [Finite D] in
/-- The two literal source factors contain the two distinct original
components in one order or the other. -/
theorem SourceTwoFactorCase.component_alignment (d : SourceTwoFactorCase ρ)
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    (A ≤ d.first ∧ B ≤ d.second) ∨ (A ≤ d.second ∧ B ≤ d.first) := by
  have unique {C : Subgroup D} {U : Subrepresentation ρ} (h : SourceFactorCase ρ C U)
      (ha : A ≤ C) (hb : B ≤ C) : False := by
    have he := component_unique_of_model h.group_models (hA.subgroupOf ha) (hB.subgroupOf hb)
    have hh := congrArg (map C.subtype) he
    rw [map_subgroupOf_eq_of_le ha,map_subgroupOf_eq_of_le hb] at hh
    exact hne hh
  rcases component_le_source_factor d.product hA with ha | ha
  · rcases component_le_source_factor d.product hB with hb | hb
    · exact (unique d.firstCase ha hb).elim
    · exact Or.inl ⟨ha,hb⟩
  · rcases component_le_source_factor d.product hB with hb | hb
    · exact Or.inr ⟨ha,hb⟩
    · exact (unique d.secondCase ha hb).elim

end CFSG.Quasithin.ChapterB.SourceInduction
