module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairFromComponents
/-!
# Identifying the components of a marked binary natural pair

A nontrivial perfect component rules out the two-element field, whose SL₂
is solvable S₃. Over a larger binary field both marked factors are simple
and perfect. Component alignment then identifies the original distinct
components with the two literal factors, proving that they generate the
whole actor and retaining their models over the same chosen field.

Source: Aschbacher–Smith 13.6.14, printed p.929, following B.5.6(3).
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.SourceInduction
open QuasisimpleSource
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) D V}
private theorem symmetric_three_solvable : Group.IsSolvable (Equiv.Perm (Fin 3)) := by
  let : Group.IsSolvable (alternatingGroup (Fin 3)) := Group.isSolvable_of_comm (by decide)
  apply Group.isSolvable_of_ker_le_range (alternatingGroup (Fin 3)).subtype Equiv.Perm.sign
  rw [Subgroup.range_subtype,← alternatingGroup_eq_sign_ker]

theorem SourceTwoFactorCase.MarkedProduct.linear_field_large
    {d : SourceTwoFactorCase ρ} (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    {A : Subgroup D} (hA : IsComponent D A) : 4 ≤ Nat.card F.Carrier := by
  have hd : F.degree ≠ 1 := by
    intro hd
    let e : SL(2,F.Carrier) ≃* Equiv.Perm (Fin 3) :=
      (ExtensionConsequences.degreeOneNaturalEquiv F hd 2).groupEquiv.trans
        ((BinaryLinear.OuterCyclic.slEquivLinear 2).trans BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree)
    let := symmetric_three_solvable
    let : Group.IsSolvable SL(2,F.Carrier) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    let : Group.IsSolvable D := Group.isSolvable_of_isSolvable_injective (f := c.action.groupEquiv.toMonoidHom) c.action.groupEquiv.injective
    let := hA.2
    let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA.isCComponent.ne_bot
    exact Group.IsPerfect.not_isSolvable A inferInstance
  rw [F.card_eq]
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2)
    (show 2 ≤ F.degree by have := F.degree_pos; omega)
  exact hp

theorem SourceTwoFactorCase.MarkedProduct.linear_components
    {d : SourceTwoFactorCase ρ} (F : BinaryField) (c : d.MarkedProduct (linearNatural F 2))
    {A B : Subgroup D} (hA : IsComponent D A) (hB : IsComponent D B) (hne : A ≠ B) :
    A ⊔ B = ⊤ ∧ Nonempty (A ≃* SL(2,F.Carrier)) ∧ Nonempty (B ≃* SL(2,F.Carrier)) := by
  have hF := c.linear_field_large F hA
  let E := SL(2,F.Carrier)
  let : Group.IsPerfect E := GorensteinWalter.sl2_isPerfect_of_card_gt_three F.Carrier (by omega)
  let : IsQuasisimple E :=
    { toIsPerfect := inferInstance
      simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hF }
  let e : D ≃* E × E := c.action.groupEquiv
  let f : E →* D := e.symm.toMonoidHom.comp (MonoidHom.inl E E)
  let g : E →* D := e.symm.toMonoidHom.comp (MonoidHom.inr E E)
  have hf : Function.Injective f := e.symm.injective.comp (fun _ _ h => congrArg Prod.fst h)
  have hg : Function.Injective g := e.symm.injective.comp (fun _ _ h => congrArg Prod.snd h)
  have hr : f.range = d.first := by
    rw [MonoidHom.range_comp]
    have hl : (MonoidHom.inl E E).range = (⊤ : Subgroup E).prod (⊥ : Subgroup E) := by
      ext ⟨x,y⟩
      simp [MonoidHom.mem_range,Subgroup.mem_prod,eq_comm]
    rw [hl]
    exact c.first_eq
  have hs : g.range = d.second := by
    rw [MonoidHom.range_comp]
    have hl : (MonoidHom.inr E E).range = (⊥ : Subgroup E).prod (⊤ : Subgroup E) := by
      ext ⟨x,y⟩
      simp [MonoidHom.mem_range,Subgroup.mem_prod,eq_comm]
    rw [hl]
    exact c.second_eq
  let ef : E ≃* d.first := (MonoidHom.ofInjective hf).trans (MulEquiv.subgroupCongr hr)
  let eg : E ≃* d.second := (MonoidHom.ofInjective hg).trans (MulEquiv.subgroupCongr hs)
  have hfirst : IsComponent D d.first :=
    ⟨d.product.swap.second_normal.isSubnormal,IsQuasisimple.of_mulEquiv ef⟩
  have hsecond : IsComponent D d.second :=
    ⟨d.product.second_normal.isSubnormal,IsQuasisimple.of_mulEquiv eg⟩
  rcases d.component_alignment hA hB hne with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · have hAe := hA.eq_of_le hfirst ha
    have hBe := hB.eq_of_le hsecond hb
    exact ⟨by rw [hAe,hBe]; exact d.product.sup_eq_top,
      ⟨(MulEquiv.subgroupCongr hAe).trans ef.symm⟩,
      ⟨(MulEquiv.subgroupCongr hBe).trans eg.symm⟩⟩
  · have hAe := hA.eq_of_le hsecond ha
    have hBe := hB.eq_of_le hfirst hb
    exact ⟨by rw [hAe,hBe,sup_comm]; exact d.product.sup_eq_top,
      ⟨(MulEquiv.subgroupCongr hAe).trans eg.symm⟩,
      ⟨(MulEquiv.subgroupCongr hBe).trans ef.symm⟩⟩
end CFSG.Quasithin.ChapterB.SourceInduction
