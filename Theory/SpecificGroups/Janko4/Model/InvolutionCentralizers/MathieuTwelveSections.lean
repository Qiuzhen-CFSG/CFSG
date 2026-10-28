module
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Residual
public import Theory.Mathieu.M12.Properties.Simplicity
public import Theory.GroupTheory.SimpleSectionSolvableReduction

/-!
# M₁₂ sections have odd centralizer in J₄

Both actual involution centralizers map to Aut(M₂₂) with solvable kernel.
A simple nonsolvable M₁₂ section would survive that kernel, forcing its
order to divide |Aut(M₂₂)|. The three-parts of the orders exclude this.
Consequently a subgroup surjecting onto M₁₂ has no centralizing involution.

Source application: the small-Mathieu branch of Aschbacher–Smith 4.2.13,
printed pp.611–612, used in 4.4.14, pp.624–625. The native centralizer
constructions and ATLAS attribution are retained through the imports.
-/

public noncomputable section

open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace Janko4.InvolutionCentralizers
attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

private theorem m12_nonsolvable : ¬ Group.IsSolvable M12 := by
  let := m12_isSimpleGroup
  intro hs
  let : CommGroup M12 := { (inferInstance : Group M12) with
    mul_comm := IsSimpleGroup.comm_iff_isSolvable.mpr hs }
  have hp := IsSimpleGroup.prime_card (α := M12)
  rw [m12_order] at hp
  norm_num at hp

private theorem not_m12_dvd_m22Aut : ¬ Nat.card M12 ∣ Nat.card (MulAut M22) := by
  have he : Nat.card (MulAut.innerSubgroup M22) = Nat.card M22 :=
    (Nat.card_congr (MonoidHom.ofInjective
      (MulAut.conj_injective_of_center_eq_bot m22_center_eq_bot)).toEquiv).symm
  have hd : Nat.card (MulAut M22) ∣ Nat.card M22 * 2 := by
    rw [←(MulAut.innerSubgroup M22).card_mul_index,he]
    exact Nat.mul_dvd_mul_left _ M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two
  intro hh
  have h := hh.trans hd
  rw [m12_order,m22_order] at h
  norm_num at h

private theorem no_m12_section_of_mathieuAction {C : Type*} [Group C] [Finite C]
    (a : C →* MulAut M22) [Group.IsSolvable a.ker]
    (B : Subgroup C) (f : B →* M12) (hf : Function.Surjective f) : False := by
  let := m12_isSimpleGroup
  obtain ⟨W,g,hg⟩ := simple_section_quotient_of_solvable_kernel m12_nonsolvable a.ker B f hf
  have hd := (card_dvd_of_surjective g hg).trans W.card_subgroup_dvd_card
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange a).toEquiv] at hd
  exact not_m12_dvd_m22Aut (hd.trans a.range.card_subgroup_dvd_card)

/-- No subgroup of either native involution centralizer has a quotient M12. -/
theorem involution_centralizer_no_m12_section (z : Janko4.Model) (hz : orderOf z = 2)
    (B : Subgroup (centralizer ({z} : Set Janko4.Model)))
    (f : B →* M12) (hf : Function.Surjective f) : False := by
  rcases centralizer_equiv_first_or_second z hz with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · let a := First.QuotientExtension.centralizerMathieuAction
    have ha : Group.IsSolvable a.ker := by
      change Group.IsSolvable First.QuotientExtension.centralizerMathieuAction.ker
      rw [First.QuotientExtension.centralizerMathieuAction_ker]
      let Q := First.QuotientExtension.Q
      let R := First.QuotientExtension.R
      let : Group.IsNilpotent (Q.subgroupOf R) :=
        (pCore_isPGroup.comap_subtype (p := 2) (G := First.centralizer)).isNilpotent
      let : Group.IsSolvable (R ⧸ Q.subgroupOf R) :=
        Group.isSolvable_of_isSolvable_injective
          (f := First.QuotientExtension.RQuotientEquivC3.toMonoidHom)
          First.QuotientExtension.RQuotientEquivC3.injective
      exact (Group.isSolvable_iff_subgroup_quotient (Q.subgroupOf R)).mpr
        ⟨inferInstance,inferInstance⟩
    let := ha
    let d := e.subgroupMap B
    exact no_m12_section_of_mathieuAction a (B.map e.toMonoidHom)
      (f.comp d.symm.toMonoidHom) (hf.comp d.symm.surjective)
  · let a := Second.ambientExtension.rightHom
    let := Second.ambientKernel_elementary
    let : Group.IsNilpotent a.ker :=
      (IsElementaryAbelian.isPGroup 2 Second.ambientKernel).isNilpotent
    let d := e.subgroupMap B
    exact no_m12_section_of_mathieuAction a (B.map e.toMonoidHom)
      (f.comp d.symm.toMonoidHom) (hf.comp d.symm.surjective)

/-- Every actual M12 section in J4 has odd centralizer. -/
theorem m12_section_centralizer_odd (B : Subgroup Janko4.Model)
    (f : B →* M12) (hf : Function.Surjective f) :
    ¬ 2 ∣ Nat.card (centralizer (B : Set Janko4.Model)) := by
  intro heven
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' 2 heven
  have hz' : orderOf (z : Janko4.Model) = 2 := (orderOf_coe z).trans hz
  let C := centralizer ({(z : Janko4.Model)} : Set Janko4.Model)
  have hBC : B ≤ C := fun b hb => mem_centralizer_singleton_iff.mpr
    (z.property b hb)
  let e := subgroupOfEquivOfLe hBC
  exact involution_centralizer_no_m12_section z hz' (B.subgroupOf C)
    (f.comp e.toMonoidHom) (hf.comp e.surjective)
end Janko4.InvolutionCentralizers
