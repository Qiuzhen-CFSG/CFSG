module

public import Theory.SpecificGroups.Janko1.Model.InvolutionCentralizer.Identification
public import Theory.SpecificGroups.Janko1.Model.Certification.InvolutionFusion
public import Theory.GroupAction.InnerInvolutionGeometry
public import Theory.GroupTheory.CComponent.TwoComponent.Involution
public import Theory.GroupTheory.PPrimeCoreReduction

/-!
# Two-components of involution fixed groups in the J₁ matrix model

The checked element fusion and the full C₂ × A₅ centralizer calculation
give trivial odd core for every inner involutory fixed group, provided the
center is trivial. For a simple model the alternative, full center, is solvable
and also satisfies B₂. Full automorphism innerness is an explicit input here;
the known-simple consumer supplies the existing generator-rigidity proof.

Sources: GLS II, Definition 2.4; GLS III, Table 5.3f.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko1

private theorem product_oddCore_eq_bot : pPrimeCore 2 InvolutionCentralizer.ProductModel = ⊥ := by
  apply pPrimeCore_prod_eq_bot
  · have hc := pPrimeCore_coprime_card (p := 2) (G := Multiplicative (ZMod 2))
    have hd := (pPrimeCore 2 (Multiplicative (ZMod 2))).card_subgroup_dvd_card
    have hd' : Nat.card (pPrimeCore 2 (Multiplicative (ZMod 2))) ∣ 2 := by
      simpa using hd
    have hone : Nat.card (pPrimeCore 2 (Multiplicative (ZMod 2))) = 1 :=
      Nat.eq_one_of_dvd_coprimes hc hd' dvd_rfl
    exact Subgroup.card_eq_one.mp hone
  · let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    rcases (inferInstance : (pPrimeCore 2 (alternatingGroup (Fin 5))).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · have hc := pPrimeCore_coprime_card (p := 2) (G := alternatingGroup (Fin 5))
      rw [h, Subgroup.card_top, nat_card_alternatingGroup] at hc
      norm_num [Nat.factorial] at hc

/-- Fusion transports the actual full centralizer, and hence its trivial odd core. -/
theorem inner_involution_fixed_oddCore_eq_bot (hc : center Model = ⊥)
    (r : MulAut Model) (hr : orderOf r = 2) (hi : ∃ g : Model, r = MulAut.conj g) :
    pPrimeCore 2 r.fixedSubgroup = ⊥ := by
  obtain ⟨x, hx, rfl, _⟩ := MulAut.inner_involution_representative hc r hr hi
  obtain ⟨g, hg⟩ := involution_fusion_of_card card_model x hx
  let e := MulAut.fixedSubgroupCongr (MulAut.conj g) (MulAut.conj x)
  have he : MulAut.congr (MulAut.conj g) (MulAut.conj x) = MulAut.conj a := by
    rw [MulAut.congr_conj]
    exact congrArg MulAut.conj hg
  rw [he] at e
  exact pPrimeCore_eq_bot_of_equiv
    (e.trans ((MulEquiv.subgroupCongr (MulAut.fixedSubgroup_conj a)).trans
      InvolutionCentralizer.productEquiv)) product_oddCore_eq_bot

/-- The remaining input is full innerness, discharged by the catalogue consumer. -/
theorem hasInvolutoryB2_of_inner [IsSimpleGroup Model]
    (hi : ∀ r : MulAut Model, ∃ g : Model, r = MulAut.conj g) : HasInvolutoryB2 Model := by
  rcases (inferInstance : (center Model).Normal).eq_bot_or_eq_top with hc | hc
  · exact HasInvolutoryB2.of_fixed_oddCore_eq_bot fun r hr =>
      inner_involution_fixed_oddCore_eq_bot hc r hr (hi r)
  · exact (HasInvolutoryB2.of_solvable (G := center Model)).of_mulEquiv
      (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hc.symm))

end Janko1
