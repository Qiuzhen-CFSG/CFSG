module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.Inputs
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.HigherField.LinearSelection.CyclicOuter
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.SpecificGroups.Triality.OuterOddSubgroups

/-!
# Excluding G₂ and triality from the larger-field Borel branch

The proved inner-field coverage for the actual octonion G₂ model makes
its outer group a quotient of the cyclic field automorphism group. For
the genuine triality carrier, inner-coefficient coverage gives the same
conclusion, retaining the entire cubic coefficient field. Its simplicity
and perfectness premises are inherited from the source component through
the actual model equivalence and L/Z(L) ≃ L⁺.

Transporting these outer groups back to L⁺ discharges the cyclicity premise
of the Borel shadow obstruction. Thus both exceptional alternatives are
excluded using the original I/C_I(L) and O_{2,Φ} quotient. No multiplier,
centerless-cover or later field-degree restriction is needed.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), final proof
of 15.3.35, printed p.1139, with 15.3.33, 15.3.36 and 15.3.41. The model
coverage results use F.1.12 and GLS3 2.5.12, respectively.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection

private theorem outer_isCyclic_of_g2_model {A : Type*} [Group A]
    (n : ℕ) (hn : 1 < n) (hmodel : ClassificationModels.IsG2At A (2 ^ n)) :
    IsCyclic (MulAut.Outer A) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact (show 2 ^ 1 < 2 ^ n from Nat.pow_lt_pow_right (by decide) hn)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (Atlas.G2.Model F))
  let f := q.comp (Atlas.G2.LieAutomorphismExtensions.fieldAction (F := F))
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective _ x
    obtain ⟨g, σ, rfl⟩ := Atlas.G2.LieAutomorphismExtensions.exists_inner_field hq a
    refine ⟨σ, ?_⟩
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    change q (Atlas.G2.LieAutomorphismExtensions.fieldAction σ) =
      q (MulAut.conj g * Atlas.G2.LieAutomorphismExtensions.fieldAction σ)
    rw [map_mul, hg, one_mul]
  let : IsCyclic (F ≃+* F) := Theory.PSL2.OuterSolvable.finiteFieldAut_isCyclic
  have hc : IsCyclic (MulAut.Outer (Atlas.G2.Model F)) := isCyclic_of_surjective f hf
  exact (MulAut.outerCongr e).isCyclic.mpr hc

variable {G : Type*} [Group G] [Finite G]

/-- The actual larger-field G₂ model cannot have the source Borel shadow. -/
theorem false_of_g2
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (n : ℕ) (hn : 1 < n)
    (hmodel : ClassificationModels.IsG2At (componentImage I L L) (2 ^ n)) : False :=
  CyclicOuter.false_of_cyclic_outer I L M Yplus S B c hB hYB
    (outer_isCyclic_of_g2_model n hn hmodel)

/-- The genuine triality alternative is excluded using inherited component
simplicity and perfectness, with no further model-certification premise. -/
theorem false_of_triality
    (I L M Yplus S B : Subgroup G) [(L.subgroupOf I).Normal]
    (c : NonCharacteristicTwo.ComponentSetup I L M Yplus S)
    (hB : BorelOverSylow L S B) (hYB : Yplus ≤ B)
    (n : ℕ) (hn : 1 < n)
    (hmodel : Triality.Standard.IsTrialityGroupAt (2 ^ n) (componentImage I L L)) : False := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hmodel
  let : IsQuasisimple L := c.component_quasisimple
  let eL := componentImageCenterEquiv I L c.component_le
  let : Group.IsPerfect (componentImage I L L) :=
    Group.IsPerfect.ofSurjective (f := eL.toMonoidHom) eL.surjective
  let : Group.IsPerfect (Triality.Standard.Carrier P) :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : IsSimpleGroup (Triality.Standard.Carrier P) := e.isSimpleGroup_congr.mp c.simple_image
  have hc := Triality.Standard.OuterOdd.outer_isCyclic P n (by omega) hP
  exact CyclicOuter.false_of_cyclic_outer I L M Yplus S B c hB hYB
    ((MulAut.outerCongr e).isCyclic.mpr hc)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.Parabolics.HigherField.LinearSelection
