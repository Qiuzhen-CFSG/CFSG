module

public import Theory.SpecificGroups.Triality.EvenInvolutionGeometry.RootElements
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.GroupAction.AutomorphismFixedTransport
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel

/-!
# Components after genuine triality field descent

An actual isomorphism of the fixed subgroup with a smaller binary triality
carrier transports subnormality and the marking of the ordinary component.
Once the smaller carrier is simple, that component fills it. The arm Levi
at exponent one and the cubic short-root subgroup at larger exponents
exclude order 168 without computing the order of the whole triality group.

The smaller carrier's simplicity is explicit: it does not follow merely
from simplicity of the original ambient group. This file supplies the
component calculation after descent, not existence of the descent isomorphism.

Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137, Theorem C and
Remark A.2.4, p.33, and 16.1.4(4), p.1171, `refs/quasithin.pdf`.
-/

public section

open Subgroup Theory.GroupTheory
open Triality.Standard Triality.Standard.Parabolics
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.EvenModels.TrialityCase

/-- The genuine triality carrier never has order 168. The q = 2 case uses
the actual PSL₂(8) arm Levi; larger parameters use the cubic short-root subgroup. -/
theorem card_ne_psl3Two (n : ℕ) (hn : 0 < n) :
    Nat.card (BinaryCarrier n hn) ≠ 168 := by
  intro hc
  by_cases h : n = 1
  · subst n
    let P := binaryParameters 1 hn
    let U := levi P .arms
    have hU : Nat.card U = 504 := by
      rw [Nat.card_congr (leviArmsEquivPSL2 P rfl).toEquiv]
      have he := Atlas.ExceptionalSupport.card_psl_mul (F := ExtensionField P) 2
      have hF : Nat.card (ExtensionField P) = 8 := card_extensionField P
      norm_num [hF, Fin.prod_univ_succ] at he
      omega
    have hd := U.card_subgroup_dvd_card
    change Nat.card U ∣ Nat.card (BinaryCarrier 1 hn) at hd
    norm_num [hU, hc] at hd
  · have hd : 2 ^ (3 * n) ∣ Nat.card (BinaryCarrier n hn) := by
      rw [← EvenInvolutionGeometry.shortRootSubgroup_card n hn]
      exact (EvenInvolutionGeometry.shortRootSubgroup n hn).card_subgroup_dvd_card
    have h64 : 64 ∣ 168 := (pow_dvd_pow 2 (by omega : 6 ≤ 3 * n)).trans (hc ▸ hd)
    norm_num at h64

/-- Given simplicity of this carrier, a nontrivial ordinary component fills
it. The concrete order obstruction then excludes PSL₃(2). -/
theorem not_component_of_simple (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)]
    (C : Subgroup (BinaryCarrier n hn)) (hC : IsComponent (BinaryCarrier n hn) C) :
    ¬ Nonempty (C ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨e⟩
  have he : Nat.card C = 168 := (Nat.card_congr e.toEquiv).trans Matrix.PSL3Two.card_PSL
  rcases hC.1.eq_bot_or_top_of_isSimpleGroup inferInstance with hb | ht
  · norm_num [hb, card_bot] at he
  · exact card_ne_psl3Two n hn (by simpa only [ht, card_top] using he)

/-- Transport the ordinary component through the actual fixed-group
isomorphism. Simplicity of the smaller carrier remains an explicit input. -/
theorem not_fixed_component_of_descent {G : Type*} [Group G]
    (a : MulAut G) (C : Subgroup a.fixedSubgroup) (hC : IsComponent a.fixedSubgroup C)
    (m : ℕ) (hm : 0 < m) [IsSimpleGroup (BinaryCarrier m hm)]
    (e : a.fixedSubgroup ≃* BinaryCarrier m hm) :
    ¬ Nonempty (C ≃* Matrix.PSL3Two.PSL) := by
  rintro ⟨d⟩
  exact not_component_of_simple m hm (C.map e.toMonoidHom) (hC.map_equiv e)
    ⟨(e.subgroupMap C).symm.trans d⟩

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification.EvenModels.TrialityCase
