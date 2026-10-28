module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.FiniteModels.Basic
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.DiagonalOuter.FieldExclusion.Components.Identification.Alternating
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.SpecificGroups.LinearCoefficientEquiv
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.FiveSevenGraph
public import Theory.SpecificGroups.BinaryLinear.InnerInvolutionComponents
public import Theory.GroupTheory.AutomorphismTowerSimple
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The binary linear branches of the field-component sieve

Entrywise field transport identifies the arbitrary order-two field witness
with the standard binary model. The actual exceptional PSL₄(2)–A₈ equivalence
then reduces this branch to the proved alternating-group exclusion. In degree
five a graph automorphism fixes no element of order seven, so the specified
involution must be inner. Its full centralizer has self-centralizing two-core
by the displacement-space radical argument, excluding ordinary components.

Source: Aschbacher–Smith, proof of 15.3.38, printed p.1137, using Theorem C(4),
printed p.33. Neither a PSL₃(2) residual quotient nor the printed incorrect
elementary-kernel formula for the degree-five rank-two involution is used.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification

universe u
variable {S : Type u} [Group S] (s : SimpleInput S)
include s

/-- The binary degree-four alternative is impossible, using the actual A₈ model. -/
theorem SimpleInput.not_psl4_two : ¬ ClassicalGroup.IsPSL S 4 2 := by
  rintro ⟨F, hF, hfin, hcard, ⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  exact s.not_alternating (by decide : 8 ≤ 8)
    ⟨e.trans ((Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF).trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)⟩

/-- In the PSL₅(2) branch the specified automorphism must be inner.
Graph automorphisms cannot fix the seven-element in the retained component. -/
theorem SimpleInput.psl5_involution_inner [Finite S]
    (hmodel : ClassicalGroup.IsPSL S 5 2) :
    ∃ g : S, s.involution = MulAut.conj g := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let f := e.trans ((Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := s.involution.fixedSubgroup) 7 s.seven_dvd_fixed_card
  have horder : orderOf (f (x : S)) = 7 :=
    (f.orderOf_eq _).trans ((Subgroup.orderOf_coe x).trans hx)
  have hfix : MulAut.congr f s.involution (f (x : S)) = f (x : S) := by
    change f (s.involution (f.symm (f (x : S)))) = f (x : S)
    rw [f.symm_apply_apply, (MulAut.mem_fixedSubgroup _ _).mp x.property]
  obtain ⟨g, hi | hg⟩ := BinaryLinear.OuterCyclic.inner_graph
    (Or.inr rfl : 5 = 4 ∨ 5 = 5) (MulAut.congr f s.involution)
  · exact (MulAut.congr_inner_iff f s.involution).mp ⟨g, hi⟩
  · have hpow : f (x : S) ^ 7 = 1 := horder ▸ pow_orderOf_eq_one (f (x : S))
    have hone := BinaryLinear.FiveSevenGraph.graph_fixed_seven_eq_one g _ hpow
      (hg ▸ hfix)
    rw [hone, orderOf_one] at horder
    omega

/-- Only the degree-five inner-involution case remains among the two binary
linear alternatives of Theorem C. This is not its centralizer exclusion. -/
theorem SimpleInput.binary_linear_remaining [Finite S] {n : ℕ}
    (hn : n = 4 ∨ n = 5) (hmodel : ClassicalGroup.IsPSL S n 2) :
    n = 5 ∧ ∃ g : S, s.involution = MulAut.conj g := by
  rcases hn with rfl | rfl
  · exact (s.not_psl4_two hmodel).elim
  · exact ⟨rfl, s.psl5_involution_inner hmodel⟩

/-- Degree five is impossible: the automorphism is inner, and its fixed group
has self-centralizing two-core, so cannot have the given ordinary component. -/
theorem SimpleInput.not_psl5_two [Finite S] : ¬ ClassicalGroup.IsPSL S 5 2 := by
  intro hmodel
  obtain ⟨g, hg⟩ := s.psl5_involution_inner hmodel
  let : IsSimpleGroup S := s.simple
  have hZ : Subgroup.center S = ⊥ :=
    (inferInstance : (Subgroup.center S).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => s.nonabelian (Subgroup.center_eq_top_iff.mp h))
  have hgorder : orderOf g = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hZ) g).symm.trans
      (hg ▸ s.involution_order)
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hmodel
  let : Fintype F := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard)
  let f := e.trans ((Matrix.ProjectiveSpecialLinearGroup.ringEquiv eF).trans
    (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide : 0 < 5)))
  have horder : orderOf (f g) = 2 := (f.orderOf_eq g).trans hgorder
  have ha : MulAut.congr f s.involution = MulAut.conj (f g) := by
    rw [hg, MulAut.congr_conj]
  let c : s.involution.fixedSubgroup ≃* (MulAut.conj (f g)).fixedSubgroup :=
    (MulAut.fixedSubgroupCongr f s.involution).trans
      (MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup ha))
  exact BinaryLinear.inner_involution_no_component (f g)
    (by change f g ^ 2 = 1; simpa only [horder] using pow_orderOf_eq_one (f g))
    (by intro h; rw [h, orderOf_one] at horder; omega)
    (s.component.map c.toMonoidHom) (s.isComponent.map_equiv c)

/-- Neither binary linear model in Theorem C has the specified fixed component. -/
theorem SimpleInput.not_binary_linear [Finite S] {n : ℕ} (hn : n = 4 ∨ n = 5) :
    ¬ ClassicalGroup.IsPSL S n 2 := by
  rcases hn with rfl | rfl
  · exact s.not_psl4_two
  · exact s.not_psl5_two

end CFSG.Quasithin.Chapter15.Section03.DiagonalOuter.FieldExclusion.Identification
