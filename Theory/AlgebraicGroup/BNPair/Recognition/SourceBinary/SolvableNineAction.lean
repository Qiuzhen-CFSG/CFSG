module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitarySource.ActorPanels
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.LinearPanelRegularity
public import Theory.GroupTheory.SolvableNormalAbelian
public import Theory.GroupAction.RegularNormal
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
/-!
# The solvable degree-nine local action

A nontrivial abelian normal subgroup of a faithful primitive solvable group
is regular. Double transitivity makes it elementary abelian; at degree nine
it is an elementary three-group of order nine. The point stabilizer acts
faithfully by conjugation on this group, so its order divides |GL₂(3)| = 48.
The whole permutation group therefore has order dividing 432.

The final two theorems apply this calculation to the SAME marked panel:
the root actor is doubly transitive, and its image lies in the whole local
action without (2B). No model identification or exclusion of the exceptional
local action is assumed. BinaryUnitaryOvergroup uses this bound together
with the normal original factor and its two-power index.
Source: the solvable primitive-group argument in Fong--Seitz I (2A)--(2B),
pp.7--9; the actual panel chart is proved in UnitarySource.ActorPanels.
-/

public noncomputable section
open Subgroup MulAction
open scoped IsMulCommutative
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

variable {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω]
  [FaithfulSMul G Ω] [Finite Ω]

/-- A solvable faithful doubly transitive action of degree nine has a regular elementary nine. -/
theorem regular_nine_of_solvable (ht : IsMultiplyPretransitive G Ω 2)
    [Group.IsSolvable G] (hc : Nat.card Ω = 9) (o : Ω) :
    ∃ A : Subgroup G, A.Normal ∧ IsElementaryAbelian 3 A ∧ Nat.card A = 9 ∧
      (∀ x y : Ω, ∃! a : A, (a : G) • x = y) := by
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  let : IsPretransitive G Ω := inferInstance
  let : Nontrivial Ω := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : Nontrivial G := by
    obtain ⟨x,hx⟩ := exists_ne o
    obtain ⟨g,hg⟩ := exists_smul_eq G o x
    exact ⟨⟨g,1,fun he => hx (by simpa only [he,one_smul] using hg.symm)⟩⟩
  obtain ⟨A,hAn,hAc,hA⟩ := Group.exists_nontrivial_abelian_normal G
  let := hAn
  let := hAc
  let : IsPretransitive A Ω := Atlas.GroupTheory.normal_pretransitive A hA
  have hfree (a : A) (x : Ω) (hax : (a : G) • x = x) : a = 1 := by
    apply Subtype.ext
    apply eq_of_smul_eq_smul (α := Ω)
    intro y
    obtain ⟨b,hb⟩ := exists_smul_eq A x y
    rw [← hb]
    change (a : G) • ((b : G) • x) = (1 : G) • ((b : G) • x)
    have hcomm : (a : G)*(b : G) = (b : G)*(a : G) := congrArg Subtype.val (mul_comm a b)
    rw [← mul_smul,hcomm,mul_smul,hax,one_smul]
  have hreg (x y : Ω) : ∃! a : A, (a : G) • x = y := by
    obtain ⟨a,ha⟩ := exists_smul_eq A x y
    refine ⟨a,ha,?_⟩
    intro b hb
    apply inv_mul_eq_one.mp
    apply hfree _ x
    change ((b : G)⁻¹ * (a : G)) • x = x
    rw [mul_smul]
    change (a : G) • x = y at ha
    rw [ha,← hb,inv_smul_smul]
  have hbij : Function.Bijective (fun a : A => (a : G) • o) := by
    refine ⟨?_,fun x => exists_smul_eq A o x⟩
    intro a b he
    obtain ⟨c,hc,hu⟩ := hreg o ((a : G) • o)
    exact (hu a rfl).trans (hu b he.symm).symm
  have hcard : Nat.card A = 9 := (Nat.card_congr (Equiv.ofBijective _ hbij)).trans hc
  obtain ⟨p,hp,he⟩ := regular_normal_elementaryAbelian ht o A hAn hA hreg
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := he
  have hp3 : p = 3 := by
    have hd : p ∣ Nat.card A := (IsElementaryAbelian.isPGroup p A).card_eq_or_dvd.resolve_left (by omega)
    rw [hcard,show 9 = 3^2 by decide] at hd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)
  exact ⟨A,hAn,hp3 ▸ he,hcard,hreg⟩

omit [Finite G] [Finite Ω] in
/-- The point stabilizer acts faithfully on the regular normal nine-group. -/
theorem stabilizer_action_injective (A : Subgroup G) [A.Normal] (o : Ω)
    (hreg : ∀ x y : Ω, ∃! a : A, (a : G) • x = y) :
    Function.Injective ((MulAut.conjNormal : G →* MulAut A).comp (stabilizer G o).subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro g hg
  apply Subtype.ext
  apply eq_of_smul_eq_smul (α := Ω)
  intro y
  obtain ⟨a,ha,_⟩ := hreg o y
  have hcomm : (g : G) * (a : G) = (a : G) * (g : G) := by
    have he := congrArg (fun f : MulAut A => (f a : G)) hg
    change (g : G) * (a : G) * (g : G)⁻¹ = (a : G) at he
    exact (mul_inv_eq_iff_eq_mul).mp he
  change (g : G) • y = (1 : G) • y
  rw [← ha, ← mul_smul, hcomm, mul_smul, g.property, one_smul]

/-- The actual solvable degree-nine action has order dividing 9 |GL₂(3)| = 432. -/
theorem card_dvd_432 (ht : IsMultiplyPretransitive G Ω 2)
    [Group.IsSolvable G] (hc : Nat.card Ω = 9) (o : Ω) : Nat.card G ∣ 432 := by
  obtain ⟨A,hAn,hAe,hAcard,hreg⟩ := regular_nine_of_solvable ht hc o
  let := hAn
  let := hAe
  obtain ⟨c,e,he⟩ := Matrix.GeneralLinearGroup.PrimeThreeFiveResidual.exists_plane_coordinates
    (show Nat.card A = 3^2 by simpa using hAcard)
  have hAut : Nat.card (MulAut A) = 48 := by
    rw [Nat.card_congr e.toEquiv,Matrix.card_GL_field]
    decide
  let f := (MulAut.conjNormal : G →* MulAut A).comp (stabilizer G o).subtype
  have hdiv : Nat.card (stabilizer G o) ∣ 48 := by
    rw [← hAut, Nat.card_congr (MonoidHom.ofInjective (stabilizer_action_injective A o hreg)).toEquiv]
    exact f.range.card_subgroup_dvd_card
  let : IsPreprimitive G Ω := isPreprimitive_of_is_two_pretransitive ht
  have hcard := (stabilizer G o).index_mul_card
  rw [index_stabilizer_of_transitive,hc] at hcard
  rw [← hcard]
  exact Nat.mul_dvd_mul_left 9 hdiv
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.BinaryPanel

namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open RootCoordinates UnitarySource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits) (i : Fin 2)

/-- The same faithful local image is doubly transitive, without (2B). -/
theorem localGroup_two_pretransitive :
    IsMultiplyPretransitive (localGroup Q split i) (Panel Q i) 2 := by
  apply is_two_pretransitive_iff.mpr
  intro a b c d hab hcd
  obtain ⟨r,hr,hr'⟩ := is_two_pretransitive_iff.mp (panelActor_two_pretransitive Q split i) hab hcd
  let x : localClosure Q split i := ⟨r.val.val,rankOne_le_localClosure Q split i r.property⟩
  refine ⟨(localAction Q split i).rangeRestrict x,?_,?_⟩
  · change localAction Q split i x a = c
    rw [localAction_eq_panelAction]
    exact hr
  · change localAction Q split i x b = d
    rw [localAction_eq_panelAction]
    exact hr'

/-- A solvable local group on the degree-nine marked panel has order dividing 432. -/
theorem localGroup_card_dvd_432 (hs : Group.IsSolvable (localGroup Q split i))
    (hc : Nat.card (Panel Q i) = 9) : Nat.card (localGroup Q split i) ∣ 432 := by
  let := hs
  exact BinaryPanel.card_dvd_432 (localGroup_two_pretransitive Q split i) hc (panelBase Q i)
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
