module

public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.Transport
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Actions
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Symplectic.Rows
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Symplectic.NormalComparison
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.LieFamilies.Symplectic.ModelOrders
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.OtherFamilies.Divisibility
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.ReverseDelta.Comparison.InnerOnly
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Plane

/-!
# Excluding symplectic residual pairs

For a root inner action, the earlier table identifies the residual with an
actual point or plane local group. Its matrix projection has a two-group
kernel and simple quotient SL₂(q). Relative normality of the outer residual
then forces its nonsolvable simple model to have the same order as SL₂(q).
The derived half-field group and the odd-degree Suzuki group are both larger.
The c₂ case has a solvable inner fixer and a nonsolvable outer residual.

At the binary endpoint the carrier is Sp₄(2)′, not Sp₄(2). Inner fixers are
two-groups; full-group root actors have residual A₄ and graph actors have
residual Sz(2)′ of order five. Their odd divisors cannot pass into the inner
fixer, even through the two distinct central covering kernels.

The exclusions are conditional only on `SymplecticInvolutionTable` and
`BinarySymplecticInvolutionRows`, whose exact earlier-table obligations are
listed in `Symplectic.Rows`. These include root residual equivalences, the
c₂ fixer calculation, field and graph-field conjugators, the Suzuki fixed
group equivalence, and the binary derived-action rows. No normal-subgroup
comparison or exclusion is assumed. The source assembly must discharge
these earlier-table inputs; this module does not assert source 16.1.4.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 16.1.2–4,
printed pp.1170–1171, and the comparison in 16.4.11(2), printed p.1193.
The root-local matrix projections come from the F.1.12(I)(2) development,
printed pp.262–264.
-/

public section
namespace CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
open Subgroup Theory.GroupTheory LiePreliminaries
open Theory.SpecificGroups.SymplecticFour
open DiagramAutomorphisms DiagramAutomorphisms.GraphFieldFixedResidual
open BenderSuzuki.MatrixGroups
private theorem two_kernel_comp_equiv {X Y A : Type*} [Group X] [Group Y] [Group A]
    (f : X →* A) (e : Y ≃* X) (hp : IsPGroup 2 f.ker) :
    IsPGroup 2 (f.comp e.toMonoidHom).ker := by
  let k : (f.comp e.toMonoidHom).ker →* f.ker :=
    (e.toMonoidHom.comp (f.comp e.toMonoidHom).ker.subtype).codRestrict f.ker
      (fun x => x.property)
  apply hp.of_injective k
  intro x y he
  apply Subtype.ext
  apply e.injective
  exact congrArg (fun z : f.ker => (z : X)) he

private theorem root_levi {F X : Type*} [Field F] [CharP F 2] [Group X]
    (h : Nonempty (X ≃* pointLocal (F := F)) ∨ Nonempty (X ≃* planeLocal (F := F))) :
    ∃ f : X →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective f ∧ IsPGroup 2 f.ker := by
  rcases h with h | h
  · obtain ⟨e⟩ := h
    refine ⟨pointQuotient.comp e.toMonoidHom, pointQuotient_surjective.comp e.surjective,
      two_kernel_comp_equiv pointQuotient e ?_⟩
    change IsPGroup 2 (pointRadical (F := F))
    exact IsElementaryAbelian.isPGroup 2 _
  · obtain ⟨e⟩ := h
    refine ⟨Plane.quotientMap.comp e.toMonoidHom, Plane.quotientMap_surjective.comp e.surjective,
      two_kernel_comp_equiv Plane.quotientMap e ?_⟩
    change IsPGroup 2 (Plane.radical (F := F))
    exact IsElementaryAbelian.isPGroup 2 _

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g r : G} {L R : Subgroup G}

private theorem not_large_outer (d : Contrary T z L g R r)
    {M A S : Type*} [Group M] [Finite M] [Group A] [IsSimpleGroup A]
    [Group S] [IsSimpleGroup S] (e : (L ⧸ center L) ≃* M)
    (hi : (∃ f : pResidual 2 (innerAction d e).fixedSubgroup →* A,
      Function.Surjective f ∧ IsPGroup 2 f.ker) ∨
      Group.IsSolvable (innerAction d e).fixedSubgroup)
    (s : pResidual 2 (outerAction d e).fixedSubgroup ≃* S)
    (hs : ¬ Group.IsSolvable S) (hc : Nat.card A < Nat.card S) : False := by
  rcases hi with ⟨f, hf, hp⟩ | hi
  · let := hp.isNilpotent
    exact (ne_of_gt hc) (normal_residual_card_eq d e f hf s hs)
  · apply false_of_solvable_inner_nonsolvable_outer d e hi
    intro h
    let := h
    exact hs (Group.isSolvable_of_surjective (f := s.toMonoidHom) s.surjective)

/-- The nonbinary symplectic exclusion, conditional on the earlier rows only.
Relative normality forces the outer simple residual to equal the inner Levi
in order; the explicit derived-subfield and Suzuki orders contradict this. -/
theorem not_symplectic_model (d : Contrary T z L g R r)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (e : (L ⧸ pCore 2 L) ≃* Sp F) (rows : SymplecticInvolutionRows F n) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2) (Nat.pow_le_pow_right (by decide) hn)
  let := NaturalExtension.model_simple hq
  obtain ⟨x, _, _, hinner⟩ := rows.inner (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  have hi : (∃ f : pResidual 2 (innerAction d c).fixedSubgroup →*
      Matrix.SpecialLinearGroup (Fin 2) F, Function.Surjective f ∧ IsPGroup 2 f.ker) ∨
      Group.IsSolvable (innerAction d c).fixedSubgroup := by
    rcases hinner with ⟨_, h⟩ | ⟨_, h⟩
    · exact Or.inl (root_levi h)
    · let := h.isNilpotent
      exact Or.inr inferInstance
  rcases rows.outer (outerAction d c) (outerAction_order d c) (outerAction_outer d c) with
    ⟨m, hm, he, a, ha⟩ | ⟨m, he, a, ha, ⟨efix⟩⟩
  · have hF' : Nat.card F = 2 ^ (2 * m) := he ▸ hF
    have hK := FieldFixedResidual.card_halfField hm hF'
    let := FieldComponent.derived_isSimple hm hK
    let s := (MulAut.fixedResidualEquivOfCompatible 2 a (outerAction d c)
      (FieldFixedResidual.representative m) ha).trans
        (FieldFixedResidual.residualEquiv ((frobeniusEquiv F 2) ^ m))
    exact not_large_outer d c hi s (SymplecticModelOrders.derived_not_solvable hm hK)
      (SymplecticModelOrders.derived_field_card_gt hm hF' hK)
  · have hm : 0 < m := by omega
    let es : commutator (SuzukiMatrixGroup m) ≃* SuzukiMatrixGroup m :=
      (MulEquiv.subgroupCongr (suzuki_commutator_eq_top m hm)).trans topEquiv
    let s := ((MulAut.fixedResidualEquivOfCompatible 2 a (outerAction d c)
      (graphFieldAut m) ha).trans (residualEquivOfSuzuki m hm efix)).trans es
    let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    exact not_large_outer d c hi s
      (BenderSuzuki.External.suzukiMatrixGroup_not_isSolvable m hm)
      (SymplecticModelOrders.suzuki_card_gt hm (he ▸ hF))

/-- Every actual projective symplectic field witness is covered. No central
kernel is dropped: the two-core quotient first passes through the canonical
center quotient, and only the characteristic-two matrix center is trivial. -/
theorem not_psp_four_quotient (d : Contrary T z L g R r)
    (rows : SymplecticInvolutionTable) {n : ℕ} (hn : 2 ≤ n)
    (hmodel : ClassicalGroup.IsPSp (L ⧸ pCore 2 L) 2 (2 ^ n)) : False := by
  obtain ⟨F, hfield, hfin, hcard, ⟨e⟩⟩ := hmodel
  let := EvenProjective.charTwo_of_card hcard
  exact not_symplectic_model d hn hcard (e.trans EvenProjective.equiv.symm)
    (rows F n hn hcard)

private theorem not_two_inner_odd_outer (d : Contrary T z L g R r)
    {M : Type*} [Group M] [Finite M] (e : (L ⧸ center L) ≃* M)
    (hi : IsPGroup 2 (innerAction d e).fixedSubgroup)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ho : p ∣ Nat.card (pResidual 2 (outerAction d e).fixedSubgroup)) : False := by
  have hout : p ∣ Nat.card (centralImage (L.conjBy g) (residual (L.conjBy g) z)) := by
    rwa [Nat.card_congr (outerResidualEquiv d e).toEquiv]
  have hin := OtherFamilies.outer_odd_prime_dvd_inner d hp hp2 hout
  rw [Nat.card_congr (innerResidualEquiv d e).toEquiv] at hin
  have hd := hin.trans (card_subgroup_dvd_card (pResidual 2 (innerAction d e).fixedSubgroup))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hi
  rw [hk] at hd
  exact hp2 ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow hd) |>.resolve_left hp.ne_one)

/-- The actual derived binary matrix model, including root actors belonging
to full Sp₄(2). Its inner fixed groups are two-groups, whereas each outer
residual has the odd divisor supplied by its A₄ or Sz(2)′ equivalence. -/
theorem not_binary_derived_symplectic_model (d : Contrary T z L g R r)
    (e : (L ⧸ pCore 2 L) ≃* commutator (Sp (ZMod 2)))
    (rows : BinarySymplecticInvolutionRows) : False := by
  let : IsQuasisimple L := d.setup.component.quasisimple
  let c := (centerQuotientEquivTwoCore (component_oddCore d)).trans e
  obtain ⟨_, _, _, hi⟩ := rows.inner (innerAction d c)
    (innerAction_order d c) (innerAction_inner d c)
  rcases rows.outer (outerAction d c) (outerAction_order d c) (outerAction_outer d c) with
    ⟨_, _, _, ⟨s⟩⟩ | ⟨_, ⟨s⟩⟩
  · apply not_two_inner_odd_outer d c hi Nat.prime_three (by decide)
    rw [Nat.card_congr s.toEquiv, nat_card_alternatingGroup]
    norm_num
  · apply not_two_inner_odd_outer d c hi (show Nat.Prime 5 by decide) (by decide)
    rw [Nat.card_congr s.toEquiv]
    simp

/-- The source catalogue's quotient-first derived carrier is transported by
actual polar and coefficient equivalences to the derived Sp₄(2) model. -/
theorem not_binary_derived_psp_quotient (d : Contrary T z L g R r)
    (e : (L ⧸ pCore 2 L) ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2)))
    (rows : BinarySymplecticInvolutionRows) : False := by
  let f := Binary.projectiveDerivedEquivAlternatingSix.trans
    (Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm
  exact not_binary_derived_symplectic_model d (e.trans f) rows

end CFSG.Quasithin.Chapter16.Intersections.SylowSymmetry.ReverseDelta.Comparison.LieFamilies
