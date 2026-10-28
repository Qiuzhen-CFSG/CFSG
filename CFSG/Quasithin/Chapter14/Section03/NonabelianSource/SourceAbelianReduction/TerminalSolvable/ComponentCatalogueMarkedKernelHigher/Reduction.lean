module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueMarkedKernelFixedPoint
public import Theory.Representation.NormalConstituentDisplacement.MultiplicityBound

/-!
# Fixed-point reduction and quotient endgame for higher multiplicity

The numerical part of G.10.16 bounds the whole binary dimension by twice
the common faithful constituent degree whenever a nonidentity actor has
displacement at most two. Thus, at higher multiplicity, the proved same-vector
G.11.1(3) alternative forces the original marked fixed line.

At the other end of the argument, the literal quotient X/C_X(H) of order
two gives exactly two actions on I. A transvection on I then has too large
a fixed space. This proves the conditional small-component conclusion by
contradiction, retaining the rank lost to the original actor kernel.

StabilizedOrthogonalConstituents and QuotientTransvection specify the two
remaining source outputs. Neither is asserted by these reductions or added
to MarkedSource. The orthogonal-constituent construction and the actual G.6.4
model exclusions must discharge them in the final higher-multiplicity theorem.

Source: Aschbacher--Smith, G.10.16(4), G.11.8(2), and G.11.9, printed
pp.363--364,368--369; the original terminal application is14.3.15, p.994.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open scoped IsMulCommutative
variable {G : Type*} [Group G] [Finite G]
namespace MarkedSource
variable {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  {L : Subgroup F.TerminalHdot} {I : Submodule (ZMod 2) (Additive F.Uhat)}
  (s : MarkedSource T M Mc F g B v L I)
include s

/-- The numerical G.10.16(4) implication on the original source module. -/
theorem dimension_le_twice_of_small_displacement
    (a : F.terminalDot (F.X g)) (ha : a ≠ 1)
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range (F.terminalRepresentation a - 1)) ≤ 2) :
    Module.finrank (ZMod 2) (Additive F.Uhat) ≤ 2 * Module.finrank (ZMod 2) I := by
  let : (componentOrbit L ⊤).Normal := componentOrbit_top_normal L
  exact NormalConstituentDisplacement.finrank_le_twice_of_small_displacement
    F.terminalRepresentation (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
    s.hypothesis.faithful (componentOrbit L ⊤) (Module.finrank (ZMod 2) I)
    s.dimension_gt_two s.constituent_finrank_eq s.constituent_faithful a
    (fun he => ha (Subtype.ext he)) hr

/-- The higher-multiplicity branch rules out every small nonidentity displacement. -/
theorem displacement_gt_two_of_higher_dimension
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (a : F.terminalDot (F.X g)) (ha : a ≠ 1) :
    2 < Module.finrank (ZMod 2) (LinearMap.range (F.terminalRepresentation a - 1)) := by
  by_contra hn
  exact (not_lt_of_ge (s.dimension_le_twice_of_small_displacement a ha (by omega))) hd

/-- The precise G.11.8(2) consequence needed here, without any appeal to G.11.7
or to a counterexample to the entire G.11.2 classification. -/
theorem fixedSpace_eq_point_of_higher_dimension
    (hfp : FixedPointAlternative (F := F) (g := g) (v := v))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} := by
  rcases hfp with hfix | ⟨a,ha,hr,_⟩
  · exact hfix
  · exact (not_lt_of_ge hr (s.displacement_gt_two_of_higher_dimension hd a ha)).elim

omit s in
/-- The genuine geometric obligation in G.11.9(1), on the original module.
The rank-one displacement on each such witness is already proved upstream. -/
def StabilizedOrthogonalConstituents : Prop :=
  ∀ x : F.terminalDot (F.X g),
    (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) →
    ∃ J : Submodule (ZMod 2) (Additive F.Uhat),
      IsIrrPlus F.terminalRepresentation (componentOrbit L ⊤) J ∧
      v ∉ J ∧ J ≤ B.orthogonal I ∧
      (x : F.TerminalHdot) ∈ subspaceStabilizer F.terminalRepresentation J

omit s in
/-- The original G.11.9(2,4) output needed by the final contradiction.
The quotient is by the literal orbit centralizer, and the displacement is on
the original selected I, not on an unspecified isomorphic module. -/
def QuotientTransvection : Prop :=
  Nat.card ((F.terminalDot (F.X g)) ⧸
    (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
      (F.terminalDot (F.X g))) = 2 ∧
  ∃ x : F.terminalDot (F.X g),
    (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot) ∧
    Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp I.subtype)) = 1

/-- A fixed marked line is incompatible with a transvection on I when every
actor induces either that same transvection or the identity on I. -/
theorem false_of_two_actor_actions
    (hfix : fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v})
    (x : F.terminalDot (F.X g))
    (hactions : ∀ y : F.terminalDot (F.X g),
      (∀ w : I, F.terminalRepresentation y w = w) ∨
      (∀ w : I, F.terminalRepresentation y w = F.terminalRepresentation x w))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp I.subtype)) ≤ 1) : False := by
  let f := (F.terminalRepresentation x - (1 : Module.End (ZMod 2) (Additive F.Uhat))).comp I.subtype
  have hle : f.ker.map I.subtype ≤ fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) := by
    rintro w ⟨u,hu,rfl⟩ y
    rcases hactions y with hf | he
    · exact hf u
    · exact (he u).trans (sub_eq_zero.mp hu)
  have hk : Module.finrank (ZMod 2) f.ker ≤ 1 := by
    have he := (Submodule.equivMapOfInjective I.subtype I.subtype_injective f.ker).finrank_eq
    have hm := Submodule.finrank_mono hle
    rw [hfix] at hm
    have hb : Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {v}) ≤ 1 := by
      simpa using (finrank_span_le_card (R := ZMod 2) ({v} : Set (Additive F.Uhat)))
    omega
  have he := f.finrank_range_add_finrank_ker
  have hd := s.dimension_gt_two
  change Module.finrank (ZMod 2) f.range ≤ 1 at hr
  omega


/-- An actual quotient of order two gives exactly two actions on the marked
constituent, even when the original actor has a nontrivial kernel. -/
theorem two_actor_actions_of_quotient_card_two
    (hq : Nat.card ((F.terminalDot (F.X g)) ⧸
      (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2)
    (x : F.terminalDot (F.X g))
    (hx : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
    ∀ y : F.terminalDot (F.X g),
      (∀ w : I, F.terminalRepresentation y w = w) ∨
      (∀ w : I, F.terminalRepresentation y w = F.terminalRepresentation x w) := by
  let X := F.terminalDot (F.X g)
  let Y := (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf X
  let q := QuotientGroup.mk' Y
  have hxq : q x ≠ 1 := fun he => hx ((QuotientGroup.eq_one_iff x).mp he)
  obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : X ⧸ Y)).mp hq
  have hfix (a : X) (ha : (a : F.TerminalHdot) ∈ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)) :
      ∀ w : I, F.terminalRepresentation a w = w :=
    (source_marked_constituent_fixes_iff_centralizes s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card (Classical.choice s.centralizer_quotient)
      F s.nonabelian g s.parabolic_mem s.normalizer_not_mem s.nonsolvable s.hypothesis
      s.component s.moved s.selected.isIrrPlus s.point_mem a).mpr ha
  intro y
  by_cases hy : q y = 1
  · exact Or.inl (hfix y ((QuotientGroup.eq_one_iff y).mp hy))
  · right
    have hyx : q y = q x := (hz (q y) hy).trans (hz (q x) hxq).symm
    have hxy : q (x⁻¹ * y) = 1 := by rw [map_mul,map_inv,hyx,inv_mul_cancel]
    have hxyfix := hfix (x⁻¹ * y) ((QuotientGroup.eq_one_iff (x⁻¹ * y)).mp hxy)
    intro w
    have he := congrArg (F.terminalRepresentation x) (hxyfix w)
    simpa only [← Module.End.mul_apply,← map_mul,Subgroup.coe_mul,Subgroup.coe_inv,
      mul_inv_cancel_left] using he

/-- The end of G.11.9 on the literal marked source: quotient rank one and
rank-one displacement on I contradict the fixed point supplied by G.11.8. -/
theorem false_of_higher_dimension_quotient_card_two
    (hfp : FixedPointAlternative (F := F) (g := g) (v := v))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hq : Nat.card ((F.terminalDot (F.X g)) ⧸
      (centralizer (componentOrbit L ⊤ : Set F.TerminalHdot)).subgroupOf
        (F.terminalDot (F.X g))) = 2)
    (x : F.terminalDot (F.X g))
    (hx : (x : F.TerminalHdot) ∉ centralizer (componentOrbit L ⊤ : Set F.TerminalHdot))
    (hr : Module.finrank (ZMod 2)
      (LinearMap.range ((F.terminalRepresentation x - 1).comp I.subtype)) ≤ 1) : False :=
  s.false_of_two_actor_actions (s.fixedSpace_eq_point_of_higher_dimension hfp hd) x
    (s.two_actor_actions_of_quotient_card_two hq x hx) hr

/-- Conditional final assembly of the higher-multiplicity image branch.
The remaining recognition input is supplied by the remaining stabilized-
constituent and rank-one-classification arguments in this task. -/
theorem smallComponentImage_of_higher_dimension_quotientTransvection
    (hfp : FixedPointAlternative (F := F) (g := g) (v := v))
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat))
    (hq : QuotientTransvection (F := F) (g := g) (L := L) (I := I)) :
    SmallComponentImage L := by
  obtain ⟨hc,x,hx,hr⟩ := hq
  exact (s.false_of_higher_dimension_quotient_card_two hfp hd hc x hx hr.le).elim

/-- The original source discharges the selected-vector alternative in the
higher-multiplicity branch. No G.11.2 counterexample is needed. -/
theorem source_fixedSpace_eq_point_of_higher_dimension
    (hd : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) (Additive F.Uhat)) :
    fixedSpace F.terminalRepresentation (F.terminalDot (F.X g)) =
      Submodule.span (ZMod 2) {v} :=
  s.fixedSpace_eq_point_of_higher_dimension s.fixedPointAlternative hd

end MarkedSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
