module

public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.Conventions
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.Statements
public import CFSG.Quasithin.Chapter16.Section01To02.OtherPreliminaries.JankoTwoHigmanSims.J2Reduction
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionFusion
public import Theory.SpecificGroups.PSL3Two.Automorphisms

/-!
# The outer involution class of the actual Hall--Janko carrier

The full automorphism equivalence from the standard-pair calculations turns
the checked permutation-extension fusion into exhaustive coverage of outer
involutions in `MulAut Carrier`. Transport gives an actual equivalence of
every fixed subgroup with the fixed subgroup of the displayed involution.

The representative's identification with Aut(L₃(2)) remains a separate model
calculation. The conditional consequences below explicitly retain that input;
they do not assert the source centralizer theorem before it is established.
Source: Aschbacher--Smith 16.1.5(8), 16.1.7(g), and 16.1.8, pp.1172–1173;
GLS3, Table 5.3g. The distinct residual-three-core endpoint is not duplicated.
-/

public section
namespace CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
open Sporadic.LeechRelated.J2 Sporadic.LeechRelated.J2.ExceptionalParabolics

private theorem concrete_action_surjective : Function.Surjective extensionAction :=
  ((Nat.bijective_iff_injective_and_card extensionAction).mpr
    ⟨extensionAction_injective, Nat.card_congr J2Reduction.fullAutomorphismEquiv.toEquiv⟩).2

/-- All outer involutions, rather than only the displayed one, belong to the
same conjugacy class in the full automorphism group. -/
theorem outer_involution_fusion (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) : IsConj involutionAut r := by
  obtain ⟨x, rfl⟩ := concrete_action_surjective r
  have hx : orderOf x = 2 :=
    (orderOf_injective extensionAction extensionAction_injective x).symm.trans hr
  have hxout : x ∉ intoExtension.range := by
    rintro ⟨g, rfl⟩
    exact ho ⟨g, extensionAction_inner g⟩
  have h := extensionAction.map_isConj
    (OuterInvolutionFusion.extension_outer_involution_fusion x hx hxout)
  simpa only [extensionAction_involution] using h

/-- Exhaustive coverage in the form required for fixed-subgroup transport. -/
theorem outer_involution_representative (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    ∃ e : MulAut Carrier, r = MulAut.congr e involutionAut := by
  obtain ⟨e, he⟩ := isConj_iff.mp (outer_involution_fusion r hr ho)
  refine ⟨e, ?_⟩
  rw [← he]
  rfl

/-- An actual equivalence of entire fixed subgroups for every outer involution. -/
theorem outer_fixed_representative (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* involutionAut.fixedSubgroup) := by
  obtain ⟨e, rfl⟩ := outer_involution_representative r hr ho
  exact ⟨(MulAut.fixedSubgroupCongr e involutionAut).symm⟩

/-- The one representative identification suffices for the entire outer
alternative of source 16.1.5(8). Its premise is a remaining model obligation. -/
theorem outer_alternative_of_representative
    (e : involutionAut.fixedSubgroup ≃* MulAut L3Two)
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) : J2InvolutionAlternative r := by
  obtain ⟨f⟩ := outer_fixed_representative r hr ho
  exact Or.inr ⟨ho, ⟨f.trans e⟩⟩

/-- The representative order determines every outer fixed-subgroup index.
In particular its two-part is eight, stronger than the bound in 16.1.8. -/
theorem outer_fixed_index_of_representative_card
    (hc : Nat.card involutionAut.fixedSubgroup = 336)
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) : r.fixedSubgroup.index = 1800 := by
  obtain ⟨e⟩ := outer_fixed_representative r hr ho
  have hcard : Nat.card r.fixedSubgroup = 336 := (Nat.card_congr e.toEquiv).trans hc
  have hi := r.fixedSubgroup.card_mul_index
  rw [hcard, FirstParabolic.card_carrier] at hi
  omega

/-- The PGL₂(7) table model gives the requested automorphism-group model
through the checked exceptional isomorphism. -/
theorem outer_fixed_equiv_of_representative
    (e : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) :
    Nonempty (r.fixedSubgroup ≃* MulAut L3Two) := by
  obtain ⟨f⟩ := outer_fixed_representative r hr ho
  exact ⟨(f.trans e).trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut⟩

/-- The representative identification gives actual component isomorphisms
for every outer involution, without imposing ambient normality on components. -/
theorem outer_component_equiv_of_representative
    (e : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g)
    (K : Subgroup r.fixedSubgroup)
    (hK : Theory.GroupTheory.IsComponent r.fixedSubgroup K) : Nonempty (K ≃* L3Two) := by
  obtain ⟨f⟩ := outer_fixed_equiv_of_representative e r hr ho
  obtain ⟨g⟩ := Matrix.PSL3Two.Automorphisms.component_equiv _ (hK.map_equiv f)
  exact ⟨(f.subgroupMap K).trans g⟩

/-- The outer fixed index is 1800 once the representative model is identified. -/
theorem outer_fixed_index_of_representative
    (e : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) : r.fixedSubgroup.index = 1800 := by
  apply outer_fixed_index_of_representative_card _ r hr ho
  rw [Nat.card_congr (e.trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut).toEquiv]
  exact Matrix.PSL3Two.Automorphisms.card_aut

/-- The exact index implies the two-part obstruction needed by source 16.1.8. -/
theorem four_dvd_outer_fixed_index_of_representative
    (e : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7))
    (r : MulAut Carrier) (hr : orderOf r = 2)
    (ho : ¬ ∃ g : Carrier, r = MulAut.conj g) : 4 ∣ r.fixedSubgroup.index := by
  rw [outer_fixed_index_of_representative e r hr ho]
  decide

end CFSG.Quasithin.Chapter16.OtherPreliminaries.JankoTwoHigmanSims.J2Outer
