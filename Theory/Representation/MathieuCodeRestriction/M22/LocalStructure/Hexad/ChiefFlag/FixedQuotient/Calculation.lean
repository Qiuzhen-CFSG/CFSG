module

public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Displacement
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.ChiefFlag.FixedQuotient.Alternatives

/-!
# The cubic calculation on the actual hexad code flag

Restrict the literal code spaces to the commuting order-three actor. Its
involution fixed space is invariant because the actors commute. The checked
transvection rank and earlier involution rank supply the two fixed dimensions.
The cubic calculation proves full quotient displacement, the source sum
identity, and equality of the intersections with V6 and V5. Rank-nullity then
excludes V6 as the preimage of the fixed quotient.

Source: Aschbacher--Smith, H.16.4(5), printed p.403, 1 March 2004.
-/

@[expose] public section
noncomputable section
namespace MathieuCode.Hexad.ChiefFlag.FixedQuotientData
open Representation Representation.BinaryOffender FixedQuotientCubic
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E]

abbrev cubicAction (y : Stabilizer) := codeAction.comp (Subgroup.zpowers y).subtype
abbrev cubicFive (y : Stabilizer) := restrict codeAction V5 (Subgroup.zpowers y)
abbrev cubicSix (D : Actions E) (y : Stabilizer) := restrict codeAction D.six (Subgroup.zpowers y)

/-- The actual involution-fixed code space with the commuting cubic action. -/
def cubicFixed (y : Stabilizer) (z : Kernel) (hyz : Commute y.val z.val) :
    Subrepresentation (cubicAction y) where
  toSubmodule := fixedSpace m22OuterCodeRepresentation (Subgroup.zpowers z.val)
  apply_mem_toSubmodule g v hv := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    have hc : Commute g.val.val z.val := by
      rw [← hn]
      exact hyz.zpow_left n
    apply (mem_fixedSpace_zpowers_iff m22OuterCodeRepresentation z.val _).mpr
    have hv' := (mem_fixedSpace_zpowers_iff m22OuterCodeRepresentation z.val v).mp hv
    change m22OuterCodeRepresentation z.val (m22OuterCodeRepresentation g.val.val v) =
      m22OuterCodeRepresentation g.val.val v
    calc
      _ = m22OuterCodeRepresentation g.val.val (m22OuterCodeRepresentation z.val v) := by
        simp only [← Module.End.mul_apply, ← map_mul, hc.eq]
      _ = _ := congrArg (m22OuterCodeRepresentation g.val.val) hv'

theorem element_fixed_stabilizer (z : Kernel) :
    fixedSpace codeAction (Subgroup.zpowers (Subgroup.inclusion kernel_le_stabilizer z)) =
      fixedSpace m22OuterCodeRepresentation (Subgroup.zpowers z.val) := by
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
  rfl

/-- The complete numerical and subspace calculation, with only the global
order-three displacement lower bound left explicit. -/
theorem code_cubic_calculation (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (y : Stabilizer) (hy : orderOf y = 3) (z : Kernel) (hz : z ≠ 1)
    (hyz : Commute y.val z.val)
    (hmove : 6 ≤ fixedCodim codeAction (Subgroup.zpowers y)) :
    fixedCodim (cubicFive y).toRepresentation ⊤ = 2 ∧
      fixedCodim (cubicAction y) ⊤ = 6 ∧
      fixedCodim (cubicSix D y).quotientRepresentation ⊤ = 4 ∧
      fixedSpace (cubicSix D y).quotientRepresentation ⊤ = ⊥ ∧
      V5.toSubmodule ⊔ (cubicFixed y z hyz).toSubmodule = V5.toSubmodule ⊔
        (Coinvariants.ker (cubicFixed y z hyz).toRepresentation).map
          (cubicFixed y z hyz).toSubmodule.subtype ∧
      D.six.toSubmodule ⊓ (cubicFixed y z hyz).toSubmodule =
        V5.toSubmodule ⊓ (cubicFixed y z hyz).toSubmodule := by
  have hc : Nat.card (Subgroup.zpowers y) = 3 := (Nat.card_zpowers y).trans hy
  have hC : Module.finrank (ZMod 2) (cubicFixed y z hyz).toSubmodule = 6 :=
    code_element_fixed_finrank h z.val z.property (fun he => hz (Subtype.ext he))
  have hAC : Module.finrank (ZMod 2)
      (V5.toSubmodule ⊓ (cubicFixed y z hyz).toSubmodule : Submodule (ZMod 2) M22Code) = 4 := by
    have he := (subrepresentationFixedEquiv codeAction V5
      (Subgroup.zpowers (Subgroup.inclusion kernel_le_stabilizer z))).finrank_eq
    rw [element_fixed_stabilizer] at he
    exact he.symm.trans (transvection_fixed_finrank D h h24 z hz)
  have hm : 6 ≤ fixedCodim (cubicAction y) ⊤ := by
    rw [fixedCodim_restrict_top]
    exact hmove
  have hma : fixedCodim (cubicFive y).toRepresentation ⊤ ≤ 2 := by
    change fixedCodim (V5.toRepresentation.comp (Subgroup.zpowers y).subtype) ⊤ ≤ 2
    rw [fixedCodim_restrict_top]
    exact five_displacement_le_two D h h24 y hy z hz hyz
  exact source_calculation (cubicAction y) hc (cubicFive y) (cubicSix D y)
    (cubicFixed y z hyz) D.five_le_six finrank_m22Code
    (codeCommutatorSubrepresentation_finrank h h24) D.six_dim hC hAC hm hma

private theorem cyclic_commutator_eq_top_of_fixed
    {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (ρ : Representation (ZMod 2) G W)
    (y : G) (hf : fixedSpace ρ (Subgroup.zpowers y) = ⊥) :
    Coinvariants.ker (ρ.comp (Subgroup.zpowers y).subtype) = ⊤ := by
  have hk : (ρ y - LinearMap.id).ker = ⊥ := by
    rw [← hf]
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    exact sub_eq_zero
  have hn := (ρ y - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hn
  have hr := Submodule.eq_top_of_finrank_eq hn
  apply top_unique
  intro v _
  obtain ⟨w, rfl⟩ := (hr.symm ▸ (show v ∈ (⊤ : Submodule (ZMod 2) W) from trivial) :
      v ∈ (ρ y - LinearMap.id).range)
  exact Coinvariants.sub_mem_ker (⟨y, Subgroup.mem_zpowers y⟩ : Subgroup.zpowers y) w

/-- In the original stabilizer notation the cubic moves exactly two
five-space dimensions and its commutator on V/V6 is the whole quotient. -/
theorem code_cubic_displacement (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (y : Stabilizer) (hy : orderOf y = 3) (z : Kernel) (hz : z ≠ 1)
    (hyz : Commute y.val z.val)
    (hmove : 6 ≤ fixedCodim codeAction (Subgroup.zpowers y)) :
    fixedCodim V5.toRepresentation (Subgroup.zpowers y) = 2 ∧
      Coinvariants.ker (D.six.quotientRepresentation.comp (Subgroup.zpowers y).subtype) = ⊤ := by
  have hc := code_cubic_calculation D h h24 y hy z hz hyz hmove
  have htwo : fixedCodim (V5.toRepresentation.comp (Subgroup.zpowers y).subtype) ⊤ = 2 := hc.1
  refine ⟨(fixedCodim_restrict_top V5.toRepresentation (Subgroup.zpowers y)).symm.trans htwo, ?_⟩
  have hf' : fixedSpace (D.six.quotientRepresentation.comp (Subgroup.zpowers y).subtype) ⊤ = ⊥ :=
    hc.2.2.2.1
  have hf : fixedSpace D.six.quotientRepresentation (Subgroup.zpowers y) = ⊥ :=
    (fixedSpace_restrict_top D.six.quotientRepresentation (Subgroup.zpowers y)).symm.trans hf'
  exact cyclic_commutator_eq_top_of_fixed D.six.quotientRepresentation y hf

/-- If V6/V1 were fixed, the involution would have rank at most one on V6.
The proved intersection calculation instead gives fixed dimension four,
contradicting rank-nullity in dimension six. -/
theorem fixedLift_ne_six_of_cubic (D : Actions E)
    (h : OuterRestrictionInput m22SourceOctad) (h24 : AmbientFixedInput m22SourceOctad)
    (y : Stabilizer) (hy : orderOf y = 3) (z : Kernel) (hz : z ≠ 1)
    (hyz : Commute y.val z.val)
    (hmove : 6 ≤ fixedCodim codeAction (Subgroup.zpowers y)) :
    fixedLift ≠ D.six := by
  intro heq
  have hinter := (code_cubic_calculation D h h24 y hy z hz hyz hmove).2.2.2.2.2
  let a := Subgroup.inclusion kernel_le_stabilizer z
  have h1five : V1 ≤ V5 := by
    change V1.toSubmodule ≤ V5.toSubmodule
    rw [codeCommutatorSubrepresentation_space]
    exact codeFixed_le_commutator h h24
  let S := sectionLower codeAction V1 D.six
  have hdS : Module.finrank (ZMod 2) S.toSubmodule = 1 :=
    (sectionLowerEquiv codeAction (h1five.trans D.five_le_six)).finrank_eq.trans
      (codeFixedSubrepresentation_finrank h)
  have hr : (D.six.toRepresentation a - LinearMap.id).range ≤ S.toSubmodule := by
    rintro _ ⟨v, rfl⟩
    exact (mem_fixedLift v.val).mp (heq.symm ▸ v.property) z
  have hle : fixedCodim D.six.toRepresentation (Subgroup.zpowers a) ≤ 1 := by
    rw [fixedCodim_zpowers_eq_displacement_rank]
    exact (Submodule.finrank_mono hr).trans hdS.le
  have hfix : Module.finrank (ZMod 2)
      (fixedSpace D.six.toRepresentation (Subgroup.zpowers a)) = 4 := by
    rw [(subrepresentationFixedEquiv codeAction D.six (Subgroup.zpowers a)).finrank_eq]
    change Module.finrank (ZMod 2)
      (D.six.toSubmodule ⊓ fixedSpace codeAction
        (Subgroup.zpowers (Subgroup.inclusion kernel_le_stabilizer z)) :
          Submodule (ZMod 2) M22Code) = 4
    rw [element_fixed_stabilizer]
    change Module.finrank (ZMod 2)
      (D.six.toSubmodule ⊓ (cubicFixed y z hyz).toSubmodule : Submodule (ZMod 2) M22Code) = 4
    rw [hinter]
    have he := (subrepresentationFixedEquiv codeAction V5 (Subgroup.zpowers a)).finrank_eq
    change _ = Module.finrank (ZMod 2)
      (V5.toSubmodule ⊓ fixedSpace codeAction
        (Subgroup.zpowers (Subgroup.inclusion kernel_le_stabilizer z)) :
          Submodule (ZMod 2) M22Code) at he
    rw [element_fixed_stabilizer] at he
    exact he.symm.trans (transvection_fixed_finrank D h h24 z hz)
  have hdim := fixedCodim_add_finrank D.six.toRepresentation (Subgroup.zpowers a)
  have hs := D.six_dim
  omega

end MathieuCode.Hexad.ChiefFlag.FixedQuotientData
