module

public import GorensteinWalter.PGammaL2
public import GorensteinWalter.PGL2Cardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import Theory.SpecificGroups.PSL3Two.Parabolics.LinearModel
public import Theory.GroupTheory.GeneralizedFitting.AutomorphismSimple

/-!
# Aut(PSL₃(2)) and PGL₂(7)

The prime-field specialization of semilinear automorphism coverage identifies
Aut(PSL₂(7)) with PGL₂(7), since prime fields have no nonidentity field
automorphisms. Transport along the checked exceptional isomorphism identifies
the requested matrix PSL₃(2) model. Its automorphism group has order 336,
and every component is actually isomorphic to PSL₃(2).

Source: GLS3, Table 5.3g and Aschbacher--Smith 16.1.5(8), 16.1.7(g), p.1172.
The exceptional-isomorphism import retains its ATLAS license and attribution.
-/

public section
namespace Matrix.PSL3Two.Automorphisms
open GorensteinWalter Theory.GroupTheory
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private theorem seven_prime_power : IsOddPrimePower (Nat.card (ZMod 7)) := by
  refine ⟨7, 1, by decide, by decide, by decide, ?_⟩
  norm_num

private theorem seven_gt_three : 3 < Nat.card (ZMod 7) := by norm_num

/-- The actual PGL₂(7) conjugation action exhausts Aut(PSL₂(7)). -/
noncomputable def pgl2SevenEquivAutPSL2 :
    PGL2 (ZMod 7) ≃* MulAut (PSL2 (ZMod 7)) := by
  apply MulEquiv.ofBijective
    (pgl2InnerAutPSL2 (ZMod 7) seven_prime_power seven_gt_three)
  refine ⟨pgl2InnerAutPSL2_injective _ _ _, ?_⟩
  intro a
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod 7)
    (p := 7) (f := 1) (by norm_num) seven_prime_power seven_gt_three a
  have hxleft : SemidirectProduct.inl x.left = x := by
    apply SemidirectProduct.ext
    · rfl
    · exact Subsingleton.elim _ _
  refine ⟨x.left, ?_⟩
  rw [← pGammaL2ToMulAutPSL2_inl, hxleft]
  exact hx

/-- Comparison with Aut of the exact matrix group PSL₃(2), not a family tag. -/
noncomputable def pgl2SevenEquivAut : PGL2 (ZMod 7) ≃* MulAut PSL :=
  pgl2SevenEquivAutPSL2.trans
    (MulAut.congr Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two)

/-- The full automorphism group has order 336. -/
theorem card_aut : Nat.card (MulAut PSL) = 336 := by
  rw [← Nat.card_congr pgl2SevenEquivAut.toEquiv, pgl2_card_formula]
  norm_num

/-- The projective binary matrix group is centerless. -/
theorem center_psl_eq_bot : Subgroup.center PSL = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have h := (Subgroup.centerCongr equiv).symm ⟨x, hx⟩ |>.property
  change equiv.symm x ∈ Subgroup.center SL at h
  have heq : equiv.symm x = 1 := Subgroup.mem_bot.mp (center_eq_bot.le h)
  exact Subgroup.mem_bot.mpr (equiv.symm.map_eq_one_iff.mp heq)

/-- Every component of Aut(PSL₃(2)) is isomorphic to the actual PSL₃(2) model. -/
theorem component_equiv (K : Subgroup (MulAut PSL))
    (hK : IsComponent (MulAut PSL) K) : Nonempty (K ≃* PSL) := by
  let := Atlas.Comparisons.Exceptional.psl3Two_simple
  exact hK.equiv_simple_of_automorphism center_psl_eq_bot

end Matrix.PSL3Two.Automorphisms
