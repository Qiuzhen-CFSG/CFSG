module

public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo.ExceptionalComparison.Generation
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# Assembly of the explicit unitary–symplectic comparison

Two verified matrix maps share an eleven-relator presentation. The symplectic
map is surjective by a transvection orbit argument. If the presentation has
at most 25920 elements, it is isomorphic to the actual simple PSp₄(3).
The unitary map is nontrivial, hence injective. An upper bound of 25920 for
the literal special unitary group then makes this second map surjective.
Finally the already proved scalar-kernel calculation identifies SU with PSU.

The two upper bounds remain explicit prerequisites in this module. It does
not yet export the unconditional exceptional isomorphism `standardEquivPSp`.
Its source use is Aschbacher–Smith I.1.4(1), printed p.408; see GLS3 §2.2's
exceptional-isomorphism table and §2.7. Final universal-cover assembly belongs
to the separate parent module `UnitaryTwo`.
-/

public section
noncomputable section
open Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime
namespace Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
namespace ExceptionalComparison

/-- The order of the literal projective symplectic endpoint. -/
theorem card_projective_symplectic : Nat.card (PSp (ZMod 3)) = 25920 := by
  have hs : Nat.card (Sp (ZMod 3)) = 51840 := by
    simpa using Theory.SpecificGroups.SymplecticFour.card_sp (ZMod 3)
  have hc : Nat.card (Subgroup.center (Sp (ZMod 3))) = 2 :=
    card_center (by decide : (2 : ZMod 3) ≠ 0)
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center (Sp (ZMod 3)))
  rw [hs, hc] at h
  change 51840 = Nat.card (PSp (ZMod 3)) * 2 at h
  omega

/-- The finite presentation bound, combined with proved symplectic generation,
makes the prescribed symplectic map an isomorphism. -/
def presentationEquivPSp [Finite Presentation] (hp : Nat.card Presentation ≤ 25920) :
    Presentation ≃* PSp (ZMod 3) :=
  MulEquiv.ofBijective toProjectiveSymplectic
    (toProjectiveSymplectic_surjective.bijective_of_nat_card_le
      (by simpa only [card_projective_symplectic] using hp))

/-- Simplicity of the actual symplectic quotient forces injectivity of the
nontrivial unitary representation once presentation exactness is established. -/
theorem toSpecial_injective [Finite Presentation] (hp : Nat.card Presentation ≤ 25920) :
    Function.Injective toSpecial := by
  let : IsSimpleGroup (PSp (ZMod 3)) := projective_simple (by norm_num)
  let : IsSimpleGroup Presentation := (presentationEquivPSp hp).isSimpleGroup
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rcases (inferInstance : toSpecial.ker.Normal).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    apply toSpecial_generator_zero_ne_one
    have hm : PresentedGroup.of 0 ∈ toSpecial.ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact hm

/-- A genuine comparison obtained from the two remaining independent bounds. -/
def specialEquivPSp_of_bounds [Finite Presentation]
    (hp : Nat.card Presentation ≤ 25920) (hu : Nat.card StandardSU ≤ 25920) :
    StandardSU ≃* PSp (ZMod 3) := by
  let ep := presentationEquivPSp hp
  have hc : Nat.card Presentation = 25920 :=
    (Nat.card_congr ep.toEquiv).trans card_projective_symplectic
  let eu : Presentation ≃* StandardSU := MulEquiv.ofBijective toSpecial
    ((toSpecial_injective hp).bijective_of_nat_card_le (by simpa only [hc] using hu))
  exact eu.symm.trans ep

end ExceptionalComparison

/-- Conditional final assembly on the specified standard projective carrier.
The presentation and unitary bounds must both be proved before dropping these
premises and exporting `standardEquivPSp`. -/
def standardEquivPSp_of_bounds [Finite ExceptionalComparison.Presentation]
    (hp : Nat.card ExceptionalComparison.Presentation ≤ 25920)
    (hu : Nat.card StandardSU ≤ 25920) : StandardPSU ≃* PSp (ZMod 3) :=
  (specialProjectiveEquiv standardForm standard_field_card standard_conj).symm.trans
    (ExceptionalComparison.specialEquivPSp_of_bounds hp hu)

end Theory.SpecificGroups.HigherClassicalCovers.UnitaryTwo
