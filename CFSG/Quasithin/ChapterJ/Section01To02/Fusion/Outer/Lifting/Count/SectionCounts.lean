module

public import CFSG.Quasithin.ChapterJ.Section01To02.Fusion.Outer.Lifting.Defs
public import Theory.Representation.BinaryConjugationSection.InvolutionCount

/-!
# The actual binary section counts for J.2.6

Freeness gives fixed-space orders four on U/Z and eight on Q/U. The
central subgroup Z contributes two inverted elements. Applying the
section-fiber formula twice gives 8 · 4 · 2 = 64. Elementary abelianness
of U also makes the lifted displacements actual fixed elements of U.

Source: Aschbacher–Smith, J.2.6, printed p.435 (PDF p.446).
-/

public section
noncomputable section
open Subgroup Representation Representation.BinaryConjugationSection
namespace CFSG.Quasithin.ChapterJ.Fusion.Outer
variable {G : Type*} [Group G] [Finite G]

/-- Fixed vectors in the literal U/Z section lift to fixed elements of U. -/
theorem fixed_lift_U (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (i : d.H) (hi : (i : G) ^ 2 = 1)
    (hfree : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (v : FourSpace) (hv : d.ru2.naturalAction.action (d.ru2.quotientMap i) v = v) :
    ∃ u : d.U, (d.ru2.natural.coordinates u).toAdd = v ∧
      (i : G) * u * (i : G)⁻¹ = u := by
  let := d.elementary_U_of_card_Z hZ
  exact d.ru2.natural.fixed_lift i hi hfree v hv

private theorem card_inverting_Z (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2)
    (i : d.H) : Nat.card (Inverting d.Z (i : G)) = 2 := by
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv (p := fun z : d.Z =>
    (i : G) * z * (i : G)⁻¹ = (z : G)⁻¹) ?_), hZ]
  intro z
  have hz : (z : G)⁻¹ = z := by
    apply inv_eq_of_mul_eq_one_left
    have h := congrArg Subtype.val (pow_card_eq_one' (x := z))
    simpa only [hZ, Subgroup.coe_pow, pow_two, Subgroup.coe_mul, Subgroup.coe_one] using h
  rw [hz, ← i.property z z.property, mul_inv_cancel_right]

/-- The four fixed coordinates in the natural section, with their actual action. -/
theorem card_natural_fixed_of_free (d : TypeRuSetup G) (i : d.H)
    (hi : (i : G) ^ 2 = 1)
    (hfree : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i)) :
    Nat.card (Fixed (d.ru2.naturalAction.action (d.ru2.quotientMap i))) = 4 := by
  have h := card_fixed_sq ((d.ru2.naturalAction.action.comp d.ru2.quotientMap) i)
    (representation_sq _ i hi) hfree
  have hc : Nat.card FourSpace = 16 := by
    rw [Nat.card_eq_fintype_card]
    exact SL2FourNatural.card_vector
  rw [hc] at h
  change 16 = Nat.card (Fixed (d.ru2.naturalAction.action (d.ru2.quotientMap i))) *
    Nat.card (Fixed (d.ru2.naturalAction.action (d.ru2.quotientMap i))) at h
  nlinarith

/-- The eight fixed coordinates in the six-dimensional section. -/
theorem card_six_fixed_of_free (d : TypeRuSetup G) (i : d.H)
    (hi : (i : G) ^ 2 = 1)
    (hfree : FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    Nat.card (Fixed (d.ru2.sixAction (d.ru2.quotientMap i))) = 8 := by
  have h := card_fixed_sq ((d.ru2.sixAction.comp d.ru2.quotientMap) i)
    (representation_sq _ i hi) hfree
  have hc : Nat.card SixSpace = 64 := by norm_num [SixSpace, Nat.card_fun, Nat.card_zmod]
  rw [hc] at h
  change 64 = Nat.card (Fixed (d.ru2.sixAction (d.ru2.quotientMap i))) *
    Nat.card (Fixed (d.ru2.sixAction (d.ru2.quotientMap i))) at h
  nlinarith

/-- The natural-section fiber count is four times the two central lifts. -/
theorem card_inverting_U (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) (i : d.H)
    (hi : (i : G) ^ 2 = 1)
    (hfree : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i)) :
    Nat.card (Inverting d.U (i : G)) = 8 := by
  rw [card_inverting_section d.ru2.natural i hi hfree, MonoidHom.comp_apply,
    card_natural_fixed_of_free d i hi hfree, card_inverting_Z d hZ i]

/-- The two actual section maps give the source's 8 · 4 · 2 count. -/
theorem card_inverting_Q (d : TypeRuSetup G) (hZ : Nat.card d.Z = 2) (i : d.H)
    (hi : (i : G) ^ 2 = 1)
    (hnatural : FreeAt d.ru2.naturalAction.action (d.ru2.quotientMap i))
    (hsix : FreeAt d.ru2.sixAction (d.ru2.quotientMap i)) :
    Nat.card (Inverting d.Q (i : G)) = 64 := by
  rw [card_inverting_section d.ru2.six i hi hsix, MonoidHom.comp_apply,
    card_six_fixed_of_free d i hi hsix, card_inverting_U d hZ i hi hnatural]

end CFSG.Quasithin.ChapterJ.Fusion.Outer
