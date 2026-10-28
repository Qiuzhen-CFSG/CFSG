module

public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.SpecificGroups.SymmetricSix.Parabolics.Actions
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Ambient
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# The binary projective symplectic group and its derived subgroup

The faithful six-letter polar representation maps S₆ into the actual
four-dimensional symplectic matrix group over `ZMod 2`. Both groups have
order 720, so this particular map is an isomorphism. Transporting the
trivial center of S₆ identifies the central quotient with S₆ as well.
Restricting that equivalence to the commutator subgroup gives A₆.

These are multiplicative equivalences of the concrete carriers, including
the commutator of the central quotient, rather than identifications from
order alone. They justify the small derived symplectic endpoint in
Aschbacher–Smith, *The Classification of Quasithin Groups*, Theorem 0.1.2(1),
printed p.4. The polar representation is developed from I.5.4 and I.5.8–9,
printed pp.420–422, in the imported six-letter action module. Attribution
for the symplectic order calculation is retained in `Sylow/AmbientOrder`.
-/

public noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.Binary

open Theory.SpecificGroups.SymmetricSix

theorem card_sp_two : Nat.card (Sp (ZMod 2)) = 720 := by
  rw [card_sp]
  norm_num

/-- The faithful polar representation is onto the binary symplectic group. -/
def symmetricSixEquiv : S6 ≃* Sp (ZMod 2) :=
  MulEquiv.ofBijective polarRepresentation
    ((Nat.bijective_iff_injective_and_card _).mpr
      ⟨polarRepresentation_injective, s6_order.trans card_sp_two.symm⟩)

/-- The equivalence uses the existing explicit polar representation. -/
theorem symmetricSixEquiv_apply (g : S6) :
    symmetricSixEquiv g = polarRepresentation g := by
  change polarRepresentation g = polarRepresentation g
  rfl

theorem center_sp_two : Subgroup.center (Sp (ZMod 2)) = ⊥ := by
  apply bot_unique
  intro x hx
  have hy := (Subgroup.centerCongr symmetricSixEquiv.symm ⟨x, hx⟩).property
  change symmetricSixEquiv.symm x ∈ Subgroup.center S6 at hy
  rw [s6_center_eq_bot, Subgroup.mem_bot] at hy
  exact symmetricSixEquiv.symm.injective (hy.trans (map_one _).symm)

/-- The actual central quotient PSp₄(2) is isomorphic to S₆. -/
def projectiveEquivSymmetricSix :
    (Sp (ZMod 2) ⧸ Subgroup.center (Sp (ZMod 2))) ≃* S6 :=
  ((QuotientGroup.quotientMulEquivOfEq center_sp_two).trans
    QuotientGroup.quotientBot).trans symmetricSixEquiv.symm

/-- The commutator carrier of PSp₄(2), with the quotient taken first, is A₆. -/
def projectiveDerivedEquivAlternatingSix :
    commutator (Sp (ZMod 2) ⧸ Subgroup.center (Sp (ZMod 2))) ≃*
      alternatingGroup (Fin 6) := by
  refine (projectiveEquivSymmetricSix.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr projectiveEquivSymmetricSix.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

end Theory.SpecificGroups.SymplecticFour.Binary
