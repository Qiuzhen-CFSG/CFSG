module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.Basic
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.Recognition
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.InterchangeLift
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.QuaternionFixed.ModelInterchange
public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.CommutatorGeometry

/-!
# The quaternion cubic fixed subgroup in J.2.3(7)

For the actual cubic subgroup `cubicSubgroup d B`, this module assembles the
source recognition of `Q ∩ C_G(B)`. The parabolic quotient calculation gives
its equality with `S ∩ C_G(B)`, order eight and central intersection of order
two. The full commutator calculation gives index eight centralizers in `S`.
The cubic-action contradiction in `QuaternionFixed.Basic` excludes the
abelian order-eight case. Finally, the two cyclic-four lifts supplied by the
nonabelian Suzuki factors are fed to the literal order-eight recognition in
`QuaternionFixed.Recognition`.

The original recognition interface below is retained for compatibility.
`QuaternionFixed.Numerics` derives all its numerical premises from the
preceding natural sections. `QuaternionFixed.CyclicLifts` constructs the first
order-four lift in the nonabelian Suzuki factor. `QuaternionFixed.InterchangeLift`
constructs the second from movement of the first fixed vector by an element of
the actual model normalizer. `QuaternionFixed.ModelInterchange` supplies this
movement using the checked outer and inner involutions on the Steinberg module.

`SingerChoice.cubicFixedQ_equiv_quaternion` applies this argument to any source
Singer choice, selecting a nonidentity element of its fixed four-group.
`cubicFixedQ_equiv_quaternion_of_full_commutator` also constructs the Singer
choice. Finally, `source_seven` discharges the full-commutator premise using
J.2.3(6). Its only additional inputs are Q ≤ K, R₁ = Q ⊔ S, and
O₂(L₁T) = R₁ from J.2.2(1), produced by `qt-j12-parabolic-structure`.
The owners `qt-j12-special-core` and `qt-j-01-02` retain their final discharge.

Source: Aschbacher–Smith, Lemma J.2.3(7), printed p.434 (PDF p.445), combined
manuscript of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.SpecialCore

variable {G : Type*} [Group G] [Finite G]

/-- The original conditional recognition interface for J.2.3(7).
The stronger `cubicFixedQ_equiv_quaternion_of_model_interchange` derives the
numerical and cyclic-four premises instead of taking them as inputs. -/
theorem cubicFixedQ_equiv_quaternion
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hfixed : cubicFixedQ d.toTypeRuSetup B =
      d.toTypeRuSetup.S ⊓ centralizer (cubicSubgroup d.toTypeRuSetup B : Set G))
    (hcard : Nat.card (cubicFixedQ d.toTypeRuSetup B) = 8)
    (hinter : Nat.card (cubicFixedQ d.toTypeRuSetup B ⊓ d.V : Subgroup G) = 2)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V)
    (hc : ∃ c : cubicFixedQ d.toTypeRuSetup B, orderOf c = 4)
    (hd : ∀ c : cubicFixedQ d.toTypeRuSetup B, orderOf c = 4 →
      ∃ e : cubicFixedQ d.toTypeRuSetup B, orderOf e = 4 ∧ e ∉ zpowers c) :
    Nonempty (cubicFixedQ d.toTypeRuSetup B ≃* QuaternionGroup 2) := by
  have hnoncomm : ¬ IsMulCommutative (cubicFixedQ d.toTypeRuSetup B) := by
    exact cubicFixedQ_not_commutative d B hfixed hcard hinter hfull
  obtain ⟨c, hc4⟩ := hc
  obtain ⟨e, he4, heout⟩ := hd c hc4
  exact QuaternionGroup.equiv_of_card_eight_two_cyclic_four hcard hnoncomm c e hc4 he4 heout

/-- J.2.3(7) for any specified Singer choice. The preceding full-commutator
conclusion is supplied by `qt-j123-commutator-geometry`; the numerical,
cyclic-four and model-interchange premises are all discharged. -/
theorem SingerChoice.cubicFixedQ_equiv_quaternion
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (c : SingerChoice d.toTypeRuSetup B)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V) :
    Nonempty (cubicFixedQ d.toTypeRuSetup B ≃* QuaternionGroup 2) := by
  let : Nontrivial (fixedCore d.toTypeRuSetup c.B7) :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      rw [c.fixedCore_card d.toTypeRuSetup B]
      decide)
  obtain ⟨s, hs⟩ := exists_ne (1 : fixedCore d.toTypeRuSetup c.B7)
  have hs1 : (s : G) ≠ 1 := fun h => hs (Subtype.ext h)
  exact cubicFixedQ_equiv_quaternion_of_model_interchange d B c hQK hfull
    s s.property hs1 (c.model_interchange d B hfull s s.property hs1)

/-- J.2.3(7) from Q ≤ K and J.2.3(6), with the B-invariant Singer subgroup
constructed internally. No choice, fixed lift or model premise remains. -/
theorem cubicFixedQ_equiv_quaternion_of_full_commutator
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hfull : ∀ t : d.toTypeRuSetup.S, (t : G) ∉ d.V →
      ⁅zpowers (t : G), d.toTypeRuSetup.S⁆ = d.V) :
    Nonempty (cubicFixedQ d.toTypeRuSetup B ≃* QuaternionGroup 2) := by
  obtain ⟨c⟩ := nonempty_singerChoice d.toTypeRuSetup B
  exact c.cubicFixedQ_equiv_quaternion d B hQK hfull

/-- The source J.2.3(7) implication from the preceding J.2.2(1) conclusions.
The result is an isomorphism of the literal ambient subgroup Q ∩ C_G(B).
The parabolic source owner supplies the three earlier conclusions; the
full-commutator and Singer arguments are applied here. -/
theorem source_seven
    (d : LocalSetup G) (B : Sylow 3 d.toTypeRuSetup.L₁)
    (hQK : d.toTypeRuSetup.Q ≤ d.toTypeRuSetup.K)
    (hprod : d.toTypeRuSetup.R₁ = d.toTypeRuSetup.Q ⊔ d.toTypeRuSetup.S)
    (hcore : (d.toTypeRuSetup.L₁ ⊔ (d.T : Subgroup G)).pCoreIn 2 =
      d.toTypeRuSetup.R₁) :
    Nonempty ((d.toTypeRuSetup.Q ⊓
      centralizer (cubicSubgroup d.toTypeRuSetup B : Set G) : Subgroup G) ≃*
        QuaternionGroup 2) :=
  cubicFixedQ_equiv_quaternion_of_full_commutator d B hQK
    (CommutatorGeometry.full_commutator d hprod hcore)

end CFSG.Quasithin.ChapterJ.SpecialCore
