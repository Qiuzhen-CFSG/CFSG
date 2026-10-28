module

public import CFSG.Quasithin.Chapter15.Section03.Constructions
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.Extraspecial
public import Theory.Representation.BinaryOffender.Defs

/-!
# Actual sections used in the extraspecial-quotient elimination

The actor is the literal quotient `H/O₂(H)`. Its representations below are
on the literal additive group of `U/Z`; the representative formula pins them
to ambient conjugation. For the two applications take `U = ⟨Z_S^H⟩` and
either the central line `Z` or `C_U(O₂(H))` as the denominator.

F.9.12 centralizers are expressed using `commutatorPreimage`, which is the
largest subgroup satisfying the stated commutator containment. Its existing
normalizer hypothesis and quotient-centralizer theorem justify this convention;
no ambient normality of `Z` is imposed.

These are shared definitions and honest action inputs. The action on `U/Z`
comes from 15.3.48, and that on `U/C_U(O₂(H))` from 15.3.49(a) and the following
faithfulness argument. This file proves neither source result and does not
postulate component reduction, an offender, or an exclusion.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.12,
printed p.322, and 15.3.48–49, printed pp.1141–1145.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination

open Subgroup
open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- `Q_H`, formed inside `H` and then embedded in the ambient group. -/
noncomputable def localTwoCore (H : Subgroup G) : Subgroup G :=
  (pCore 2 H).map H.subtype

/-- The source's star image, with the intersection with `H` explicit. -/
def starImage (H A : Subgroup G) : Subgroup (H ⧸ pCore 2 H) :=
  (A.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))

/-- `U_C = C_{U_H}(Q_H)`. -/
noncomputable def centralizerLayer (H U : Subgroup G) : Subgroup G :=
  U ⊓ centralizer (localTwoCore H : Set G)

/-- The two kernels `D_H` and `E_H` in F.9.12 are obtained by taking
`X = U_H` and `X = V_H` respectively. Reversing the arguments gives the
kernels at the other endpoint. -/
abbrev sectionCentralizer (X U Z : Subgroup G) : Subgroup G :=
  commutatorPreimage X U Z

/-- A faithful action on the actual elementary abelian section. The formula
on quotient representatives specifies conjugation, so an unrelated faithful
representation cannot serve as this input. -/
structure SectionAction (H U Z : Subgroup G) [IsElementaryAbelian 2 U] where
  layer_le : Z ≤ U
  normalizes : H ≤ normalizer (U : Set G)
  normalizes_layer : H ≤ normalizer (Z : Set G)
  representation : Representation (ZMod 2) (H ⧸ pCore 2 H)
    (Additive (U ⧸ Z.subgroupOf U))
  on_representatives : ∀ (h : H) (u : U),
    representation (QuotientGroup.mk' (pCore 2 H) h)
      (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U) u)) =
    Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf U)
      ⟨(h : G) * (u : G) * (h : G)⁻¹,
        le_normalizer_iff.mp normalizes h h.property u u.property⟩)
  faithful : Function.Injective representation

/-- The actual excluded odd quotient, including its order and exponent.
No arbitrary group-family tag is used. -/
def ExtraspecialOddQuotient (Y : Subgroup G) : Prop :=
  IsExtraspecial 3 (Y ⧸ pCore 2 Y) ∧
    Nat.card (Y ⧸ pCore 2 Y) = 27 ∧ Monoid.exponent (Y ⧸ pCore 2 Y) = 3

end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
