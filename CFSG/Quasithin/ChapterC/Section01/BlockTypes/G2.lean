module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.Representation.G2Natural
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Natural G₂(2) blocks (C.1.30)

The quotient actor is the actual commutator subgroup of the split-octonion
G₂ model over F₂. Its natural space is the trace-zero octonions modulo the
scalar identity line. The previously constructed representation has dimension
six; here it supplies the concrete block model and literal conjugation formulas.
In particular G₂(2) and G₂(2)′ are kept distinct.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, Definition C.1.30, printed p.135.
-/

@[expose] public section

open Atlas.G2.Natural
namespace CFSG.Quasithin.ChapterC

/-- The derived octonion action on the multiplicative additive natural space. -/
def g2TwoNaturalAction : commutator (Atlas.G2.Model (ZMod 2)) →*
    MulAut (Multiplicative (Space (ZMod 2))) where
  toFun g := (LinearMap.GeneralLinearGroup.toLinearEquiv
    ((derivedAction (ZMod 2)).asGroupHom g)).toAddEquiv.toMultiplicative
  map_one' := by
    ext v
    exact LinearMap.congr_fun (map_one (derivedAction (ZMod 2))) v.toAdd
  map_mul' g j := by
    ext v
    exact LinearMap.congr_fun (map_mul (derivedAction (ZMod 2)) g j) v.toAdd

@[simp] theorem g2TwoNaturalAction_apply (g : commutator (Atlas.G2.Model (ZMod 2)))
    (v : Multiplicative (Space (ZMod 2))) :
    (g2TwoNaturalAction g v).toAdd = derivedAction (ZMod 2) g v.toAdd := rfl

/-- The intrinsic type of a G₂(2)-block: the actor is G₂(2)′ and the module
is its genuine six-dimensional natural quotient. Ambient subnormality is
supplied by `IsBlockOfType`, as for the other named block types. -/
def IsG2TwoBlock (L : Type*) [Group L] : Prop :=
  IsShort L ∧ IsLinearBlockModel L (Representation.g2DerivedNatural (ZMod 2))

variable {L : Type*} [Group L]

theorem IsG2TwoBlock.short (h : IsG2TwoBlock L) : IsShort L := h.1

/-- The model can be chosen with exactly the canonical natural action. -/
theorem IsG2TwoBlock.natural_model (h : IsG2TwoBlock L) :
    Nonempty (BlockModuleModel L g2TwoNaturalAction) := by
  obtain ⟨_, rho, hm, he⟩ := h
  have hr : rho = g2TwoNaturalAction := by
    ext g v
    exact he g v
  rwa [hr] at hm

/-- Construct this type from a short group and its concrete equivariant model. -/
theorem IsG2TwoBlock.of_model (hshort : IsShort L)
    (hmodel : Nonempty (BlockModuleModel L g2TwoNaturalAction)) : IsG2TwoBlock L :=
  ⟨hshort, g2TwoNaturalAction, hmodel, fun _ _ => rfl⟩

/-- The quotient is the derived group, with no full-group substitution. -/
theorem IsG2TwoBlock.quotient_iso (h : IsG2TwoBlock L) :
    Nonempty ((L ⧸ pCore 2 L) ≃* commutator (Atlas.G2.Model (ZMod 2))) :=
  h.2.quotient_iso

/-- The natural quotient has binary dimension six. -/
theorem IsG2TwoBlock.module_card (h : IsG2TwoBlock L) :
    Nat.card (BlockModule L) = 2 ^ 6 := by
  rw [h.2.module_card, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod, finrank_space]

/-- The module identification intertwines the original conjugation action. -/
theorem BlockModuleModel.g2_intertwining (model : BlockModuleModel L g2TwoNaturalAction)
    (l : L) (v : blockU L) :
    (model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l v))).toAdd =
      derivedAction (ZMod 2) (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l))
        (model.moduleIso (QuotientGroup.mk' (blockFixed L) v)).toAdd :=
  congrArg Multiplicative.toAdd (model.intertwining l v)

/-- On an octonion representative, conjugation is the literal octonion action
followed by the trace-zero scalar quotient map. -/
theorem BlockModuleModel.g2_intertwining_mk (model : BlockModuleModel L g2TwoNaturalAction)
    (l : L) (v : blockU L) (x : TraceZero (ZMod 2))
    (hx : (model.moduleIso (QuotientGroup.mk' (blockFixed L) v)).toAdd = Atlas.G2.Natural.mk (ZMod 2) x) :
    (model.moduleIso (QuotientGroup.mk' (blockFixed L) (blockConjugate L l v))).toAdd =
      Atlas.G2.Natural.mk (ZMod 2) (traceZeroAction (ZMod 2)
        (model.quotientIso (QuotientGroup.mk' (pCore 2 L) l)).val x) := by
  rw [model.g2_intertwining, hx, derivedAction_mk]

end CFSG.Quasithin.ChapterC

