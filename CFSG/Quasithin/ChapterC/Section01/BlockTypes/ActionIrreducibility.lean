module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.Conjugation
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# Irreducibility of an action marked by a short group

The quotient coordinates of a block model give an action equivalence with
conjugation on U/C_U(K). The invariant-subgroup interval in C.1.7 therefore
makes the marked binary representation irreducible. This applies in particular
to the literal star moved section, without assuming that U itself is irreducible.
Source: Aschbacher–Smith C.1.7, printed p.123.
-/
public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC
open ExceptionalRestrictions ChapterB.QuasisimpleSource
variable {K A V : Type*} [Group K] [Group A] [AddCommGroup V] [Module (ZMod 2) V]

/-- A marked model of the actual block quotient inherits C.1.7 irreducibility. -/
theorem IsLinearBlockModel.action_irreducible
    {σ : Representation (ZMod 2) A V} (h : IsShort K)
    (m : IsLinearBlockModel K σ) : IsIrreducible σ := by
  let := h.elementary
  let : IsElementaryAbelian 2 (BlockModule K) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' (blockFixed K))
      (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,⟨m⟩,hρ⟩ := m
  let e : Additive (BlockModule K) ≃ₗ[ZMod 2] V :=
    (m.moduleIso.toAdditive.trans (AddEquiv.additiveMultiplicative V)).toLinearEquiv
      (ZMod.map_smul _)
  let E : ActionEquiv (moduleRepresentation h) σ :=
    ⟨m.quotientIso,e,by
      intro g v
      obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) g
      obtain ⟨u,hu⟩ := QuotientGroup.mk'_surjective (blockFixed K) v.toMul
      have hv : v = Additive.ofMul (QuotientGroup.mk' (blockFixed K) u) :=
        Additive.toMul.injective hu.symm
      rw [hv]
      have he := h.exists_quotient_moduleAction.choose_spec g u
      change (m.moduleIso (h.exists_quotient_moduleAction.choose _
        (QuotientGroup.mk' (blockFixed K) u))).toAdd = _
      rw [he]
      exact (congrArg Multiplicative.toAdd (m.intertwining g u)).trans (hρ _ _)⟩
  exact ExtensionConsequences.irreducible_of_equiv (ExtensionConsequences.actionSymm E)
    (moduleRepresentation_irreducible h)
end CFSG.Quasithin.ChapterC
