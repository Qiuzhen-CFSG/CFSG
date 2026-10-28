module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition.FFPassage
public import Theory.Representation.BinaryOffender.QuadraticSection

/-!
# The whole-module or quotient hexacode section

F.9.18(6) supplies three alternatives for every nonzero moved invariant
subspace: it is the whole moved module, both sections are FF-modules, or
one section is a strong FF-module. `SectionInputs` retains all three clauses.
The fixed-codimension inequality also proves this input directly from the
quadratic-ratio bound supplied by the source geometry.

For the actual cubic cover, the primitive cubic polynomial passes to both
sections. The proved FF passage therefore excludes strong offenders on each
nonzero section, with faithfulness established before classification. A proper
quotient in the remaining FF case receives actual hexacode coordinates. If the
selected Irr⁺ member is the whole module, we transport its coordinates to the
literal quotient by zero. In both cases the actor, its component image and the
linear intertwiner are retained; dimension six is derived from the coordinates.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.9.18(6),
printed pp.325–326; B.4.2(8), B.4.5, pp.86–87; 13.8.21(2), p.956.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender Atlas.Codes
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
universe u v
variable {D : Type u} [Group D]
variable {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

/-- All three alternatives of F.9.18(6), for every nonzero moved invariant
subspace. In the reduced configuration K₀T = H, so all actors below are D. -/
structure SectionInputs (ρ : Representation (ZMod 2) D V) (L : Subgroup D) : Prop where
  alternatives : ∀ W : Subrepresentation ρ, W.toSubmodule ≠ ⊥ →
    subspaceCommutator ρ W.toSubmodule L = W.toSubmodule →
    W.toSubmodule = subspaceCommutator ρ ⊤ L ∨
      (IsFFModule W.toRepresentation ∧ IsFFModule W.quotientRepresentation) ∨
      (IsStrongFFModule W.toRepresentation ∨ IsStrongFFModule W.quotientRepresentation)

/-- The fixed-codimension inequality proves the section alternatives directly
from a quadratic subgroup of ratio at most two. No irreducibility is used. -/
theorem sectionInputs_of_small_ratio [Finite D] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    (hq : quadraticRatio ρ ≤ 2) : SectionInputs ρ L := by
  obtain ⟨A, hA, _, hbound⟩ := (quadraticRatio_le_two_iff ρ).mp hq
  constructor
  intro W _ _
  have hsum := fixedCodim_quotient_add_subrepresentation_le ρ W A
  by_cases hsub : fixedCodim W.toRepresentation A < rank A
  · exact Or.inr (Or.inr (Or.inl ⟨A, hA, hsub⟩))
  by_cases hquot : fixedCodim W.quotientRepresentation A < rank A
  · exact Or.inr (Or.inr (Or.inr ⟨A, hA, hquot⟩))
  exact Or.inr (Or.inl ⟨⟨A, hA, by omega⟩, ⟨A, hA, by omega⟩⟩)

/-- Transport actual hexacode coordinates from a full subrepresentation to
the literal quotient of the ambient module by zero. The actor is unchanged. -/
noncomputable def HexacodeModel.quotientBotOfTop
    {ρ : Representation (ZMod 2) D V} {L : Subgroup D}
    (I : Subrepresentation ρ) (hI : I = ⊤) (m : HexacodeModel L I.toRepresentation) :
    HexacodeModel L (⊥ : Subrepresentation ρ).quotientRepresentation := by
  subst I
  let q : (V ⧸ (⊥ : Subrepresentation ρ).toSubmodule) ≃ₗ[ZMod 2] V :=
    Submodule.quotEquivOfEqBot _ rfl
  let t : V ≃ₗ[ZMod 2] (⊤ : Subrepresentation ρ).toSubmodule := Submodule.topEquiv.symm
  exact {
    actor := m.actor
    faithful := m.faithful
    component_image := m.component_image
    coordinates := (q.trans t).trans m.coordinates
    intertwines := by
      intro g v
      induction v using Submodule.Quotient.induction_on with
      | H v => exact m.intertwines g (t v) }

/-- The complete F.9.18(6) case split. Cubic faithfulness and the proved
reducible FF passage exclude strong offenders on both nonzero sections.
The output is a proper denominator with actual quotient coordinates. -/
theorem exists_hexacode_quotient [Finite D] [FiniteDimensional (ZMod 2) V]
    [Nontrivial V] (ρ : Representation (ZMod 2) D V) (L : Subgroup D) [L.Normal]
    (eL : L ≃* HexEvenAutomorphisms) (inputs : IrreducibleInputs.{u,v} L)
    (z : D) (hzorder : orderOf z = 3)
    (hzcenter : zpowers z = (center L).map L.subtype)
    (hcent : centralizer (L : Set D) ≤ L) (hpoly : CubicPolynomial ρ z)
    (hgen : subspaceCommutator ρ ⊤ L = ⊤) (sections : SectionInputs ρ L)
    (I : Subrepresentation ρ) (hI : IsIrrPlus ρ L I.toSubmodule)
    (m : HexacodeModel L I.toRepresentation) :
    ∃ W : Subrepresentation ρ, W ≠ ⊤ ∧
      (W = ⊥ ∨ (IsIrrPlus ρ L W.toSubmodule ∧
        Module.finrank (ZMod 2) W.toSubmodule = 6)) ∧
      Nonempty (HexacodeModel L W.quotientRepresentation) := by
  by_cases htop : I = ⊤
  · refine ⟨⊥, ?_, Or.inl rfl, ⟨m.quotientBotOfTop I htop⟩⟩
    intro he
    have hh : (⊥ : Submodule (ZMod 2) V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule he
    exact bot_ne_top hh
  let : Nontrivial I.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr (hI.ne_bot ρ)
  let : Nontrivial (V ⧸ I.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr
    (fun he => htop (Subrepresentation.toSubmodule_injective he))
  have hsub := FFPassage.passage I.toRepresentation L eL inputs z hzorder hzcenter
    hcent (hpoly.subrepresentation I)
  have hquot := FFPassage.passage I.quotientRepresentation L eL inputs z hzorder hzcenter
    hcent (hpoly.quotient I)
  have hFF : IsFFModule I.quotientRepresentation := by
    rcases sections.alternatives I (hI.ne_bot ρ) hI.choose_spec.1 with he | hb | hc
    · exact (htop (Subrepresentation.toSubmodule_injective (he.trans hgen))).elim
    · exact hb.2
    · exact (hc.elim hsub.1 hquot.1).elim
  exact ⟨I, htop, Or.inr ⟨hI, m.finrank⟩, (hquot.2 hFF).2.1⟩

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.ModuleRecognition
