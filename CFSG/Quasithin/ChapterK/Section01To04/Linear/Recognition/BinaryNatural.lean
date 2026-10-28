module

public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Source
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Source
public import Theory.Representation.BinaryFullLinearRecognition

/-!
# Source natural recognition for binary linear groups

A faithful representation of SL_n(2) in dimension n gives the actual natural
intertwiner by equality of finite orders. Every binary linear operator is
semilinear with the identity coefficient automorphism. These two facts supply
the complete natural-module source input and its ratio, offender and generation
conclusions for the degree-four and degree-five branches of B.4.2.

Source: Aschbacher–Smith K.3.2.1 and B.4.2(9).
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryNatural
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

theorem sourceInput_of_finrank (h : ChapterK.RankOne.SourceHypotheses ρ L) (n : ℕ) (hn : n=4 ∨ n=5)
    (e : L ≃* SL(n,ZMod 2)) (hd : Module.finrank (ZMod 2) V = n) :
    Nonempty (ChapterK.Linear.Natural.SourceInput ρ L BinaryField.two n KnownSimple.IsKnownSimple) := by
  obtain ⟨j,f,hf⟩ := BinaryFullLinearRecognition.exists_natural_equiv
    (ρ.comp L.subtype) (h.faithful.comp L.subtype_injective) e hd
  let a : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n) := {
    groupEquiv := j
    linearEquiv := f
    intertwines := hf }
  refine ⟨⟨h.sqtk,h.fitting.symm,h.quasisimple,h.faithful,h.irreducible,h.smallCubic,
    Or.inr ⟨hn,rfl⟩,a,?_⟩⟩
  change ∀ g : G, ∃ τ : ZMod 2 ≃+* ZMod 2, ∀ (c : ZMod 2) (v : V),
    f (ρ g (f.symm (c • f v))) = τ c • f (ρ g v)
  intro g
  refine ⟨RingEquiv.refl _,?_⟩
  intro c v
  simp only [map_smul, LinearEquiv.symm_apply_apply, RingEquiv.refl_apply]

/-- Literal B.4.2 natural row with all recognition and scalar premises discharged. -/
theorem actionCase_of_finrank (h : ChapterK.RankOne.SourceHypotheses ρ L)
    (n : ℕ) (hn : n = 4 ∨ n = 5) (e : L ≃* SL(n,ZMod 2))
    (hd : Module.finrank (ZMod 2) V = n) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨s⟩ := sourceInput_of_finrank h n hn e hd
  exact (Natural.source_natural ρ L BinaryField.two n s).2.2.2

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryNatural
