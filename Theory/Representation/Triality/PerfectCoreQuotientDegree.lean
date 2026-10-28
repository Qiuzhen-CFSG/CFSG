module
public import Theory.Representation.Triality.SevenPlaneDegree
public import Theory.Representation.QuadraticFourGroup.Recognition.IrreducibleReduction.Section
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.Quotient
public import Theory.GroupAction.PerfectFrattiniAction
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Frattini.PGroup

/-!
# Faithful triality sections of a perfect action with a two-core

A nontrivial binary representation of a finite perfect group with simple
binary-triality two-core quotient has a literal irreducible subquotient
carrying a faithful action of that quotient. The quotient marking and
its evaluation on every original group element are retained. The actual
seven-plane theorem forces dimension at least twenty-four, without any
splitting or irreducibility assumption on the original representation.

For a nontrivial action on a finite two-group, Burnside's automorphism
kernel detects the action on its Frattini quotient. Applying the same
section argument gives order at least 2^24 in that quotient. Simplicity
of the actor's quotient is an inherited hypothesis.

Source: the irreducible-section argument of GLS2, Theorem 25.14, Step 2;
Aschbacher--Smith G.9.3, printed p.356, and A.1.29, printed p.27.
The original retained-core application is LocalBinaryFaithfulSection in
the 5.1.13 local Cartan argument, printed pp.635--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace Triality.SevenPlaneDegree
variable {H V : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [IsSimpleGroup (H ⧸ pCore 2 H)]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- A literal irreducible subquotient carries the faithful simple quotient action. -/
theorem exists_faithful_core_quotient_section
    (e : (H ⧸ pCore 2 H) ≃* Standard.BinaryCarrier 1 Nat.zero_lt_one)
    (ρ : Representation (ZMod 2) H V) (hnt : ∃ h, ρ h ≠ 1) :
    ∃ U : Subrepresentation ρ, ∃ D : Subrepresentation U.toRepresentation,
      ∃ σ : Representation (ZMod 2) (Standard.BinaryCarrier 1 Nat.zero_lt_one)
        (U ⧸ D.toSubmodule),
      D.quotientRepresentation.IsIrreducible ∧ σ.IsIrreducible ∧
      Function.Injective σ ∧
      (∀ h, σ (e (QuotientGroup.mk' (pCore 2 H) h)) = D.quotientRepresentation h) ∧
      24 ≤ Module.finrank (ZMod 2) (U ⧸ D.toSubmodule) := by
  let : Group.IsPerfect (⊤ : Subgroup H) := Group.IsPerfect.ofSurjective
    (f := (topEquiv (G := H)).symm.toMonoidHom) (topEquiv (G := H)).symm.surjective
  have hn : ¬ (⊤ : Subgroup H) ≤ ρ.ker := by
    intro hh
    obtain ⟨g,hg⟩ := hnt
    exact hg (hh (mem_top g))
  obtain ⟨U,D,hi,hd⟩ := QuadraticFourGroup.exists_irreducible_section_surviving_perfect
    (ρ := ρ) (⊤ : Subgroup H) hn
  let := hi
  have hk : pCore 2 H ≤ D.quotientRepresentation.ker :=
    normal_p_subgroup_le_ker D.quotientRepresentation _ pCore_isPGroup
  let τ := quotientOfLEKer D.quotientRepresentation (pCore 2 H) hk
  have ht : Function.Injective τ := by
    apply τ.ker_eq_bot_iff.mp
    rcases (MonoidHom.normal_ker τ).eq_bot_or_eq_top with hb | hh
    · exact hb
    · apply (hd ?_).elim
      intro g _
      exact show QuotientGroup.mk' (pCore 2 H) g ∈ τ.ker from hh ▸ mem_top _
  let σ := τ.comp e.symm.toMonoidHom
  have hs : Representation.IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective τ).mpr
      ((quotientOfLEKer_irreducible_iff _ _ hk).mpr hi)
  have hσ : Function.Injective σ := ht.comp e.symm.injective
  refine ⟨U,D,σ,hi,hs,hσ,?_,finrank_ge σ hσ⟩
  intro g
  change τ (e.symm (e (QuotientGroup.mk' (pCore 2 H) g))) = _
  rw [e.symm_apply_apply]
  rfl

/-- The entire nontrivial representation is at least twenty-four dimensional. -/
theorem perfect_core_quotient_finrank_bound
    (e : (H ⧸ pCore 2 H) ≃* Standard.BinaryCarrier 1 Nat.zero_lt_one)
    (ρ : Representation (ZMod 2) H V) (hnt : ∃ h, ρ h ≠ 1) :
    24 ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨U,D,_,_,_,_,_,hd⟩ := exists_faithful_core_quotient_section e ρ hnt
  exact hd.trans ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le U.toSubmodule))

end Triality.SevenPlaneDegree

namespace MulAut
variable {H P : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    [Group P] [Finite P]

/-- The actual binary linear action underlying an action on an elementary two-group. -/
@[expose] def binaryRepresentation [IsElementaryAbelian 2 P] (a : H →* MulAut P) :
    Representation (ZMod 2) H (Additive P) where
  toFun h := (a h).toAdditive.toAddMonoidHom.toZModLinearMap 2
  map_one' := by ext; simp
  map_mul' := by intros; ext; simp

omit [Finite H] [Group.IsPerfect H] [Finite P] in
theorem binaryRepresentation_nontrivial [IsElementaryAbelian 2 P]
    (a : H →* MulAut P) (ha : a ≠ 1) : ∃ h, binaryRepresentation a h ≠ 1 := by
  by_contra! hh
  apply ha
  ext h p
  exact congrArg (fun f : Module.End (ZMod 2) (Additive P) => (f (Additive.ofMul p)).toMul) (hh h)

/-- A nontrivial perfect action above the genuine binary-triality quotient
requires at least twenty-four dimensions in the original Frattini layer. -/
theorem triality_frattini_card_ge
    [IsSimpleGroup (H ⧸ pCore 2 H)]
    (e : (H ⧸ pCore 2 H) ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one)
    (hP : IsPGroup 2 P) (a : H →* MulAut P) (ha : a ≠ 1) :
    2^24 ≤ Nat.card (P ⧸ frattini P) := by
  let : Fact (IsPGroup 2 P) := ⟨hP⟩
  let : IsElementaryAbelian 2 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini
  let d := (quotientAut (frattini P)).comp a
  have hd : d ≠ 1 := MonoidHom.frattini_comp_ne_one_of_isPerfect hP a ha
  have hl := Triality.SevenPlaneDegree.perfect_core_quotient_finrank_bound e
    (binaryRepresentation d) (binaryRepresentation_nontrivial d hd)
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (P ⧸ frattini P))
  change Nat.card (P ⧸ frattini P) = _ at hc
  rw [hc,Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hl
end MulAut
