module
public import Theory.Representation.BinaryOffender.CubicCenterChief
public import Theory.Representation.Mathieu.M22James.Classification

/-!
# Minimum binary degree of a faithful triple-Mathieu action

Faithfulness detects the cubic center on a chief factor. Quasisimplicity
then makes the action on that factor faithful. James's irreducible minimum
degree bounds the factor by twelve, hence also bounds the entire original
module, without an irreducibility assumption on that module.

Source: Aschbacher–Smith H.12.1(1), printed pp.393–394, and the faithful
chief-factor argument of 13.5.21, printed p.924; refs/quasithin.pdf.
-/

public noncomputable section
namespace Sporadic.Mathieu.M22TripleCover
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
variable {D W : Type*} [Group D] [Finite D] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

/-- Every faithful finite binary action of the genuine triple cover has
dimension at least twelve, including reducible actions. -/
theorem faithful_finrank_ge_twelve (e : D ≃* M22TripleCover)
    (ρ : Representation (ZMod 2) D W) (hf : Function.Injective ρ) :
    12 ≤ Module.finrank (ZMod 2) W := by
  let : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  let : IsQuasisimple D := IsQuasisimple.of_mulEquiv e.symm
  let : IsQuasisimple (⊤ : Subgroup D) := IsQuasisimple.of_mulEquiv topEquiv.symm
  have hc : Nat.card (center (⊤ : Subgroup D)) = 3 :=
    (Nat.card_congr (centerCongr (topEquiv.trans e)).toEquiv).trans center_card
  obtain ⟨U,N,hi,hinj⟩ := exists_faithful_chief_of_cubic_center ρ ⊤ hf hc
  let τ := sectionRepresentation ρ U N
  let := hi
  have ht : Function.Injective τ := by
    intro x y hxy
    exact congrArg Subtype.val (hinj (show
      (τ.comp (⊤ : Subgroup D).subtype) ⟨x,mem_top x⟩ =
      (τ.comp (⊤ : Subgroup D).subtype) ⟨y,mem_top y⟩ from hxy))
  exact (faithful_irreducible_finrank_ge_twelve_of_equiv e τ ht).trans
    ((Submodule.finrank_quotient_le _).trans (Submodule.finrank_le N.toSubmodule))
end Sporadic.Mathieu.M22TripleCover
