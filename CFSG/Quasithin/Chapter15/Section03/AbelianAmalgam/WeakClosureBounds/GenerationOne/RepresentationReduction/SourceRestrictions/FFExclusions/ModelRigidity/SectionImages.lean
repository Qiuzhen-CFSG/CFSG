module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Unitary

/-!
# Model rigidity for actual faithful section images

The parent's central-kernel theorem identifies the central simple quotient
of a nontrivial quasisimple action with that of its faithful image. Composing
with the specified model map transfers the concrete rigidity results without
removing a central kernel. The SL₃ and derived Sp₄ variants retain the
canonical projection and inclusion established in `CanonicalModels`.

Source: Aschbacher--Smith, the application of B.4.2 and B.5.1 to the
E.2.2 models in 15.3.65, printed p.1152.
-/

public section
open Subgroup Matrix Theory.GroupTheory Representation.BinaryOffender
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity

variable {D E V : Type*} [Group D] [Group E] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) [IsQuasisimple D]
    (hn : ¬ ∀ g v, ρ g v = v)
    {family : Family} {q : ℕ}

include hn

/-- A specified central quotient model gives the catalogue comparison for
the actual action image; the kernel is permitted to be nontrivial central. -/
theorem componentModel_actionImage_of_central_quotient_iff
    (e : D ⧸ center D ≃* E) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      ComponentModel E family q := by
  let a := (actionImageCentralQuotientEquiv ρ hn).symm.trans e
  exact ⟨fun h => h.transport a.symm, fun h => h.transport a⟩

variable {F : Type} [Field F] [Finite F] {f : ℕ}

/-- Rank-one field recovery on the faithful image, from the central simple model. -/
theorem pslTwo_actionImage_componentModel_iff
    (e : D ⧸ center D ≃* PSL(2,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearTwo ∧ q = 2 ^ f :=
  (componentModel_actionImage_of_central_quotient_iff ρ hn e).trans
    (pslTwo_componentModel_iff hf ho hF)

/-- Ternary linear field recovery on the faithful image, from the central simple model. -/
theorem pslThree_actionImage_componentModel_iff
    (e : D ⧸ center D ≃* PSL(3,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearThree ∧ q = 2 ^ f :=
  (componentModel_actionImage_of_central_quotient_iff ρ hn e).trans
    (pslThree_componentModel_iff hf ho hF)

/-- A specified SL₂ model uses its literal projective quotient. -/
theorem slTwo_actionImage_componentModel_iff (e : D ≃* SL(2,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearTwo ∧ q = 2 ^ f :=
  pslTwo_actionImage_componentModel_iff ρ hn (centralQuotientCongr e) hf ho hF

/-- A specified SL₃ model uses its literal projective quotient. -/
theorem slThree_actionImage_componentModel_iff (e : D ≃* SL(3,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearThree ∧ q = 2 ^ f :=
  pslThree_actionImage_componentModel_iff ρ hn (centralQuotientCongr e) hf ho hF

/-- The projective rank-one model in the actual E.2.2 Borel pair gives the
same comparison, using the inverse of the characteristic-two scalar projection. -/
theorem pslTwoModel_actionImage_componentModel_iff (e : D ≃* PSL(2,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearTwo ∧ q = 2 ^ f := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := MulEquiv.ofBijective (BenderSuzuki.Converse.pi F)
    ⟨BenderSuzuki.Converse.pi_injective, BenderSuzuki.Converse.pi_surjective⟩
  exact slTwo_actionImage_componentModel_iff ρ hn (e.trans a.symm) hf ho hF

/-- The projective ternary model in the E.2.2 Borel pair is compared through
the proved odd-exponent SL₃ projection, preserving the specified model map. -/
theorem pslThreeModel_actionImage_componentModel_iff (e : D ≃* PSL(3,F))
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .linearThree ∧ q = 2 ^ f :=
  slThree_actionImage_componentModel_iff ρ hn
    (e.trans (slThreeEquivProjective hF ho).symm) hf ho hF

/-- Symplectic field recovery retains the actual model's center quotient. -/
theorem spFour_actionImage_componentModel_iff
    (e : D ≃* Theory.SpecificGroups.SymplecticFour.Sp F)
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .symplecticFour ∧ q = 2 ^ f :=
  (componentModel_actionImage_iff ρ hn e family q).trans
    (spFour_componentModel_iff hf ho hF)

/-- E.2.2's literal derived symplectic model yields the same faithful-image result. -/
theorem spFourDerived_actionImage_componentModel_iff
    (e : D ≃* BorelReduction.SourceCases.Sp4Derived F)
    (hf : 1 < f) (ho : Odd f) (hF : Nat.card F = 2 ^ f) :
    ComponentModel (actionImage ρ ⧸ center (actionImage ρ)) family q ↔
      family = .symplecticFour ∧ q = 2 ^ f :=
  (componentModel_actionImage_iff ρ hn e family q).trans
    (spFourDerived_componentModel_iff hf ho hF)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity
