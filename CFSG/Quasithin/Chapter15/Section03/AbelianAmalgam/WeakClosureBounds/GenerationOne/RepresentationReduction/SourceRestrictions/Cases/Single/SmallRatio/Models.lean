module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.ClassificationInputs
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Ratios
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.FFExclusions.ModelRigidity.Unitary
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.ModuleIdentifications

/-!
# Connected source models and natural constituent witnesses

The five single-component E.2.2 models are marked by actual group
isomorphisms, with the fixed-field exponent distinguished from the unitary
matrix-field exponent. Comparison with the complete B.4.2 catalogue recovers
the defining field as well as the possible natural family. The conclusion
retains both maps in each action equivalence, for later central-quotient and
Borel transport. Centerlessness is an explicit intermediate premise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.2.2,
B.4.2--5 (printed pp.86--87), and the deduction on printed p.1152.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory Matrix
open BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
open FFExclusions.ModelRigidity

inductive SourceModel (S : Type*) [Group S] (f : ℕ) : Prop
  | linearTwo (F : Type) [Field F] [Finite F]
      (field : Nat.card F = 2 ^ f) (equiv : S ≃* PSL(2,F))
  | suzuki (m : ℕ) (positive : 0 < m) (degree : f = 2 * m + 1)
      (equiv : S ≃* SuzukiMatrixGroup m)
  | unitary (F : Type) [Field F] [Finite F] (J : HermitianForm 3 F)
      (field : Nat.card F = (2 ^ f) ^ 2)
      (conjugation : ∀ x, J.conj x = x ^ (2 ^ f))
      (equiv : S ≃* ProjectiveSpecialUnitaryMatrixGroup J)
  | linearThree (F : Type) [Field F] [Finite F]
      (field : Nat.card F = 2 ^ f) (equiv : S ≃* PSL(3,F))
  | symplecticFour (F : Type) [Field F] [Finite F]
      (field : Nat.card F = 2 ^ f) (equiv : S ≃* BorelReduction.SourceCases.Sp4Derived F)

def centerQuotientEquiv {S : Type*} [Group S] (hz : center S = ⊥) :
    S ⧸ center S ≃* S :=
  (QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot

theorem centerless_of_equiv {S R : Type*} [Group S] [Group R]
    (hz : center S = ⊥) (e : S ≃* R) : center R = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  apply e.symm.injective
  have h := (centerCongr e.symm ⟨x, hx⟩).property
  change e.symm x ∈ center S at h
  simpa only [hz, mem_bot, map_one] using h

def symplecticProjectiveEquiv {F : Type} [Field F] [Finite F] {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f) :
    BorelReduction.SourceCases.Sp4Derived F ≃*
      Theory.SpecificGroups.SymplecticFour.Sp F ⧸ center (Theory.SpecificGroups.SymplecticFour.Sp F) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact (spFourDerivedEquiv hF hf).trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv

theorem SourceModel.componentModel {S : Type*} [Group S] {f : ℕ}
    (hs : SourceModel S f) (hf : 1 < f) (ho : Odd f)
    {family : Family} {q : ℕ} (h : ComponentModel S family q) :
    (family = .linearTwo ∨ family = .linearThree ∨ family = .symplecticFour) ∧ q = 2 ^ f := by
  cases hs with
  | linearTwo F hF e =>
    obtain ⟨ht, hq⟩ := pslTwo_componentModel hf ho hF (h.transport e.symm)
    exact ⟨Or.inl ht, hq⟩
  | suzuki m hm _ e => exact (not_componentModel_of_suzuki_equiv m hm e _ _ h).elim
  | unitary F J hF hc e =>
    exact (unitary_not_componentModel J hf ho hF hc (h.transport e.symm)).elim
  | linearThree F hF e =>
    obtain ⟨ht, hq⟩ := pslThree_componentModel hf ho hF (h.transport e.symm)
    exact ⟨Or.inr (Or.inl ht), hq⟩
  | symplecticFour F hF e =>
    obtain ⟨ht, hq⟩ := spFour_componentModel hf ho hF
      (h.transport (e.trans (symplecticProjectiveEquiv hf hF)).symm)
    exact ⟨Or.inr (Or.inr ht), hq⟩

universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]

inductive NaturalConstituent (ρ : Representation (ZMod 2) D V) (L : Subgroup D) (f : ℕ) : Prop
  | linearTwo (F : BinaryField) (field : Nat.card F.Carrier = 2 ^ f)
      (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 2))
  | suzuki (m : ℕ) (positive : 0 < m) (degree : f = 2 * m + 1)
      (field : Nat.card (BenderSuzuki.PFAppendixIII.BinaryGaloisField (2 * m + 1)) = 2 ^ f)
      (action : ActionEquiv (ρ.comp L.subtype)
        (CFSG.Quasithin.Chapter13.Section08.Components.Suzuki.natural m))
  | linearThree (F : BinaryField) (field : Nat.card F.Carrier = 2 ^ f)
      (action : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
  | symplecticFour (F : BinaryField) (field : Nat.card F.Carrier = 2 ^ f)
      (action : ActionEquiv (ρ.comp L.subtype) (binarySymplectic F))

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Single.SmallRatio
