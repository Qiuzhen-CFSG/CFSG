module

public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL2.PrimeNormalExtension
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import GorensteinWalter.LinearRingEquiv

/-!
# The proper prime-field component extension in F.6.18

If the generalized Fitting subgroup is a proper PSL₂(p), its trivial center
and generalized Fitting self-centralization make ambient conjugation faithful.
The actual prime-field automorphism realization then identifies the ambient
group with PGL₂(p). The marked form retains the original component embedding;
the source consumer also handles the literal two-residual as that component.

Source: Aschbacher--Smith, F.6.18, printed p.310, row (5). Prime and Sylow
sieves supply the source parameter restrictions separately.
-/

@[expose] public section
noncomputable section

open Subgroup Theory.GroupTheory GorensteinWalter
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly

variable {G : Type*} [Group G] [Finite G]

/-- The marked PGL₂ recognition preserves the original PSL₂ component map. -/
theorem marked_pgl_prime_of_proper_psl_generalizedFitting
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hproper : K ≠ ⊤) (F : Type) [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (hF : Nat.card F = p)
    (eK : K ≃* PSL(2, F)) :
    ∃ eG : G ≃* PGL2 F, ∀ k : K,
      eG k = Matrix.ProjectiveSpecialLinearGroup.toPGL (eK k) := by
  have hZ : center K = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz := (Subgroup.centerCongr eK ⟨x, hx⟩).property
    change eK x ∈ center PSL(2, F) at hz
    rw [psl2_center_eq_bot F, mem_bot] at hz
    exact eK.injective (hz.trans (map_one eK).symm)
  have hcentral : centralizer (K : Set G) ≤ K := by
    simpa only [hFstar] using centralizer_generalizedFitting_le G
  have hC : centralizer (K : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hz : (⟨x, hcentral hx⟩ : K) ∈ center K := by
      rw [mem_center_iff]
      intro y
      exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
    rw [hZ, mem_bot] at hz
    exact congrArg Subtype.val hz
  exact Theory.PSL2.exists_pgl_equiv_of_proper_normal_prime_psl K hC hproper F hp hF eK

/-- The field-independent source predicate yields the concrete prime-field
PGL₂ carrier, without an extra automorphism-coverage premise. -/
theorem pgl_prime_of_proper_psl_generalizedFitting
    (K : Subgroup G) [K.Normal] (hFstar : generalizedFitting G = K)
    (hproper : K ≠ ⊤) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hmodel : ClassicalGroup.IsPSL K 2 p) :
    Nonempty (G ≃* PGL2 (ZMod p)) := by
  obtain ⟨F, _, _, hF, ⟨eK⟩⟩ := hmodel
  obtain ⟨eG, _⟩ := marked_pgl_prime_of_proper_psl_generalizedFitting
    K hFstar hproper F hp hF eK
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hF])
  exact ⟨eG.trans (pgl2RingEquiv eF)⟩

/-- Apply the recognition directly to the source's original two-residual. -/
theorem pgl_prime_of_proper_psl_twoResidual
    (hFstar : pResidual 2 G = generalizedFitting G)
    (hproper : pResidual 2 G ≠ ⊤) {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (hmodel : ClassicalGroup.IsPSL (pResidual 2 G) 2 p) :
    Nonempty (G ≃* PGL2 (ZMod p)) :=
  pgl_prime_of_proper_psl_generalizedFitting (pResidual 2 G) hFstar.symm hproper hp hmodel

end CFSG.Quasithin.ChapterF.SourceAssembly
