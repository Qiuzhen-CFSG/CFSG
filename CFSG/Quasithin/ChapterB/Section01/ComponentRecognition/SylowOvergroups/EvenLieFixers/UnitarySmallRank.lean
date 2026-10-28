module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Transport
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.SU3.SylowPointwiseInner.Full
public import Theory.SpecificGroups.ClassicalUnitary.SylowPointwiseInner.Reduction

/-!
# Full PSU₂ and PSU₃ Sylow fixers in B.1.13

The concrete carrier calculations control every pointwise-fixing automorphism,
without an involution or two-power-order assumption. The actual `IsPSU` witness
transports the whole fixer. The final applications use the component's literal
central quotient and conjugation action to discharge the characteristic-two
Sylow-centralizer premise in B.1.13, printed pp.73–74.

The PSU₃ simplicity hypothesis is supplied by the source component. Its matrix
field has order (2^f)², and the Hermitian form remains arbitrary. These are the
dimension-two and dimension-three branches; higher dimensions remain separate.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
variable {X G : Type*} [Group X] [Group G]

/-- Every binary PSU₂ model has a two-group pointwise automorphism fixer. -/
theorem unitaryTwo_model_fixer [Finite X] {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSU X 2 (2 ^ f)) : SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv X e.toEquiv
  apply fixer_of_equiv e
  exact fixer_twoGroup_of_inner
    (Theory.SpecificGroups.ClassicalUnitary.SylowPointwiseInner.fixing_sylow_two J hf hF hconj)

/-- The full PSU₃ fixer bound, with simplicity inherited through the actual model. -/
theorem unitaryThree_model_fixer [Finite X] [IsSimpleGroup X]
    {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU X 3 (2 ^ f)) : SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, J, hF, hconj, ⟨e⟩⟩ := hmodel
  let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_equiv X e.toEquiv
  let : IsSimpleGroup (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
    e.symm.isSimpleGroup
  apply fixer_of_equiv e
  exact fixer_twoGroup_of_inner
    (BenderSuzuki.MatrixGroups.HermitianForm.SylowPointwiseInner.fixing_sylow_eq_mem_conj
      J hf hF hconj)

/-- PSU₂ discharges B.1.13's fixer premise on the literal central quotient. -/
theorem le_component_of_unitaryTwo_model [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G)) {f : ℕ} (hf : 0 < f)
    (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 2 (2 ^ f))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (unitaryTwo_model_fixer hf hmodel) hd

/-- PSU₃ discharges the same premise; no automorphism-order restriction remains. -/
theorem le_component_of_unitaryThree_model [Finite G]
    (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hKN : K ≤ normalizer (L : Set G)) {f : ℕ} (hf : 2 ≤ f)
    (hmodel : ClassicalGroup.IsPSU (L ⧸ center L) 3 (2 ^ f))
    (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥) : K ≤ L := by
  let : IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  exact le_component_of_quotient_model K L T hL hLK hkind hKN (MulEquiv.refl _)
    (unitaryThree_model_fixer hf hmodel) hd

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
