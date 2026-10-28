module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieFixers.Transport
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.SmallModels
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.PointwiseFixer
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SylowPointwiseInner
public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.SylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.InnerFieldCoverage
public import Theory.AtlasPort.LinearGroups.G2.EvenInvolutionGeometry.BinarySylowFixers
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.SpecificGroups.Tits.SylowPointwiseInner

/-!
# Complete small-rank family calculations for the B.1.13 fixer

The root-coordinate and polar-geometry automorphism theorems identify the
whole pointwise fixer with inner automorphisms induced by the Sylow subgroup.
This gives a two-group, with no hypothesis on individual automorphism orders.
The semilinear coverage premises for Sp₄ and G₂ are discharged here using
their proved producers. Suzuki is transported from its marked root Sylow.
The binary G₂ derived group and Tits group use their actual derived and
Parrott carriers. These are proved branches of the full characteristic-two
problem, not an assertion that the small-rank list exhausts that problem.

The final applications discharge precisely the Sylow-fixer premise in the
literal conjugation-action reduction for B.1.13, printed pp.73–74 of
`refs/quasithin.pdf`. Model proofs retain their source and ATLAS license
attribution in the imported modules.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers

variable {G : Type*} [Group G]

/-- Binary PSL₃, including both q = 2 and q = 4, has a two-group fixer. -/
theorem linearThree_fixer (F : Type*) [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f) :
    SylowFixerIsTwoGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) := by
  apply fixer_twoGroup_of_inner
  intro S a ha
  obtain ⟨z, ⟨y, hy, rfl⟩, he⟩ :=
    Matrix.PSL3.LinearThree.exists_sylow_center_conj_of_equiv F hf hF
      (MulEquiv.refl _) S a ha
  exact ⟨y, y.property, he⟩

/-- The nonbinary four-dimensional symplectic calculation has no remaining
diagram-preserving automorphism classification premise. -/
theorem symplecticFour_fixer (F : Type*) [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f) :
    SylowFixerIsTwoGroup (Matrix.symplecticGroup (Fin 2) F) := by
  apply fixer_twoGroup_of_inner
  exact Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.aut_fixing_sylow_inner
    hF hf Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.SemilinearClassification.inner_field_of_preservesDiagram

/-- Projectivization uses the proved characteristic-two trivial-center equivalence. -/
theorem projectiveSymplecticFour_fixer (F : Type*) [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f) :
    SylowFixerIsTwoGroup (ClassicalGroup.PSp 2 F) :=
  fixer_of_equiv Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    (symplecticFour_fixer F hf hF)

/-- Every Suzuki parameter in the simple range is covered, at every Sylow subgroup. -/
theorem suzuki_fixer (m : ℕ) (hm : 1 ≤ m) :
    SylowFixerIsTwoGroup (BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) := by
  obtain ⟨P, hP⟩ := BenderSuzuki.MatrixGroups.suzukiRootSubgroup_isSylow m (by omega)
  apply fixer_twoGroup_of_inner
  intro S a ha
  apply MulAut.fixing_inner_sylow P S _ a ha
  intro b hb
  change ∀ x ∈ (P : Subgroup _), b x = x at hb
  change ∃ x ∈ (P : Subgroup _), b = MulAut.conj x
  rw [hP] at hb ⊢
  exact BenderSuzuki.ZD.BaseAutomorphisms.suzuki_aut_fixing_root_inner m hm b hb

/-- The full even G₂ range q > 2, with inner-field coverage discharged. -/
theorem g2_fixer (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) : SylowFixerIsTwoGroup (Atlas.G2.Model F) :=
  fixer_twoGroup_of_inner (Atlas.G2.EvenInvolutionGeometry.fixing_sylow_inner
    (Atlas.G2.LieAutomorphismExtensions.semilinearAction_surjective hF))

/-- The binary exception uses G₂(2)′, with its full automorphism action proved. -/
theorem g2Derived_fixer :
    SylowFixerIsTwoGroup (commutator (Atlas.G2.Model (ZMod 2))) :=
  fixer_twoGroup_of_inner (Atlas.G2.EvenInvolutionGeometry.binary_fixing_sylow_inner
    Atlas.G2.LieAutomorphismExtensions.binaryConjugation_bijective)

/-- The Tits endpoint uses the certified Parrott carrier, rather than full ²F₄(2). -/
theorem tits_fixer : SylowFixerIsTwoGroup Tits.ParrottGroup :=
  fixer_twoGroup_of_inner Tits.SylowPointwiseInner.parrott_fixing_sylow_inner

/-- The literal classical PSL₂ interface transports the already proved rank-one result. -/
theorem linearTwo_model_fixer {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hmodel : ClassicalGroup.IsPSL X 2 (2 ^ f)) :
    SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact fixer_of_equiv e linearTwo_fixer

/-- The literal classical PSL₃ interface, with every positive binary exponent. -/
theorem linearThree_model_fixer {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 0 < f) (hmodel : ClassicalGroup.IsPSL X 3 (2 ^ f)) :
    SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact fixer_of_equiv e (linearThree_fixer F hf hF)

/-- The literal projective symplectic interface for every nonbinary field. -/
theorem symplecticFour_model_fixer {X : Type*} [Group X] [Finite X]
    {f : ℕ} (hf : 1 < f) (hmodel : ClassicalGroup.IsPSp X 2 (2 ^ f)) :
    SylowFixerIsTwoGroup X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  let := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  exact fixer_of_equiv e (projectiveSymplecticFour_fixer F hf hF)

section Applications
variable [Finite G] (K L : Subgroup G) (T : Sylow 2 G)
  (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
  (hkind : IsQuasisimple K ∨ Nat.card K = 3)
  (hKN : K ≤ normalizer (L : Set G))
  (hd : K ≤ L ∨ ⁅K, L ⊓ (K ⊔ (T : Subgroup G))⁆ = ⊥)

include hL hLK hkind hKN hd

/-- The PSL₃ branch of the actual B.1.13 containment argument. -/
theorem linearThree_le_component (F : Type*) [Field F] [Finite F]
    {f : ℕ} (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ⧸ center L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e
    (linearThree_fixer F hf hF) hd

/-- The nonbinary PSp₄ branch, retaining the literal component central quotient. -/
theorem symplecticFour_le_component (F : Type*) [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (e : L ⧸ center L ≃* ClassicalGroup.PSp 2 F) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e
    (projectiveSymplecticFour_fixer F hf hF) hd

/-- The Suzuki branch of the actual B.1.13 containment argument. -/
theorem suzuki_le_component (m : ℕ) (hm : 1 ≤ m)
    (e : L ⧸ center L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e (suzuki_fixer m hm) hd

/-- The G₂(q), q > 2 branch of the actual B.1.13 containment argument. -/
theorem g2_le_component (F : Type*) [Field F] [Finite F] [CharP F 2]
    (hF : 2 < Nat.card F) (e : L ⧸ center L ≃* Atlas.G2.Model F) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e (g2_fixer F hF) hd

/-- The G₂(2)′ branch of the actual B.1.13 containment argument. -/
theorem g2Derived_le_component
    (e : L ⧸ center L ≃* commutator (Atlas.G2.Model (ZMod 2))) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e g2Derived_fixer hd

/-- The Tits branch of the actual B.1.13 containment argument. -/
theorem tits_le_component (e : L ⧸ center L ≃* Tits.ParrottGroup) : K ≤ L :=
  le_component_of_quotient_model K L T hL hLK hkind hKN e tits_fixer hd

end Applications
end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups.EvenLieFixers
