module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.CommonField
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanOpposition

/-!
# Opposition and independent-root separation on the Ree source quotient

The common-field argument identifies the perpendicular root's Cartan kernel
with the inverted factor of its simple reflection. Together with the actual
panel fixed-kernel equality this forces the longest Weyl element to invert H.
Two distinct root reflections then separate H, since their product has a power
equal to opposition. Finally, the eighth power of any actual simple-lift
product lies in H and is fixed by opposition; oddness makes it trivial.

These are source calculations on the same Q, not native Ree-model equations.
They include m=0. Natural rank-one markings and odd linear degree remain the
preceding inputs of CommonField; the remaining (6H) and section-10 source
construction are still required in this theorem family.

Source: Fong--Seitz I (1973), proof of (6H)(a), printed p.51 (independent-root
separation), and II (1974), end of section 10, p.232 (literal Weyl relation).
-/

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure (rootAt)
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}
variable (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (Endpoint Q 0 ⧸ panelKernel Q 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (quotientBorel Q 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (Endpoint Q 1 ⧸ panelKernel Q 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (quotientBorel Q 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i) (hcore : Q.tits.B.normalCore = ⊥)

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The actual longest Weyl element inverts the whole source Cartan. -/
theorem ree_longestCartanAction_inversion :
    ∀ h, weylCartanAction Q split (longest Q) h = h⁻¹ :=
  longestCartanAction_inversion Q split hm 0 1 (by decide)
    (linear_reflectionFixed_eq_kernel Q split 0 n μ₀ T hB₀ (s 0))
    (ree_perpendicular_kernels Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore).1

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- The reflection relation holds in N, not just in its Weyl quotient.
The two lifts may be any representatives of the original ordered classes. -/
theorem ree_reflection_product_eight (a b : Q.tits.N)
    (ha : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) a = Q.simple 0)
    (hb : QuotientGroup.mk' ((Q.tits.B ⊓ Q.tits.N).subgroupOf Q.tits.N) b = Q.simple 1) :
    (a*b)^8 = 1 :=
  reflection_product_eight_of_opposition Q split hm
    (ree_longestCartanAction_inversion Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore) a b ha hb

include hm hn μ₀ hB₀ μ₁ hB₁ s hcore in
/-- Source (6H)'s kernel separation for every pair of independent roots.
Independence means that their Weyl reflections differ; opposite roots have
one reflection and are therefore correctly excluded. -/
theorem ree_independent_root_centralizer_eq_bot
    (i j : Fin 2) (w v : Weyl Q)
    (hne : w⁻¹*Q.simple i*w ≠ v⁻¹*Q.simple j*v) :
    (((Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) ⊓
      centralizer (rootAt Q split i w : Set (X ⧸ Q.D))) ⊓
      centralizer (rootAt Q split j v : Set (X ⧸ Q.D))) = ⊥ := by
  apply independent_root_centralizer_eq_bot Q split hm ?_
    (ree_longestCartanAction_inversion Q split hm n hn m μ₀ T hB₀ μ₁ hB₁ s hcore) i j w v hne
  intro k
  have hk : k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl
  · exact linear_reflectionFixed_eq_kernel Q split 0 n μ₀ T hB₀ (s 0)
  · exact suzuki_reflectionFixed_eq_kernel Q split 1 m μ₁ hB₁ (s 1)

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
