module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.CommonField
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCartan

/-!
# Original marked consumer of the Ree common-field and Cartan construction

The full original Borel marking transports the naturally marked endpoint
quotients to the same finite source quotient. CommonField then proves their
common degree and the two-kernel Cartan product. Pulling this product back
retains the entire original Cartan and both endpoint inclusion squares.
For the generated original carrier, the final formula uses the literal Q.q.

Source: Fong--Seitz I (1973), (6H)(a), p.51. The original hypotheses and
natural panel markings are retained explicitly, including the earlier
odd-degree restriction. This leaf does not claim the remaining (6H) clauses,
the synchronized section-10 root relations, or a final Ree model comparison.
No finiteness of the original ambient group and no binary simplicity is used.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i)

include e h hm hn μ₀ hB₀ μ₁ hB₁ s in
/-- The naturally marked fields at the two original endpoints coincide in degree. -/
theorem original_ree_common_field_exponent : n = 2*m+1 :=
  ree_common_field_exponent Q split hm n hn m (faithfulModelMarking Q e h 0 μ₀) T
    (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀) (faithfulModelMarking Q e h 1 μ₁)
    (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁) s
    (LinearThreePresentation.borel_core_eq_bot Q e h)

include e h hm hn μ₀ hB₀ μ₁ hB₁ s in
theorem original_ree_cartan_card : Nat.card (originalCartan Q e h) = (2^(2*m+1)-1)^2 := by
  rw [Nat.card_congr (originalCartanEquiv Q e h).toEquiv]
  exact ree_cartan_card Q split hm n hn m (faithfulModelMarking Q e h 0 μ₀) T
    (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀) (faithfulModelMarking Q e h 1 μ₁)
    (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁) s
    (LinearThreePresentation.borel_core_eq_bot Q e h)

/-- The two exact source panel kernels give product coordinates on the original
Cartan, pulled back through the full common-Borel marking. -/
def originalReeCartanEquiv :
    (cartanPanelMap Q 0).ker × (cartanPanelMap Q 1).ker ≃* originalCartan Q e h :=
  (reeCartanEquiv Q split hm n hn m (faithfulModelMarking Q e h 0 μ₀) T
    (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀) (faithfulModelMarking Q e h 1 μ₁)
    (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁) s
    (LinearThreePresentation.borel_core_eq_bot Q e h)).trans (originalCartanEquiv Q e h).symm

@[simp] theorem originalReeCartanEquiv_borel
    (a : (cartanPanelMap Q 0).ker) (b : (cartanPanelMap Q 1).ker) :
    borelMap Q e h (originalReeCartanEquiv Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s (a,b)).val =
      (a.val : X ⧸ Q.D)*b.val := by
  change (originalCartanEquiv Q e h ((originalCartanEquiv Q e h).symm _): X ⧸ Q.D) = _
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- Both original endpoint squares retain the same actual Cartan product. -/
theorem originalReeCartanEquiv_endpoint (i : Fin 2)
    (a : (cartanPanelMap Q 0).ker) (b : (cartanPanelMap Q 1).ker) :
    let c := originalReeCartanEquiv Q e h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s (a,b)
    endpointMap Q e i ⟨c.val,commonBorel_le_parabolic i c.val.property⟩ =
      (a.val : X ⧸ Q.D)*b.val := by
  dsimp only
  rw [endpoint_borel Q e h i, originalReeCartanEquiv_borel]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (hm : rotationOrder Q = 8) (n : ℕ) (hn : Odd n) (m : ℕ)
  (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
  (T : Sylow 2 (PSL2BinaryMatrixGroup n))
  (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
  (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
  (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
  (s : ∀ i, RootReflection Q split i)

/-- On the original generated carrier the product comparison uses the literal
quotient map q, with no finiteness assumption on the original ambient group. -/
theorem originalReeCartanEquiv_quotient
    (a : (cartanPanelMap Q 0).ker) (b : (cartanPanelMap Q 1).ker) :
    let c := originalReeCartanEquiv Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s (a,b)
    Q.q ⟨c.val,parabolic_le_generated 0 (commonBorel_le_parabolic 0 c.val.property)⟩ =
      (a.val : (generated L S) ⧸ Q.D)*b.val := by
  dsimp only
  rw [originalCartan_quotient Q h]
  exact originalReeCartanEquiv_borel Q (originalMarkedIso Q) h split hm n hn m μ₀ T hB₀ μ₁ hB₁ s a b

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
