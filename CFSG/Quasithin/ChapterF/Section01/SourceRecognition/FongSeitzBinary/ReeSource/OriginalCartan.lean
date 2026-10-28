module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.CartanFactors
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearThreePresentation

/-!
# The original Cartan in the marked source quotient

The full Cartan is pulled back through the original common-Borel marking.
Its two panel kernels are the actual original endpoint cores, so the source
joint-kernel and faithful rank-one inversion results apply without replacing
the original carrier or either endpoint square. The resulting product-order
bound is a checked part of Fong–Seitz I (6H)(a), not the common-field
conclusion: equality of the linear and Suzuki parameters and the remaining
(6H) clauses are still separate obligations.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups
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

/-- Pull back the entire source Cartan through the full original Borel marking. -/
def originalCartan : Subgroup (commonBorel L S) :=
  (Q.tits.B ⊓ Q.tits.N).comap (borelMap Q e h)

def originalCartanMap : originalCartan Q e h →* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  (borelMap Q e h).subgroupComap (Q.tits.B ⊓ Q.tits.N)

include e h
theorem originalCartanMap_bijective : Function.Bijective (originalCartanMap Q e h) := by
  let b : commonBorel L S ≃* Q.tits.B :=
    (MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle
  constructor
  · intro a c he
    apply Subtype.ext
    apply b.injective
    exact Subtype.ext (congrArg (fun z : (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) =>
      (z : X ⧸ Q.D)) he)
  · intro c
    let a := b.symm ⟨c,c.property.1⟩
    have he : borelMap Q e h a = c := congrArg Subtype.val (b.apply_symm_apply ⟨c,c.property.1⟩)
    refine ⟨⟨a,?_⟩,Subtype.ext he⟩
    change borelMap Q e h a ∈ Q.tits.B ⊓ Q.tits.N
    rw [he]
    exact c.property

def originalCartanEquiv : originalCartan Q e h ≃* (Q.tits.B ⊓ Q.tits.N : Subgroup (X ⧸ Q.D)) :=
  MulEquiv.ofBijective (originalCartanMap Q e h) (originalCartanMap_bijective Q e h)

@[simp] theorem originalCartanEquiv_apply (a : originalCartan Q e h) :
    (originalCartanEquiv Q e h a : X ⧸ Q.D) = borelMap Q e h a.val := rfl

/-- The same Cartan representative lies on both original endpoint squares. -/
theorem originalCartan_endpoint (i : Fin 2) (a : originalCartan Q e h) :
    endpointMap Q e i ⟨a.val,commonBorel_le_parabolic i a.val.property⟩ =
      (originalCartanEquiv Q e h a : X ⧸ Q.D) := endpoint_borel Q e h i a.val

/-- The source joint-kernel assertion, using the two original endpoint cores. -/
theorem original_joint_cartan_kernel (s : ∀ i, RootReflection Q split i) :
    (Q.tits.B ⊓ Q.tits.N) ⊓
      (originalPanelKernel (L := L) (S := S) 0).map (endpointMap Q e 0) ⊓
      (originalPanelKernel (L := L) (S := S) 1).map (endpointMap Q e 1) = ⊥ := by
  rw [originalPanelKernel_image Q e h 0, originalPanelKernel_image Q e h 1]
  exact joint_cartan_kernel_eq_bot Q split s (LinearThreePresentation.borel_core_eq_bot Q e h)

/-- The source linear fixed factor is the image of the actual original endpoint core. -/
theorem original_linear_fixed_kernel (i : Fin 2) (n : ℕ)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) :
    reflectionFixed Q split i =
      ((originalPanelKernel (L := L) (S := S) i).map (endpointMap Q e i)).subgroupOf
        (Q.tits.B ⊓ Q.tits.N) := by
  rw [originalPanelKernel_image Q e h i, ← cartanPanelMap_kernel]
  exact linear_reflectionFixed_eq_kernel Q split i n (faithfulModelMarking Q e h i μ) T
    (faithfulModelMarking_borel Q e h i μ _ hB) s

/-- The same exact kernel equality for the full Suzuki family, including Sz(2). -/
theorem original_suzuki_fixed_kernel (i : Fin 2) (m : ℕ)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* SuzukiMatrixGroup m)
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) :
    reflectionFixed Q split i =
      ((originalPanelKernel (L := L) (S := S) i).map (endpointMap Q e i)).subgroupOf
        (Q.tits.B ⊓ Q.tits.N) := by
  rw [originalPanelKernel_image Q e h i, ← cartanPanelMap_kernel]
  exact suzuki_reflectionFixed_eq_kernel Q split i m (faithfulModelMarking Q e h i μ)
    (faithfulModelMarking_borel Q e h i μ _ hB) s

/-- The full original Cartan satisfies the source product-order bound with the
actual natural faithful-panel markings on both original endpoints. -/
theorem original_ree_cartan_card_dvd (n : ℕ) (hn : 0 < n) (m : ℕ)
    (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup m)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : ∀ i, RootReflection Q split i) :
    Nat.card (originalCartan Q e h) ∣ (2^n-1)*(2^(2*m+1)-1) := by
  rw [Nat.card_congr (originalCartanEquiv Q e h).toEquiv]
  exact ree_cartan_card_dvd Q split n hn m (faithfulModelMarking Q e h 0 μ₀) T
    (faithfulModelMarking_borel Q e h 0 μ₀ _ hB₀) (faithfulModelMarking Q e h 1 μ₁)
    (faithfulModelMarking_borel Q e h 1 μ₁ _ hB₁) s
    (LinearThreePresentation.borel_core_eq_bot Q e h)

theorem original_binary_ree_cartan_eq_bot
    (μ₀ : (parabolic L S 0 ⧸ originalPanelKernel (L := L) (S := S) 0) ≃* PSL2BinaryMatrixGroup 1)
    (T : Sylow 2 (PSL2BinaryMatrixGroup 1))
    (hB₀ : (originalFaithfulBorel (L := L) (S := S) 0).map μ₀.toMonoidHom = normalizer (T : Set _))
    (μ₁ : (parabolic L S 1 ⧸ originalPanelKernel (L := L) (S := S) 1) ≃* SuzukiMatrixGroup 0)
    (hB₁ : (originalFaithfulBorel (L := L) (S := S) 1).map μ₁.toMonoidHom =
      normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))
    (s : ∀ i, RootReflection Q split i) : originalCartan Q e h = ⊥ := by
  apply Subgroup.card_eq_one.mp
  have hd := original_ree_cartan_card_dvd Q e h split 1 (by decide) 0 μ₀ T hB₀ μ₁ hB₁ s
  simpa using hd

/-- The linear reflection product gives actual coordinates on the original Cartan. -/
def originalLinearCartanEquiv (i : Fin 2) (n : ℕ)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) :
    (cartanPanelMap Q i).ker × reflectionInverted Q split i ≃* originalCartan Q e h :=
  (linearCartanEquiv Q split i n (faithfulModelMarking Q e h i μ) T
    (faithfulModelMarking_borel Q e h i μ _ hB) s).trans (originalCartanEquiv Q e h).symm

/-- The all-parameter Suzuki reflection product on the original Cartan. -/
def originalSuzukiCartanEquiv (i : Fin 2) (m : ℕ)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* SuzukiMatrixGroup m)
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) :
    (cartanPanelMap Q i).ker × reflectionInverted Q split i ≃* originalCartan Q e h :=
  (suzukiCartanEquiv Q split i m (faithfulModelMarking Q e h i μ)
    (faithfulModelMarking_borel Q e h i μ _ hB) s).trans (originalCartanEquiv Q e h).symm

theorem original_linear_inverted_card (i : Fin 2) (n : ℕ) (hn : 0 < n)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* PSL2BinaryMatrixGroup n)
    (T : Sylow 2 (PSL2BinaryMatrixGroup n))
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom = normalizer (T : Set _))
    (s : RootReflection Q split i) : Nat.card (reflectionInverted Q split i) = 2^n-1 :=
  linear_inverted_card Q split i n hn (faithfulModelMarking Q e h i μ) T
    (faithfulModelMarking_borel Q e h i μ _ hB) s

theorem original_suzuki_inverted_card (i : Fin 2) (m : ℕ)
    (μ : (parabolic L S i ⧸ originalPanelKernel (L := L) (S := S) i) ≃* SuzukiMatrixGroup m)
    (hB : (originalFaithfulBorel (L := L) (S := S) i).map μ.toMonoidHom =
      normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))
    (s : RootReflection Q split i) : Nat.card (reflectionInverted Q split i) = 2^(2*m+1)-1 :=
  suzuki_inverted_card Q split i m (faithfulModelMarking Q e h i μ)
    (faithfulModelMarking_borel Q e h i μ _ hB) s

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}

/-- On the generated original carrier the Cartan marking is the literal q. -/
theorem originalCartan_quotient (Q : SourceQuotient L S) (h : HypothesisF11 L S)
    (a : originalCartan Q (originalMarkedIso Q) h) :
    Q.q ⟨a.val, parabolic_le_generated 0
      (commonBorel_le_parabolic 0 a.val.property)⟩ =
        (originalCartanEquiv Q (originalMarkedIso Q) h a : (generated L S) ⧸ Q.D) := by
  have he := originalCartan_endpoint Q (originalMarkedIso Q) h 0 a
  exact (originalMarkedIso_left_apply Q _).symm.trans he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
