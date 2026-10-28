module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry.Normalizers
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The local dual-root calculation in G.2.5

A root centered at V₁ with axis V₁+V₁ᵍ lifts into the part of U fixing V₁ᵍ.
The full LT point-normalizer calculation proves that this part normalizes Uᵍ.
The Frattini bound kills its action on the two pair intersections in U modulo
S₂; normalization of U and Uᵍ by S forces its displacement on the third pair
into W∩Wᵍ. Commutator preimages extend the bound to S₃.

The final theorem applies these bounds to the literal quotient action from
`Hypothesis.lower_action`, retaining its original coordinate projection. Full
I-invariance is still an input there; the model root-generation argument must
discharge it in the final dual-geometry assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
G.2.5(6), printed p.336, PDF p.347.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
open Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : LinearThree.Hypothesis D F n g h)
include d

/-- The local root calculation on the literal third layer. A subgroup of U
which normalizes Uᵍ fixes the two intersections in U modulo S₂ and moves the
whole third layer into W ∩ Wᵍ. -/
theorem root_step (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (R : Subgroup G) (hRU : R ≤ D.U)
    (hRg : R ≤ normalizer (conjugate D.U g : Set G)) :
    R ≤ normalizer (S₃ D g h : Set G) ∧
    ⁅S₃ D g h, R⁆ ≤ W D g h ⊓ conjugate (W D g h) g ∧
    ⁅W D g h ⊓ conjugate (W D g h) g, R⁆ ≤ S₂ D g h ∧
    ⁅W D g h ⊓ conjugate (W D g h) h, R⁆ ≤ S₂ D g h := by
  let A := W D g h ⊓ conjugate (W D g h) g
  let B := W D g h ⊓ conjugate (W D g h) h
  let C := conjugate (W D g h) g ⊓ conjugate (W D g h) h
  have hWS : W D g h ≤ S D g h := inf_le_right
  have hWgS : conjugate (W D g h) g ≤ S D g h := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact inf_le_right
  have hWA : S D g h ≤ normalizer (W D g h : Set G) :=
    (le_inf hU (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hWg : S D g h ≤ normalizer (conjugate (W D g h) g : Set G) := by
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact (le_inf hUg (S D g h).le_normalizer).trans inf_normalizer_le_normalizer_inf
  have hAN : S D g h ≤ normalizer (A : Set G) :=
    (le_inf hWA hWg).trans inf_normalizer_le_normalizer_inf
  have hVE := (d.intersection hUT hf).1
  have hEA : S₂ D g h ≤ A := by
    rw [d.S₂_eq_triple_W hUT hf hLI]
    exact inf_le_left
  have hder : ⁅D.U, D.U⁆ ≤ S₂ D g h :=
    ((derived_le_of_frattini_image_le (d.U_isPGroup hUT) hf).trans d.setup.point_le).trans hVE
  have hA : ⁅A, R⁆ ≤ S₂ D g h :=
    (commutator_mono (inf_le_left.trans inf_le_left) hRU).trans hder
  have hB : ⁅B, R⁆ ≤ S₂ D g h :=
    (commutator_mono (inf_le_left.trans inf_le_left) hRU).trans hder
  have hUS : ⁅D.U, S D g h⁆ ≤ W D g h :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hU)
      (le_normalizer_iff_commutator_le_right.mp
        ((show D.U ≤ I D g h from le_sup_left.trans le_sup_left).trans (I_normalizes_core D g h)))
  have hCW : ⁅C, R⁆ ≤ W D g h := by
    rw [commutator_comm]
    exact (commutator_mono hRU (inf_le_left.trans hWgS)).trans hUS
  have hCUg : ⁅C, R⁆ ≤ conjugate D.U g :=
    (commutator_mono (inf_le_left.trans (map_mono inf_le_left)) le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hRg)
  have hC : ⁅C, R⁆ ≤ A := by
    change ⁅C, R⁆ ≤ W D g h ⊓ conjugate (W D g h) g
    rw [conjugate_W D g h g (hLI d.g_mem)]
    exact le_inf hCW (le_inf hCUg (hCW.trans hWS))
  have hpre : S₃ D g h ≤ commutatorPreimage (S D g h) R A :=
    sup_le (sup_le
      (le_commutatorPreimage (inf_le_left.trans hWS) (hA.trans hEA))
      (le_commutatorPreimage (inf_le_left.trans hWS) (hB.trans hEA)))
      (le_commutatorPreimage (inf_le_left.trans hWgS) hC)
  have hmove : ⁅S₃ D g h, R⁆ ≤ A :=
    (commutator_mono hpre le_rfl).trans (commutator_commutatorPreimage_le _ _ _ hAN)
  exact ⟨le_normalizer_iff_commutator_le_left.mpr
    (hmove.trans (le_sup_left.trans le_sup_left)), hmove, hA, hB⟩

/-- The actual part of U fixing the second marked source point. -/
def pointFixingPart (D : Setup G) (x : G) : Subgroup G :=
  D.U ⊓ normalizer (conjugate D.V₁ x : Set G)

/-- This source-defined subgroup normalizes the corresponding conjugate of U. -/
theorem pointFixingPart_normalizes_U (hUT : D.U ≤ D.T) :
    pointFixingPart D g ≤ normalizer (conjugate D.U g : Set G) :=
  (le_inf ((inf_le_left.trans hUT).trans le_sup_right) inf_le_right).trans
    (conjugatePointNormalizerLT_normalizes_U d ⟨g, d.g_mem⟩)

/-- No separate normalization premise is needed for the actual root lift. -/
theorem pointFixingPart_root_step (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G)) :
    pointFixingPart D g ≤ normalizer (S₃ D g h : Set G) ∧
    ⁅S₃ D g h, pointFixingPart D g⁆ ≤ W D g h ⊓ conjugate (W D g h) g ∧
    ⁅W D g h ⊓ conjugate (W D g h) g, pointFixingPart D g⁆ ≤ S₂ D g h ∧
    ⁅W D g h ⊓ conjugate (W D g h) h, pointFixingPart D g⁆ ≤ S₂ D g h :=
  root_step d hUT hf hLI hU hUg _ inf_le_left (pointFixingPart_normalizes_U d hUT)

/-- Apply the local root calculation to the actual descended lower action and
its literal quotient map. The complete I-invariance input is retained for
final assembly, rather than hidden in a representation witness. -/
theorem lower_action_root_step (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁) (hLI : D.L ≤ I D g h)
    (hU : S D g h ≤ normalizer (D.U : Set G))
    (hUg : S D g h ≤ normalizer (conjugate D.U g : Set G))
    (hUh : S D g h ≤ normalizer (conjugate D.U h : Set G))
    (hgen : S D g h = (W D g h ⊔ conjugate (W D g h) g) ⊔ conjugate (W D g h) h)
    (hN : I D g h ≤ normalizer (S₃ D g h : Set G))
    (e : StarComparison D g h hLI) :
    letI := Hypothesis.lower_normal d hUT hf hLI
    letI := Hypothesis.lower_elementary d hUT hf hLI
    ∃ (σ : Representation (ZMod 2) (D.star D.L) (Additive (LowerQuotient D g h)))
      (s : Representation.BinaryConjugationSection (I D g h) (S₃ D g h) (S₂ D g h)
        (σ.comp e.projection)),
      (∀ a : S₃ D g h, (s.coordinates a).toAdd =
        Additive.ofMul (QuotientGroup.mk' ((S₂ D g h).subgroupOf (S₃ D g h)) a)) ∧
      ∀ u : I D g h, (u : G) ∈ pointFixingPart D g →
        LinearMap.range (σ (e.projection u) - 1) ≤
          s.imageSpace (W D g h ⊓ conjugate (W D g h) g) ∧
        (∀ v ∈ s.imageSpace (W D g h ⊓ conjugate (W D g h) g),
          σ (e.projection u) v = v) ∧
        (∀ v ∈ s.imageSpace (W D g h ⊓ conjugate (W D g h) h),
          σ (e.projection u) v = v) := by
  let := Hypothesis.lower_normal d hUT hf hLI
  let := Hypothesis.lower_elementary d hUT hf hLI
  obtain ⟨σ, s, hcoord⟩ := Hypothesis.lower_action d hUT hf hLI hU hUg hUh hgen hN e
  obtain ⟨_, hmove, hfixA, hfixB⟩ := pointFixingPart_root_step d hUT hf hLI hU hUg
  rw [commutator_comm] at hmove hfixA hfixB
  refine ⟨σ, s, hcoord, fun u hu => ?_⟩
  exact ⟨s.displacement_range_le_imageSpace_of_commutator_le _ _ hmove u hu,
    s.fixed_on_imageSpace_of_commutator_le _ _ hfixA u hu,
    s.fixed_on_imageSpace_of_commutator_le _ _ hfixB u hu⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.Recognition.DualGeometry
