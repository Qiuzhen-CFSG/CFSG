module

public import Theory.SpecificGroups.ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem.RootGeometry
public import Theory.SpecificGroups.LieType.OddExceptionalSubsystems.F4Identification.WordDescent.ComplementRepresentation.PairActions.ShortA2.Model
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The diagonal scalar kernel of the two marked A₂ factors

Generation by the four adjacent elementary curves extends the proved cross-root
commutation to the two full SL₃ images. Any kernel pair of faithful factor maps
is therefore central in each factor. Elementary diagonal words express these
scalar matrices by the two simple coroots. The fourth F₄ torus coordinate then
identifies their scalars. Thus the kernel lies in the diagonal cubic center.
Source: GLS3 1.12.1(e), 1.12.6 and the subsystem construction in 2.6.2--3.
-/

@[expose] public noncomputable section
open Subgroup Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
open ReeF4.CentralCovers.OddPrimary.Cyclotomic
open ReeF4.BinaryDegree.ExceptionalTensor
open ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.RootModel.Corrected
open TwistedE6.FoldedSubsystem.F4Identification.ComplementRepresentation.ShortA2
variable {F : Type*} [Field F]

abbrev simpleGenerator (s k : Bool) (t : F) : SL3 F := modelGenerator F s k t

/-- The literal four-curve marking detects homomorphisms on full SL₃. -/
theorem hom_ext_simple {A : Type*} [Group A] {f g : SL3 F →* A}
    (h : ∀ s k t, f (simpleGenerator s k t) = g (simpleGenerator s k t)) : f = g := by
  have he : MonoidHom.eqLocus f g = ⊤ := model_generates F _ h
  ext x
  exact show x ∈ MonoidHom.eqLocus f g from he ▸ mem_top x

/-- Scalar matrices, with their center retained, are two simple diagonal words. -/
def slCoroot (k : Bool) (a : Fˣ) : SL3 F :=
  if k then Matrix.SpecialLinearGroup.diag2n (show (0 : Fin 3) ≠ 1 by decide) (a : F) a.ne_zero
  else Matrix.SpecialLinearGroup.diag2n (show (1 : Fin 3) ≠ 2 by decide) (a : F) a.ne_zero

theorem slCoroot_word (k : Bool) (a : Fˣ) :
    slCoroot k a = simpleGenerator true k (a : F) * simpleGenerator false k (-((a : F)⁻¹)) *
      simpleGenerator true k (a : F) * simpleGenerator true k (-1) *
        simpleGenerator false k 1 * simpleGenerator true k (-1) := by
  cases k
  · exact Atlas.diagonal_elementary_decomposition (by decide) (a : F) a.ne_zero
  · exact Atlas.diagonal_elementary_decomposition (by decide) (a : F) a.ne_zero

theorem central_coroot_expression (A : SL3 F) (hA : A ∈ center (SL3 F)) :
    ∃ a : Fˣ, A.val = Matrix.scalar (Fin 3) (a : F) ∧
      A = slCoroot true a * slCoroot false a⁻¹ := by
  obtain ⟨c, hc, hs⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hc3 : c ^ 3 = 1 := by simpa using hc
  have hc0 : c ≠ 0 := by intro hz; simp [hz] at hc3
  let a : Fˣ := Units.mk0 c hc0
  refine ⟨a, hs.symm, ?_⟩
  apply Subtype.ext
  rw [← hs, Matrix.SpecialLinearGroup.coe_mul]
  change Matrix.scalar (Fin 3) c = _
  simp only [slCoroot, Bool.false_eq_true, ↓reduceIte, Matrix.SpecialLinearGroup.diag2n_coe,
    Matrix.diagonal_mul_diagonal]
  have hc2 : c⁻¹ * c⁻¹ = c := by
    have he : c * c ^ 2 = 1 := by rw [← pow_succ', hc3]
    calc
      c⁻¹ * c⁻¹ = (c ^ 2)⁻¹ := by rw [pow_two, _root_.mul_inv_rev]
      _ = c := (eq_inv_of_mul_eq_one_left he).symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a, Matrix.scalar_apply, Matrix.diagonal, hc2]

variable [IsAlgClosed F] [CharP F 2]

/-- The root equations that mark an actual SL₃ factor. -/
def MarkedMap (f : SL3 F →* AlgebraicPoints F) (r : Bool → F4Chevalley.Root) : Prop :=
  ∀ s k t, f (simpleGenerator s k t) = rootPoint (signedRoot s (r k)) t

omit [CharP F 2] in
theorem markedMap_coroot {f : SL3 F →* AlgebraicPoints F}
    {r : Bool → F4Chevalley.Root} (hf : MarkedMap f r) (k : Bool) (a : Fˣ) :
    f (slCoroot k a) = algebraicCorootElement (r k) a := by
  change ∀ s k t, f (simpleGenerator s k t) = rootPoint (signedRoot s (r k)) t at hf
  rw [slCoroot_word]
  simp only [map_mul, hf, signedRoot, Bool.false_eq_true, ↓reduceIte]
  simp only [algebraicCorootElement, algebraicNElement, Units.val_one,
    inv_one, _root_.mul_inv_rev, ZeroAndMiddle.root_inv, neg_neg]
  simp only [rootPoint, algebraicRootElement, mul_assoc]

/-- Orthogonality holds on the complete two images, not just their tori. -/
theorem markedMaps_commute {L S : SL3 F →* AlgebraicPoints F}
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot) (A B : SL3 F) :
    Commute (L A) (S B) := by
  have hs (s k : Bool) (a : F) : ∀ B, Commute (L (simpleGenerator s k a)) (S B) := by
    have ht : (centralizer ({L (simpleGenerator s k a)} : Set (AlgebraicPoints F))).comap S = ⊤ := by
      apply model_generates F
      intro t l b
      change S (simpleGenerator t l b) ∈ centralizer ({L (simpleGenerator s k a)} : Set _)
      rw [mem_centralizer_singleton_iff, hL, hS]
      exact (cross_root_commute s k t l a b).eq.symm
    intro B
    have hm : B ∈ (centralizer ({L (simpleGenerator s k a)} : Set (AlgebraicPoints F))).comap S :=
      ht ▸ mem_top B
    exact (mem_centralizer_singleton_iff.mp hm).symm
  have ht : (centralizer ({S B} : Set (AlgebraicPoints F))).comap L = ⊤ := by
    apply model_generates F
    intro s k a
    exact mem_centralizer_singleton_iff.mpr (hs s k a B).eq
  have hm : A ∈ (centralizer ({S B} : Set (AlgebraicPoints F))).comap L := ht ▸ mem_top A
  exact mem_centralizer_singleton_iff.mp hm

/-- The product of the two actual commuting factor maps. -/
def pairMap (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot) :
    SL3 F × SL3 F →* AlgebraicPoints F :=
  L.noncommCoprod S (markedMaps_commute hL hS)

theorem pairMap_kernel_central (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot)
    (hLi : Function.Injective L) (hSi : Function.Injective S)
    (A B : SL3 F) (h : pairMap L S hL hS (A,B) = 1) :
    A ∈ center (SL3 F) ∧ B ∈ center (SL3 F) := by
  have hprod : L A * S B = 1 := h
  have hLA : L A = (S B)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hSB : S B = (L A)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  constructor
  · rw [mem_center_iff]
    intro x
    apply hLi
    simp only [map_mul, hLA]
    exact ((markedMaps_commute hL hS x B).inv_right).eq
  · rw [mem_center_iff]
    intro x
    apply hSi
    simp only [map_mul, hSB]
    exact ((markedMaps_commute hL hS A x).symm.inv_right).eq

/-- The fourth literal torus coordinate identifies the two central scalars. -/
theorem pairMap_kernel (L S : SL3 F →* AlgebraicPoints F)
    (hL : MarkedMap L longRoot) (hS : MarkedMap S shortRoot)
    (hLi : Function.Injective L) (hSi : Function.Injective S)
    (A B : SL3 F) (h : pairMap L S hL hS (A,B) = 1) :
    A = B ∧ A ∈ center (SL3 F) := by
  obtain ⟨hAc, hBc⟩ := pairMap_kernel_central L S hL hS hLi hSi A B h
  obtain ⟨a, ha, hA⟩ := central_coroot_expression A hAc
  obtain ⟨b, hb, hB⟩ := central_coroot_expression B hBc
  have hp : L A * S B = 1 := h
  rw [hA, hB, map_mul, map_mul, markedMap_coroot hL, markedMap_coroot hL,
    markedMap_coroot hS, markedMap_coroot hS] at hp
  simp only [Three.Descent.ExceptionalTorus.coroot_diagonal, ← map_mul] at hp
  have hu := diagonal_injective (hp.trans (map_one Cyclotomic.diagonal).symm)
  have h3 := congrFun hu 3
  have hab : a = b := by
    apply inv_mul_eq_one.mp
    simpa [longRoot, shortRoot,
      Three.Descent.ExceptionalTorus.lowestRoot_corootCoordinates,
      corootCoordinates_simple] using h3
  exact ⟨Subtype.ext (ha.trans (hab ▸ hb.symm)), hAc⟩

end ReeF4.CentralCovers.OddPrimary.GoodPrimes.Unitary.Descent.Subsystem
