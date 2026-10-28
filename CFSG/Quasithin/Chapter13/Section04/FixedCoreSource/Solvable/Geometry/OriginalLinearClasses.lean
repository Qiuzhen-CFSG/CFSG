module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalLinearAmalgam
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.OriginalClasses

/-!
# Four marked classes in the original solvable source application

The original R₁ product and the normalized L₃(2) component construct the
literal third quotient and marked C₃ geometry. Applying the intrinsic
four-class theorem to this constructed geometry gives four actual
involutions in O₂(H₀), each representing exactly one E-class. Thus the
orbit classification is connected to the original parabolics and chosen
five-dimensional module, with no assumed geometry or fusion statement.

The source 13.4.7 case-(ii) component remains explicit here, as in the
ambient-recognition consumer OriginalLinearAmalgam. Selecting that case
from the genuine alternatives and the earlier-source discharge remain
with the original solvable and fixed-core assembly owners, respectively.
Source: Aschbacher–Smith 13.4.9, printed pp.906–907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The four original core representatives exhaust the involution classes
of the actual generated subgroup in the source case-(ii) application. -/
theorem original_R1_linear_amalgam_four_classes
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
    (hVJ : V ≤ elementaryAbelianMaxJ (firstFlagCore h structural D m))
    (hout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (h1339 : ∀ Y : Subgroup G, Y ≤ centralizer ({z.val} : Set G) →
      centralizer ({z.val} : Set G) ≤ normalizer (Y : Set G) →
      Y ≤ normalizer (L : Set G) → IsPPerfect 2 Y →
      Y = ⊥ ∨ (Y = selectedFirstResidual T L V z.val ∧ Nat.card (Y ⧸ pCore 2 Y) = 3))
    (hsolv : Group.IsSolvable (centralizer ({z.val} : Set G)))
    (hindex : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (h1342 : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) →
      (primeToResidual 3 (normalizer (L : Set G))).map
      (normalizer (L : Set G)).subtype = L)
    (W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)))
    (hW : Module.finrank (ZMod 2) W = 2)
    (hT : (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G))
    (hgenerate : (firstCentralizerResidual L z.val ⊔ (T : Subgroup G)) ⊔
      ((L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)) =
        L ⊔ (T : Subgroup G))
    (hsupp : normalizer (L : Set G) =
      L ⊔ (centralizer ({z.val} : Set G) ⊓ normalizer (L : Set G)))
    (hlinear :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∃ K : Subgroup G, (T : Subgroup G) ≤ normalizer (K : Set G) ∧
        X = K ⊔ (T : Subgroup G) ∧
        Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)) :
    let H := centralizer ({z.val} : Set G)
    let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
    let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
    let X := (I ⊔ (T : Subgroup G)) ⊔ B
    let E := generated (normalizer (L : Set G)) z.val X
    ∃ r : Fin 4 → X.pCoreIn 2,
      (∀ i, (r i).val ≠ 1 ∧ (r i).val ^ 2 = 1) ∧
      (∀ a ∈ E, a ^ 2 = 1 → a ≠ 1 →
        ∃! i : Fin 4, ∃ g ∈ E, MulAut.conj g a = (r i).val) := by
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  obtain ⟨K,hTK,hX,⟨eK⟩⟩ := hlinear
  obtain ⟨_,_,⟨eP⟩,_⟩ := original_R1_line_parabolics h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342
  have hthird := third_quotient_of_normalized_linear_component X K P hX hTK eK
    le_sup_right le_sup_left eP
  obtain ⟨⟨C⟩,_⟩ := original_R1_marked_geometry h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hgenerate hsupp hthird
  exact exists_original_four_involution_classes D z.val X C

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
