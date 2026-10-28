module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.SourceAmalgam

/-!
# Original solvable recognition from the earlier amalgam proposition

Construct the invariant plane and the literal pair IT,L₂T, verify all
applicability clauses, and select the linear case by excluding the product
case. The selected component gives H₀/O₂(H₀) ≅ L₃(2) through the actual
S₃ parabolic. The retained marked C₃, four involution classes, Burnside
fusion and commuting-product arguments then prove ambient recognition.

The only amalgam input is `PlaneAmalgamSource1347`, the restricted consequence
of the genuine earlier 13.4.7(1--4). No invariant plane, component selection,
Thompson normality, overgroup supplement, geometry, ambient involution fusion, centralizer
containment or E=G is an additional hypothesis at these endpoints.
The earlier 13.2--13.3, 13.4.2--7 and universal Structural1222 inputs remain
explicit for discharge by qt-d-1341-fixed-core-source, including the earlier
13.2.2(5) fusion control on V. Thus these are
conditional applications, not an unconditional proof of 13.4.8--9.
Source: Aschbacher--Smith 13.4.8--9, printed pp.904--907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual solvable-centralizer branch with all local amalgam and
recognition premises supplied from the original pair and earlier source input. -/
theorem isPSp_of_original_R1_source_amalgam
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
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
    (h1347 : PlaneAmalgamSource1347 D m) :
    ClassicalGroup.IsPSp G 3 2 := by
  obtain ⟨W,hW,hT,_,⟨K,_,_,_,hTK,hX,hK⟩,hnormal,hsupp⟩ :=
    exists_original_R1_linear_amalgam h₀ h structural D m hcase z hz hzL
      hout hfusion h1339 hsolv hindex h1342 h1347
  exact isPSp_of_original_R1_linear_component h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT
    ⟨K,hTK,hX,hK⟩ hnormal hsupp

/-- The same selected original pair carries the marked C₃ geometry and the
four actual involution classes. All witnesses use the same original third
vertex and its literal two-core. -/
theorem exists_original_R1_source_geometry_and_classes
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hcase : normalizer (ChapterB.baumann (firstFlagCore h structural D m) : Set G) ≤
      normalizer (L : Set G) ∨ ChapterC.IsShort L)
    (z : V) (hz : z.val ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hzL : z.val ∉ centralizer (L : Set G))
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
    (h1347 : PlaneAmalgamSource1347 D m) :
    ∃ W : Submodule (ZMod 2) (BinaryPermutation.natural (Fin 6)),
      Module.finrank (ZMod 2) W = 2 ∧
      (T : Subgroup G) ≤ normalizer (m.naturalPreimage W : Set G) ∧
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let P := I ⊔ (T : Subgroup G)
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := P ⊔ B
      let E := generated (normalizer (L : Set G)) z.val X
      X ∈ Chapter1.HOver G (T : Set G) ∧ LinearAmalgamConclusion T X ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) ∧
      Nonempty (MarkedC3 T L z.val X) ∧
      Nonempty (E ≃* Theory.SpecificGroups.SymplecticSix.Sp (ZMod 2)) ∧
      elementaryAbelianMaxJ (T : Subgroup G) = X.pCoreIn 2 ∧
      ∃ r : Fin 4 → X.pCoreIn 2,
        (∀ i, (r i).val ≠ 1 ∧ (r i).val ^ 2 = 1) ∧
        (∀ a ∈ E, a ^ 2 = 1 → a ≠ 1 →
          ∃! i : Fin 4, ∃ g ∈ E, MulAut.conj g a = (r i).val) := by
  obtain ⟨W,hW,hT,hlocal,hlin⟩ := exists_original_R1_linear_amalgam
    h₀ h structural D m hcase z hz hzL hout hfusion h1339 hsolv hindex h1342 h1347
  have hlin' := hlin
  obtain ⟨⟨K,hcomp,hfaith,hstar,hTK,hX,⟨eK⟩⟩,hnormal,hsupp⟩ := hlin
  let H := centralizer ({z.val} : Set G)
  let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
  let P := I ⊔ (T : Subgroup G)
  let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
  let X := P ⊔ B
  have hVJ := module_le_original_R1_thompson h₀ h structural D m hcase z hz hzL
    hout h1339 hsolv hindex h1342
  obtain ⟨_,_,⟨eP⟩,_⟩ := original_R1_line_parabolics h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342
  have hthird := third_quotient_of_normalized_linear_component X K P hX hTK eK
    le_sup_right le_sup_left eP
  have hg := (original_R1_inside_generation h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT).2
  obtain ⟨⟨C⟩,he⟩ := original_R1_marked_geometry h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hg
    (normalizer_component_centralizer_supplement h structural D m z) hthird
  have hclasses := original_R1_linear_component_four_classes h₀ h structural D m hcase z hz hzL
    hout hfusion h1339 hsolv hindex h1342 W hW hT ⟨K,hTK,hX,⟨eK⟩⟩
  refine ⟨W,hW,hT,hlocal,hlin',hthird,⟨C⟩,he,?_,hclasses⟩
  exact thompson_eq_plane_core D z.val X C hnormal

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
