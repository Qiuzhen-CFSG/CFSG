module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.OriginalChamber
public import Theory.SpecificGroups.PSL3Two.NormalExtension.Parabolic

/-!
# The original linear amalgam and ambient symplectic recognition

In case (ii) of 13.4.7, write the literal H₀ as K₀T, with T normalizing
K₀ and K₀/O₂(K₀)≅L₃(2). The actual parabolic IT has S₃ two-core quotient.
The outer-extension exclusion therefore proves H₀/O₂(H₀)≅L₃(2). All
relative normality and quotient transports use the original inclusions.

The final theorem constructs the original marked C₃ system and applies the
checked involution representatives, Burnside fusion and commuting-product
centralizer argument. It proves IsPSp G 3 2 from the genuine source local
product and the case-(ii) component, Thompson normality and overgroup
supplement. It assumes neither the full H₀ quotient nor any geometry or
ambient recognition premise.

The 13.4.7 alternative theorem and its (3–4) exclusions, the original
13.2–13.3 inputs and universal Structural1222 still require earlier-source
discharge with qt-d-1341-fixed-core-source. Selecting case (ii) from those
alternatives and the retained individual four-orbit exports remain part
of qt-d-1341-solvable-source. This is a conditional assembly, not a claim
that those earlier theorems have been proved.
Source: Aschbacher–Smith 13.4.7–9, printed pp.899–907.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource SolvableCentralizerC3
open Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}


/-- Upgrade the source component quotient to the quotient of the literal
third vertex, using its actual S₃ parabolic. -/
theorem third_quotient_of_normalized_linear_component
    (X K P : Subgroup G) (hX : X = K ⊔ (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL)
    (hTP : (T : Subgroup G) ≤ P) (hPX : P ≤ X)
    (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) :
    Nonempty ((X ⧸ pCore 2 X) ≃* Matrix.PSL3Two.PSL) := by
  have hKX : K ≤ X := hX ▸ le_sup_left
  have hTX : (T : Subgroup G) ≤ X := hX ▸ le_sup_right
  let N := K.subgroupOf X
  let A := P.subgroupOf X
  let S := T.subtype hTX
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (show X ≤ normalizer (K : Set G) by rw [hX]; exact sup_le K.le_normalizer hTK)
  let a := subgroupOfEquivOfLe hKX
  let b := subgroupOfEquivOfLe hPX
  have hgen : N ⊔ (S : Subgroup X) = ⊤ := by
    apply map_injective X.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hKX,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hTX,←MonoidHom.range_eq_map,range_subtype]
    exact hX.symm
  exact Matrix.PSL3Two.quotient_of_normal_component_and_symmetricThree_parabolic N
    ((QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eK) S hgen A
    (fun _ ht => hTP ht) ((QuotientGroup.congr _ _ b (pCore_map_iso 2 b)).trans eP)


/-- The original solvable branch from the component conclusion of 13.4.7(ii),
Thompson normality and the source overgroup supplement. The full third quotient,
marked geometry, involution fusion and commuting-product premises are proved. -/
theorem isPSp_of_original_R1_linear_amalgam
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
        Nonempty ((K ⧸ pCore 2 K) ≃* Matrix.PSL3Two.PSL))
    (hnormal :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      (I ⊔ (T : Subgroup G)) ⊔ B ≤
        normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G))
    (supplement :
      let H := centralizer ({z.val} : Set G)
      let I := conjugateSpanBy (elementaryAbelianMaxJ (firstFlagCore h structural D m)) H
      let B := (L ⊔ (T : Subgroup G)) ⊓ normalizer (m.naturalPreimage W : Set G)
      let X := (I ⊔ (T : Subgroup G)) ⊔ B
      ∀ Y : Subgroup G, Y ∈ Chapter1.HOver G (X : Set G) →
        (Y : Set G) = (X : Set G) *
          (Y ⊓ centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X : Set G) : Subgroup G)) :
    ClassicalGroup.IsPSp G 3 2 := by
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
  exact isPSp_of_original_R1_and_amalgam_conclusions h₀ h structural D m hcase z hz hzL
    hVJ hout hfusion h1339 hsolv hindex h1342 W hW hT hgenerate hsupp hthird hnormal supplement

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
