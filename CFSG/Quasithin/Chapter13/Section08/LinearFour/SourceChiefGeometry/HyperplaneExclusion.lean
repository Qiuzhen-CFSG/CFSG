module
public import CFSG.Quasithin.Chapter13.Section08.LinearFour.SourceChiefGeometry.HyperplaneConstruction
public import Theory.GroupTheory.ConjugateSpanSeedCentralizer

/-!
# Applying the constructed critical hyperplane to the terminal exclusion

The natural section and the original critical conjugator give |Uγ| = 32
and |A₁| = 2. The seed centralizer bound and the excluded reverse line
prove that the upper critical group centralizes the natural axis. Its
original parabolic placement then gives image order four and constructs
E_H U_H as a hyperplane in V_H. The actual exterior action supplies both
critical intersection indices and A₁ ≤ V_H. These conclusions feed the
source centralizer chain and the faithful chief-section contradiction on
H_C/V_H, without assuming H_C/V_H elementary abelian.

The initial natural/exterior markings, reciprocal placement, strict image
inclusion and axis/kernel premises, and the 13.8.31 chief obstruction
remain explicit obligations of qt-d-138-linear-four-source. Earlier
13.8.27 setup belongs to qt-d-138-six-g2-source; qt-d-1381-source owns final
assembly. This conditional application does not complete 13.8.28.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
13.8.32(3) and the proof of 13.8.28, printed pp.965–966, with 13.5.4(4).
The same y, inverse conjugation and quotient kernel are retained throughout.
-/

public noncomputable section
open Subgroup Representation NoncentralChiefRefinement
open scoped MatrixGroups
open Atlas.Order20160A8.Bivectors (exteriorMap)
open BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.Chapter13.Section08.LinearFour
open BinaryParabolicExteriorSquare
variable {G : Type*} [Group G] [Finite G]

/-- The source hyperplane, both critical indices and line placement are proved
from the reciprocal parabolic; the terminal chief-section contradiction uses
the same quotient and critical conjugator throughout. -/
theorem source_linear_four_exclusion_of_reciprocal_parabolic
    (H Q QH HC UH V1 V3 V VH R A1 Uγ Gγ K DR : Subgroup G)
    [IsElementaryAbelian 2 Uγ]
    (hQH : QH = H.pCoreIn 2) (hVC : VH ≤ HC)
    (hQR : QH ≤ R) (hindex : Q.relIndex R = 4)
    (hcent : Q ⊓ QH ≤ centralizer (V3 : Set G))
    (hdual : (QH ⊓ centralizer (V3 : Set G)).relIndex QH = 4)
    (hHCQH : HC ≤ QH) (hHCV3 : HC ≤ centralizer (V3 : Set G))
    (hHHC : H ≤ normalizer (HC : Set G))
    (hQV : Q ≤ centralizer (V : Set G))
    (hVH : VH = conjugateSpanBy V H)
    (hGγ : Gγ = centralizer (A1 : Set G))
    (hGγUγ : Gγ ≤ normalizer (Uγ : Set G)) (hUγH : Uγ ≤ H)
    (hV1 : Nat.card V1 = 2)
    (ν : Representation (ZMod 2) H (Fin 4 → ZMod 2))
    (dnatural : BinaryConjugationSection H UH V1 ν)
    (ρ : Representation (ZMod 2) H (Fin 6 → ZMod 2))
    (π : H →* SL(4, ZMod 2)) (hker : π.ker = QH.subgroupOf H)
    (hact : ∀ h x, ρ h x = exteriorMap (π h).val x)
    (d : BinaryConjugationSection H VH UH ρ)
    (houtside : ¬ Uγ ≤ QH) (hmeet : Uγ ⊓ UH ≠ ⊥)
    (hcommV : ⁅Uγ,VH⁆ ≤ Uγ ⊓ VH)
    (hnatural : ∀ h w, ν h w = Matrix.mulVec (π h).val w)
    (hV1D : V1 ≤ DR) (hDU : DR ≤ UH) (hindexD : DR.relIndex UH = 2)
    (y : G) (hUγ : Uγ = UH.conjBy y) (hA1 : A1 = V1.conjBy y)
    (hbackUH : UH.conjBy y⁻¹ ≤ H) (hbackVH : VH.conjBy y⁻¹ ≤ H)
    (hlower : (QH.conjBy y).relIndex UH = 2)
    (hstrict : ((UH.conjBy y⁻¹).subgroupOf H).map π <
      ((VH.conjBy y⁻¹).subgroupOf H).map π)
    (hspanUH : UH = conjugateSpanBy V3 H)
    (hseed : ⁅centralizer (V3:Set G),V⁆ ≤ V1)
    (haxis : DR ≤ centralizer (UH.conjBy y⁻¹ : Set G))
    (hV1outside : ¬ V1 ≤ Uγ)
    (g : SL(4,ZMod 2))
    (hradical : ((VH.conjBy y⁻¹).subgroupOf H).map π ≤ PlaneRadical.radical.conjBy g)
    (hcommE : ⁅Uγ,VH ⊓ QH.conjBy y⁆ ≤ A1)
    (hcover : IsSQTK KnownSimple.IsKnownSimple H)
    (e : (H ⧸ pCore 2 H) ≃* LinearGroup 4)
    (hKH : K ≤ H) (hK : IsPPerfect 2 K) (hmove : ¬ ⁅HC, K⁆ ≤ VH)
    (hKonto : Function.Surjective
      ((QuotientGroup.mk' (pCore 2 H)).comp (K.subgroupOf H).subtype))
    (hnotfour : ∀ s : ChiefSeries H,
      s.head.val.map H.subtype = VH → s.last.val.map H.subtype = HC →
      (∀ i : Fin s.length, ∀ D : Subgroup (Section (s i.castSucc) (s i.succ)),
        (∀ k : K.subgroupOf H, ∀ x, x ∈ D →
          sectionAction (s i.castSucc) (s i.succ) k x ∈ D) → D = ⊥ ∨ D = ⊤) →
      s.restrictedNoncentralCount (K.subgroupOf H) = 1 → ∀ i : Fin s.length,
        (¬ ∀ k : K.subgroupOf H, ∀ x,
          sectionAction (s i.castSucc) (s i.succ) k x = x) →
          Nat.card (Section (s i.castSucc) (s i.succ)) ≠ 16) : False := by
  have hU : Nat.card Uγ = 32 := by
    rw [hUγ]
    change Nat.card (UH.map _) = 32
    rw [card_map_of_injective (MulAut.conj y).injective,dnatural.card_section,hV1]
    norm_num
  have hA : Nat.card A1 = 2 := by
    rw [hA1]
    change Nat.card (V1.map _) = 2
    rw [card_map_of_injective (MulAut.conj y).injective,hV1]
  have hAH : A1 ≤ H := by
    rw [hA1]
    have hm : V1.conjBy y ≤ UH.conjBy y := map_mono dnatural.kernel_le
    exact (hm.trans_eq hUγ.symm).trans hUγH
  have hn1 : H ≤ normalizer (V1:Set G) :=
    (normal_subgroupOf_iff_le_normalizer
      (dnatural.kernel_le.trans dnatural.section_le)).mp dnatural.kernel_normal_actor
  have hline : ¬ V1.conjBy y⁻¹ ≤ UH := by
    intro hh
    have hm := map_mono (f := (MulAut.conj y).toMonoidHom) hh
    change (V1.conjBy y⁻¹).conjBy y ≤ UH.conjBy y at hm
    rw [conjBy_inv'] at hm
    exact hV1outside (hm.trans_eq hUγ.symm)
  have hcentral : VH.conjBy y⁻¹ ≤ centralizer (DR:Set G) := by
    rw [hVH]
    exact conjugateSpanBy_centralizes_axis_of_line_not_le H UH V1 V3 V DR hDU dnatural.normalized hn1
      hspanUH hseed hV1 y⁻¹ (by rw [←hVH]; exact hbackVH) haxis hline
  obtain ⟨hstar,hintersection,hA1V⟩ := source_critical_geometry_of_reciprocal_parabolic
    H UH V1 DR QH VH Uγ A1 ν dnatural π hker hnatural ρ d hact
    hV1D hDU hindexD y hbackUH hbackVH hlower hstrict hcentral g hradical
    hUγH houtside hcommV (hVC.trans hHCQH) hU hmeet hcommE hAH hA
  exact source_linear_four_exclusion H Q QH HC V3 V VH R A1 Uγ Gγ K
    hQH hVC hQR hindex hcent hdual hHCQH hHCV3 hHHC hQV hVH hA1V hGγ
    hGγUγ hUγH hU hstar hintersection hcover e hKH hK hmove hKonto hnotfour

end CFSG.Quasithin.Chapter13.Section08.LinearFour
