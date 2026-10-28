module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.MarkedAction
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Basic
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource.Hypothesis1311
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.ChosenSimpleAction
/-!
# Reduction (a) on the original unitary flag

One natural marking identifies the original Sylow-invariant point, plane
and three-space. The point parabolic is irreducible on the three-space
modulo the point, so its orbit of the plane generates that three-space.
If the original point-normalizer core centralizes the plane, characteristic
two puts the entire conjugate span in the omega-center of that same core.
No F.9 applicability or later Chapter 14 hypothesis is assumed.

The two normalizer inputs are the earlier 12.2 conclusions, supplied by
`unitary_original_module_normalizers` in the source application.
Source: Aschbacher--Smith, Lemma 13.3.14(a), printed p.891.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterE Atlas.G2.Natural.BinaryPointFlag
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {G : Type*} [Group G] [Finite G]
/-- The genuine unitary flag proves reduction (a); the two normalizer
premises are the earlier chosen-module conclusions of 12.2. -/
theorem unitary_flag_reduction_a
    (D : ChapterF.Section09.Setup G) [IsElementaryAbelian 2 D.V]
    (h : Hypothesis1331 D.T D.L) (chosen : ChosenModule D.T D.L D.V)
    (hTN : (D.T : Subgroup G) ≤ normalizer (D.V : Set G))
    (hNL : normalizer (D.V : Set G) ≤ normalizer (D.L : Set G))
    (e : inducedAutomizer D.V D.L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive D.V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer D.V D.L) v,
      E0 (automizerRepresentation D.V l v) =
        Atlas.G2.Natural.derivedAction F (e l) (E0 v))
    (hUV : D.Vplus ≤ D.V) (hZV : D.V₁ ≤ D.V)
    (hTZ : (D.T : Subgroup G) ≤ normalizer (D.V₁ : Set G))
    (hTU : (D.T : Subgroup G) ≤ normalizer (D.Vplus : Set G))
    (hZ : Nat.card D.V₁ = 2) (hU : Nat.card D.Vplus = 8)
    (B : Subgroup G) (hBV : B ≤ D.V)
    (hTB : (D.T : Subgroup G) ≤ normalizer (B : Set G)) (hB : Nat.card B = 4)
    (hHfull : D.H = normalizer (D.V₁ : Set G))
    (hc : ⁅D.QH,B⁆ = ⊥) :
    D.UH = conjugateSpanBy B D.H ∧
      D.UH ≤ Stellmacher.omegaOneCenterAmbient D.QH := by
  obtain ⟨rho,E,he,ht,hd,hz,hp,hs⟩ := exists_unitary_flag_marking D.T D.L D.V₁ B D.Vplus
    chosen.normalizes hNL e E0 he0 hTN hZV hBV hUV hTZ hTB hTU hZ hB hU
  have hTH : (D.T : Subgroup G) ≤ D.H := hHfull ▸ hTZ
  have hTC : (D.T : Subgroup G) ≤ centralizer (D.V₁ : Set G) :=
    hTZ.trans (normalizer_le_centralizer_of_card_two D.V₁ hZ)
  have hL1 : D.L₁ ≤ D.L ⊓ centralizer (D.V₁ : Set G) := map_subtype_le _
  let J : Subgroup G := D.L₁ ⊔ (D.T : Subgroup G)
  have hJC : J ≤ centralizer (D.V₁ : Set G) := sup_le (hL1.trans inf_le_right) hTC
  have hJH : J ≤ D.H := by
    rw [hHfull]
    exact hJC.trans (Subgroup.centralizer_le_normalizer _)
  have hJN : J ≤ normalizer (D.V : Set G) :=
    sup_le ((hL1.trans inf_le_left).trans chosen.normalizes) hTN
  have hJU : J ≤ normalizer (D.Vplus : Set G) :=
    point_centralizer_normalizes_marked_seed D.Vplus D.V₁ J rho E he hs hz hUV hJN hJC
  have hP : Atlas.G2.BinaryParabolicPair.derivedSecondAmbient ≤
      (inducedAutomizer D.V J).map rho :=
    source_point_parabolic_covered D.T D.L D.V₁ rho E he hz hZV hTC
      chosen.sylow_normalizes_component hd
  have hZB : D.V₁ ≤ B := marked_point_le_plane D.V₁ B E hz hp hZV
  have hBU : B ≤ D.Vplus := by
    intro b hb
    let v : Additive D.V := Additive.ofMul ⟨b,hBV hb⟩
    have hv : E v ∈ plane := hp ▸ (mem_pointCoordinateSubspace E B v).mpr hb
    exact (mem_pointCoordinateSubspace E D.Vplus v).mp (hs.symm ▸ plane_le_seed hv)
  have hspan : D.Vplus = conjugateSpanBy B J := by
    let S := conjugateSpanBy B J
    have hBS : B ≤ S := le_conjugateSpanBy B J
    have hSU : S ≤ D.Vplus := conjugateSpanBy_le hBU hJU
    have hh := point_seed_irreducible D.Vplus D.V₁ J rho E he hs hz hUV hP S
      (hZB.trans hBS) hSU (le_normalizer_conjugateSpanBy B J)
    rcases hh with hzS | huS
    · have hBZ : B ≤ D.V₁ := hBS.trans_eq hzS
      have hc' : Nat.card B ≤ Nat.card D.V₁ :=
        Nat.card_le_card_of_injective (inclusion hBZ) (inclusion_injective hBZ)
      omega
    · exact huS.symm
  have hZn : D.V₁ ≠ ⊥ := D.V₁.one_lt_card_iff_ne_bot.mp (by omega)
  have hH : D.H ∈ Chapter1.He G := by
    rw [hHfull]
    exact Chapter1.twoLocal_mem_He_of_sylow_le D.T (h.qtke.evenCharacteristic D.T)
      ⟨D.V₁,hZn,(IsElementaryAbelian.isPGroup 2 D.V).to_le hZV,rfl⟩ hTZ
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBV
  apply Noncentrality.reduction_a B D.Vplus J D.H
    (hBV.trans (chosen.le_sylow.trans hTH)) hJH hspan hH
  rwa [commutator_comm]
end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
