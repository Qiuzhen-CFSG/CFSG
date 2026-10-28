module

public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWSetup
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.BSWRecognition
public import CFSG.Quasithin.ChapterI.Section04To05.Dihedral.ExceptionalIsomorphisms
public import GorensteinWalter.Section4.PSL2ReflectedTorusCard
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Theory.GroupTheory.CentralizerSmallKernelTransport

/-!
# Recognition from an involution centralizer of order eight

The exact hypotheses of I.4.1 with `n = 3` give a Brauer–Suzuki–Wall
configuration whose rotation subgroup has order four. The existing recognition
theorem identifies the original group with `PSL₂(F)` for a finite odd field.
Its involution centralizer is a reflected torus: adjoining the external
involution doubles the torus order. Thus the torus has order four and `F`
has order seven or nine. The actual exceptional equivalences give `PSL₃(2)`
or `A₆`, without a simplicity hypothesis or prime-field restriction.

Source: Aschbacher–Smith, I.4.1(2), printed p.415 (PDF p.426).
The other cases of I.4.1 remain separate.
-/

public section
noncomputable section

namespace CFSG.Quasithin
open GorensteinWalter Subgroup

private theorem field_card_seven_or_nine_of_centralizer_eight
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) {t : PSL2 F}
    (ht : IsInvolution t)
    (hcard : Nat.card (centralizer ({t} : Set (PSL2 F))) = 8) :
    Nat.card F = 7 ∨ Nat.card F = 9 := by
  obtain ⟨T, s, _hcyclic, _htT, hs, hsout, hinv, hcentralizer, _heven, htorus⟩ :=
    psl2_reflected_torus_card hF ht
  have hnorm : s ∈ normalizer (T : Set (PSL2 F)) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hx
      change s * y * s⁻¹ ∈ T
      rw [hinv y hy]
      exact T.inv_mem hy
    · intro x hx
      refine mem_map.mpr ⟨x⁻¹, T.inv_mem hx, ?_⟩
      change s * x⁻¹ * s⁻¹ = x
      rw [hinv (x⁻¹) (T.inv_mem hx), inv_inv]
  have hdouble := card_sup_zpowers_of_normalizing_involution T s hs.2 hsout hnorm
  rw [← hcentralizer, hcard] at hdouble
  have hTcard : Nat.card T = 4 := by omega
  have hodd : Odd (Nat.card F) := by
    obtain ⟨p, n, _hp, hpodd, _hn, hq⟩ := hF
    rw [hq]
    exact hpodd.pow
  obtain ⟨k, hk⟩ := hodd
  rcases htorus with hminus | hplus
  · right
    omega
  · left
    omega

namespace DihedralInvolutionCentralizerHypotheses

/-- I.4.1(2), with the original group and the two actual model isomorphisms. -/
theorem recognize_eight {X : Type*} [Group X] [Finite X]
    (h : DihedralInvolutionCentralizerHypotheses X 3) :
    Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨b, _hbt, _hbH, hbK⟩ := h.exists_brauerSuzukiWallHypotheses
  have hbFour : 4 ≤ Nat.card b.K := by simpa using le_of_eq hbK.symm
  obtain ⟨F, hF, hFin, hOdd, ⟨e⟩⟩ :=
    exists_field_mulEquiv_psl2_of_bsw_four_le_card_K b hbFour
  let := hF
  let := hFin
  have ht : IsInvolution (e h.z) := by
    constructor
    · intro he
      apply h.involution.1
      apply e.injective
      simpa only [map_one] using he
    · simpa only [map_pow, map_one] using congrArg e h.involution.2
  have hcentralizer : Nat.card (centralizer ({e h.z} : Set (PSL2 F))) = 8 := by
    calc
      _ = Nat.card (centralizer ({h.z} : Set X)) :=
        (Nat.card_congr
          (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e h.z).toEquiv).symm
      _ = 8 := by simpa using h.centralizer_card
  rcases field_card_seven_or_nine_of_centralizer_eight hOdd ht hcentralizer with h7 | h9
  · exact Or.inl ⟨e.trans (psl2_equiv_psl3Two_of_card_seven h7).some⟩
  · exact Or.inr ⟨e.trans (psl2_equiv_alternatingSix_of_card_nine h9).some⟩

end DihedralInvolutionCentralizerHypotheses
end CFSG.Quasithin
