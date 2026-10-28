module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.PrimeRankCyclicSection
public import Theory.GroupTheory.PResidual.NormalizedGenerators

/-!
# The residual and three-rank steps of 15.4.23

The subgroup `P` in the alternate amalgam is an E₉, disjoint from `L`.
Its elements have odd order, so it lies in `O²(I′)`. The residual commutator
bound then makes `P` centralize `L/N`, where `N = O₂(L)` in the application.
The preceding cyclic-section theorem constructs rank three through the
coprime quotient. The contradiction uses the genuine SQTK rank bound.

Source: Aschbacher–Smith, Lemma 15.4.23, printed p.1165, PDF p.1182.
Both printed residuals in that paragraph are superscript `O²`, not `O₂`.

The ambient group in these lemmas is a rank-bounded local overgroup, such as
`N_G(O₂(L))`, not the ambient simple group. Constructing `P` and deriving the
residual bound from 15.4.21–22 remain obligations of the source assembly.
-/

namespace CFSG.Quasithin.Chapter15.Section04.Source

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The actual E₉ witness of 15.4.23 lies in the two-residual, so a residual
commutator bound produces rank three in the local overgroup. -/
public theorem three_rank_of_alternate_residual
    (N L I' P : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (hindex : N.relIndex L = 3) (hN : IsPGroup 2 N)
    [IsElementaryAbelian 3 P] (hPcard : Nat.card P = 9)
    (hPI : P ≤ I') (hdis : Disjoint L P)
    (hcomm : ⁅(pResidual 2 I').map I'.subtype, L⁆ ≤ N) :
    3 ≤ primeRank 3 G := by
  have hPres : P ≤ (pResidual 2 I').map I'.subtype := by
    intro x hx
    let y : I' := ⟨x, hPI hx⟩
    have hy : y ^ 3 = 1 := Subtype.ext (elemPow_eq_one_of_isElementaryAbelian x hx)
    have hc : Nat.Coprime 2 (orderOf y) :=
      Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hy) (by decide)
    exact ⟨y, mem_pResidual_of_orderOf_coprime hc, rfl⟩
  have hcop : Nat.Coprime 3 (Nat.card N) := by
    obtain ⟨n, hn⟩ := hN.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  exact primeRank_ge_of_centralized_cyclic_section N L P hNL hindex hcop
    (show Nat.card P = 3 ^ 2 from hPcard) hdis
    ((commutator_mono hPres le_rfl).trans hcomm)

/-- SQTK supplies the upper bound contradicted by the preceding construction. -/
public theorem no_alternate_E9_in_SQTK
    {κ : CFSG.Quasithin.GroupClass} (hG : CFSG.Quasithin.IsSQTK κ G)
    (N L I' P : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (hindex : N.relIndex L = 3) (hN : IsPGroup 2 N)
    [IsElementaryAbelian 3 P] (hPcard : Nat.card P = 9)
    (hPI : P ≤ I') (hdis : Disjoint L P)
    (hcomm : ⁅(pResidual 2 I').map I'.subtype, L⁆ ≤ N) : False := by
  have hlo := three_rank_of_alternate_residual N L I' P hNL hindex hN hPcard hPI hdis hcomm
  have hhi := hG.stronglyQuasithin 3 (by decide) (by decide)
  omega

/-- Conditional assembly of the last step of 15.4.23, using the genuine `F*`.
The residual bound must be proved from the first branch, and the E₉ witness
must be constructed from both alternatives for `I′`; neither is asserted here. -/
public theorem generalizedFitting_ne_twoCore_of_alternate
    {κ : CFSG.Quasithin.GroupClass} (hG : CFSG.Quasithin.IsSQTK κ G)
    (N L I I' : Subgroup G) [N.Normal]
    (hNL : N ≤ L) (hindex : N.relIndex L = 3) (hN : IsPGroup 2 N)
    (hbound : Theory.GroupTheory.generalizedFitting I = pCore 2 I →
      ⁅(pResidual 2 I').map I'.subtype, L⁆ ≤ N)
    (hP : ∃ P : Subgroup G, IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      P ≤ I' ∧ Disjoint L P) :
    Theory.GroupTheory.generalizedFitting I ≠ pCore 2 I := by
  intro hF
  obtain ⟨P, hPe, hPc, hPI, hd⟩ := hP
  let := hPe
  exact no_alternate_E9_in_SQTK hG N L I' P hNL hindex hN hPc hPI hd (hbound hF)

end CFSG.Quasithin.Chapter15.Section04.Source
