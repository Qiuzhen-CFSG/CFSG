module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Core
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalConstruction.Quotient
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.FusionConsequences

/-!
# Constructing the final moving conjugate from an S₃ overgroup

Given T≤H≤G₁ with H/O₂(H)≅S₃ and H escaping N_G(L), E.3.15 supplies
A=Vᵍ≤T outside the core. Its core intersection B has index two. The point
transporter gives A∩V₁=1, and the plane-span commutator bound and orbit count
show that B centralizes the plane span while that span normalizes A.

Normal generation in S₃ then produces an actual H-conjugate Aʰ moving V₂.
We transport the literal core intersection Bʰ=Aʰ∩O₂(H). It centralizes the
plane span and consequently normalizes V by 12.9.7.
The source's literal TerminalConfiguration is then constructed: since Aʰ≤G₁,
the TI normalizer bound M∩G₁≤N_G(V) rules out Aʰ≤M. The core hyperplane
lies in M, so its index two identifies it with Aʰ∩M. The existing Sylow
hyperplane transport and terminal commutator theorem supply the contradiction.
No normality of V in the whole of M is assumed.

The S₃ overgroup itself and the preceding component, local-control and
weak-closure results remain to be constructed by the natural-source owner.
This module completes the ensuing conjugate argument, not Theorem 12.9.1.
Source: Aschbacher--Smith, proof of 12.9.1, printed pp.863--864.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {X : Type u} [Group X] [Finite X]
variable {K : GroupClass.{u}} {T : Sylow 2 X} {L V : Subgroup X} {n : ℕ}

omit [Finite X] in
private theorem right_conjugate_mul (A : Subgroup X) (a b : X) :
    conjugate (conjugate A a) b = conjugate A (a * b) := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

/-- The actual moving conjugate and its transported core hyperplane. -/
theorem exists_moving_core_hyperplane
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (fusion : FusionControl T L V)
    (H : Subgroup X) (ht : (T : Subgroup X) ≤ H) (hH : H ≤ F.H)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ H ≤ normalizer (L : Set X)) :
    ∃ g : X, conjugate V g ≤ H ∧
      conjugateSpanBy (F.Vi 2) H ≤ normalizer (conjugate V g : Set X) ∧
      ¬ conjugate V g ≤ normalizer (F.Vi 2 : Set X) ∧
      (conjugate V g ⊓ H.pCoreIn 2).relIndex (conjugate V g) = 2 ∧
      conjugate V g ⊓ H.pCoreIn 2 ≤ centralizer (conjugateSpanBy (F.Vi 2) H : Set X) := by
  let := h.chosen.elementary
  obtain ⟨g, hgT, hgQ⟩ := exists_escaping_conjugate fusion H ht hout
  let A := conjugate V g
  let Q := H.pCoreIn 2
  let B := A ⊓ Q
  let U := conjugateSpanBy (F.Vi 2) H
  have hAH : A ≤ H := hgT.trans ht
  have hAp : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨hindex, hgen⟩ := core_hyperplane_and_generation H A hAH hAp he hgQ
  have hdis : A ⊓ F.Vi 1 = ⊥ := escaping_conjugate_disjoint_point h F hab H hH g hAH hgQ
  have hcomm : ⁅U,B⁆ ≤ F.Vi 1 :=
    (commutator_mono le_rfl inf_le_right).trans (plane_span_core_commutator h F H ht hH)
  have hUN : U ≤ normalizer (A : Set X) := plane_span_normalizes_conjugate h F hn
    (fun i hi hin => (control i hi hin).trans inf_le_right) H B g inf_le_left hindex hcomm
  have hBC : B ≤ centralizer (U : Set X) := by
    apply le_centralizer_iff.mp
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply bot_unique
    rw [← hdis]
    exact le_inf ((commutator_mono le_rfl inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp hUN)) hcomm
  have hQT : Q ≤ (T : Subgroup X) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht] using
      pCoreIn_le_sylow H (T.subtype ht)
  have hHP : ¬ H ≤ normalizer (F.Vi 2 : Set X) := by
    intro hh
    exact hout (hh.trans ((control 2 (by omega) (by have := h.rank; omega)).trans inf_le_left))
  obtain ⟨k, hk, hmove⟩ := exists_moving_conjugate_of_generation H A (F.Vi 2)
    hQT (F.invariant 2) hgen hHP
  let D := conjugate B k
  let A' := conjugate V (g * k)
  have hAk : conjugate A k = A' := right_conjugate_mul V g k
  have hUk : conjugate U k = U :=
    (conjugate_eq_iff _ _).mpr ((le_normalizer_conjugateSpanBy _ _) hk)
  have hQk : conjugate Q k = Q :=
    (conjugate_eq_iff _ _).mpr ((H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))) hk)
  have hHk : conjugate H k = H := (conjugate_eq_iff _ _).mpr (H.le_normalizer hk)
  have hA'H : A' ≤ H := hAk ▸ (map_mono hAH).trans_eq hHk
  have hD : D = A' ⊓ Q := by
    change (A ⊓ Q).map (MulAut.conj k⁻¹).toMonoidHom = _
    rw [map_inf _ _ _ (MulAut.conj k⁻¹).injective]
    exact congrArg₂ (· ⊓ ·) hAk hQk
  have hDi : D.relIndex A' = 2 := by
    rw [← hAk]
    change (B.map (MulAut.conj k⁻¹).toMonoidHom).relIndex
      (A.map (MulAut.conj k⁻¹).toMonoidHom) = 2
    rw [relIndex_map_map_of_injective _ _ (MulAut.conj k⁻¹).injective]
    exact hindex
  have hDC : D ≤ centralizer (U : Set X) := by
    have hc := (map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hBC).trans
      (map_centralizer_le_centralizer_image (U : Set X) (MulAut.conj k⁻¹).toMonoidHom)
    change D ≤ centralizer (conjugate U k : Set X) at hc
    rwa [hUk] at hc
  have hUN' : U ≤ normalizer (A' : Set X) := by
    have hh := map_mono (f := (MulAut.conj k⁻¹).toMonoidHom) hUN
    rw [map_equiv_normalizer_eq] at hh
    change conjugate U k ≤ normalizer (conjugate A k : Set X) at hh
    rwa [hUk, hAk] at hh
  have hmove' : ¬ A' ≤ normalizer (F.Vi 2 : Set X) := by rwa [hAk] at hmove
  have hDi' : (A' ⊓ Q).relIndex A' = 2 := hD ▸ hDi
  have hDC' : A' ⊓ Q ≤ centralizer (U : Set X) := hD ▸ hDC
  exact ⟨g * k, hA'H, hUN', hmove', hDi', hDC'⟩

omit [Finite X] in
private theorem hyperplane_eq_inf (D A M : Subgroup X) (hDA : D ≤ A) (hDM : D ≤ M)
    (hi : D.relIndex A = 2) (hne : ¬ A ≤ M) : D = A ⊓ M := by
  have hde : D ≤ A ⊓ M := le_inf hDA hDM
  have hc := relIndex_mul_relIndex D (A ⊓ M) A hde inf_le_left
  rw [hi] at hc
  have hp : (D.relIndex (A ⊓ M) * (A ⊓ M).relIndex A).Prime := hc ▸ Nat.prime_two
  rcases Nat.prime_mul_iff.mp hp with ⟨_, he⟩ | ⟨_, he⟩
  · exact (hne ((relIndex_eq_one.mp he).trans inf_le_right)).elim
  · exact le_antisymm hde (relIndex_eq_one.mp he)

/-- Construct the literal terminal configuration, including the intersection with M.
The point-normalizer bound from 12.2.6 identifies the transported core hyperplane.
The original V and the relative point normalizer remain unchanged. -/
theorem terminalConfiguration_of_symmetricThree
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (fusion : FusionControl T L V)
    (H : Subgroup X) (ht : (T : Subgroup X) ≤ H) (hH : H ≤ F.H)
    (hout : ¬ H ≤ normalizer (L : Set X))
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) :
    Nonempty (TerminalConfiguration F L) := by
  let := h.chosen.elementary
  obtain ⟨g, hAH, hUN, hmove, hindex, hBC⟩ :=
    exists_moving_core_hyperplane h hn F hab control fusion H ht hH ⟨e⟩ hout
  let A := conjugate V g
  let B := A ⊓ H.pCoreIn 2
  have hBM : B ≤ normalizer (L : Set X) :=
    (hBC.trans ((centralizer_le (le_conjugateSpanBy (F.Vi 2) H)).trans
      (Subgroup.centralizer_le_normalizer _))).trans
      ((control 2 (by omega) (by have := h.rank; omega)).trans inf_le_left)
  have hMN : normalizer (L : Set X) ⊓ F.H ≤ normalizer (V : Set X) :=
    (h.flag_normalizer_le earlier.structural F (by omega : 1 ≤ 1)
      (by have := h.rank; omega)).trans inf_le_right
  have hnotM : ¬ A ≤ normalizer (L : Set X) := by
    intro haM
    have haN : A ≤ normalizer (V : Set X) :=
      (le_inf haM (hAH.trans hH)).trans hMN
    have haC : A ≤ centralizer (V : Set X) :=
      (ChapterE.conjugate_normalization_equivalences_of_weakClosure_zero
        (h.sylow_normalizes_seed earlier.structural) fusion.weakClosure_centralizes g⁻¹).1.mp haN
    exact hmove (haC.trans ((centralizer_le (F.le_seed 2)).trans
      (Subgroup.centralizer_le_normalizer _)))
  have hd : B = A ⊓ normalizer (L : Set X) :=
    hyperplane_eq_inf B A _ inf_le_left hBM hindex hnotM
  refine ⟨{ H := H
            sylow_le := ht
            point_le := hH
            quotient := ⟨e⟩
            g := g
            conjugate_le := hAH
            span_normalizes := hUN
            moves_plane := hmove
            hyperplane_normalizes := ?_
            hyperplane_index := ?_ }⟩
  · exact (le_inf inf_le_right (inf_le_left.trans (hAH.trans hH))).trans hMN
  · change (A ⊓ normalizer (L : Set X)).relIndex A = 2
    rw [← hd]
    exact hindex

/-- The final source contradiction, conditional only on the preceding stages and H. -/
theorem contradiction_of_symmetric_three_overgroup
    (h : HigherRankHypothesis K T L V n) (hn : n = 4 ∨ n = 5)
    (earlier : EarlierSetupResults K) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U)
    (control : ∀ i, 1 < i → i < n →
      F.Gi i ≤ seedNormalizer (normalizer (L : Set X)) V)
    (fusion : FusionControl T L V)
    (H : Subgroup X) (ht : (T : Subgroup X) ≤ H) (hH : H ≤ F.H)
    (he : Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)))
    (hout : ¬ H ≤ normalizer (L : Set X)) : False := by
  obtain ⟨e⟩ := he
  obtain ⟨d⟩ := terminalConfiguration_of_symmetricThree h hn earlier F hab control
    fusion H ht hH hout e
  exact terminal_contradiction_of_sylow_hyperplanes h earlier F hab fusion.hyperplanes
    d.H d.point_le d.g d.conjugate_le d.span_normalizes d.moves_plane
    d.hyperplane_normalizes d.hyperplane_index

/-- The remaining overgroup construction in the first sentence of the final proof.
Its discharge, along with the earlier local stages, stays with
`qt-d-1291-natural-source`. It contains no moving-conjugate conclusion. -/
def SymmetricThreeOvergroupInput (K : GroupClass.{u}) : Prop :=
  ∀ (X : Type u) [Group X] [Finite X] (T : Sylow 2 X) (L V : Subgroup X) (n : ℕ),
    HigherRankHypothesis K T L V n → n = 4 ∨ n = 5 → EarlierSetupResults K →
    ∀ F : InvariantFlag T V n, IsMulCommutative F.U →
    ∀ C : ComponentGeometry F L, LocalControl C →
      ∃ H : Subgroup X, (T : Subgroup X) ≤ H ∧ H ≤ C.K1 ⊔ (T : Subgroup X) ∧
        Nonempty ((H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 3)) ∧
        ¬ H ≤ normalizer (L : Set X)

/-- Discharge the full terminal input from the remaining S₃-overgroup selection. -/
theorem terminalInput_of_symmetricThreeOvergroups
    (source : SymmetricThreeOvergroupInput K) : TerminalInput K := by
  intro X _ _ T L V n h hn earlier F hab C localControl fusion
  obtain ⟨H, ht, hHK, ⟨e⟩, hout⟩ := source X T L V n h hn earlier F hab C localControl
  exact terminalConfiguration_of_symmetricThree h hn earlier F hab localControl.normalizers
    fusion H ht (hHK.trans localControl.overgroup.2.1) hout e

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
