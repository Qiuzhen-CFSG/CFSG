module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.TerminalGeometry
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.AbelianClauses
public import Theory.GroupTheory.Commutator.RelativeGeneration
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.ConjugateSpanSylow
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The escaping seed conjugate and the plane-span core

E.3.15 and the weak-closure normalizer bound produce a conjugate A≤T escaping
O₂(H). The flag transporter and the abelian point span force A∩V₁=1.

The two-core of H lies in T and acts trivially on V₂/V₁, of order two.
Relative normality propagates [V₂,O₂(H)]≤V₁ through the H-conjugate span.
These calculations use only H≤G₁ and T≤H, without a Chapter G action certificate.

Source: Aschbacher--Smith, final proof of 12.9.1, printed pp.863--864.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource
open Section02 Section08 Section08.InvariantFlag
universe u
variable {X : Type u} [Group X] [Finite X]
variable {K : GroupClass.{u}} {T : Sylow 2 X} {L V : Subgroup X} {n : ℕ}

omit [Finite X] in
private theorem core_le_sylow {H : Subgroup X} (ht : (T : Subgroup X) ≤ H) :
    H.pCoreIn 2 ≤ (T : Subgroup X) := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht] using
    pCoreIn_le_sylow H (T.subtype ht)

omit [Finite X] in
private theorem core_normalized (H : Subgroup X) :
    H ≤ normalizer (H.pCoreIn 2 : Set X) :=
  H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))

/-- E.3.15 supplies a whole seed conjugate escaping the actual two-core. -/
theorem exists_escaping_conjugate
    (fusion : FusionControl T L V)
    (H : Subgroup X) (ht : (T : Subgroup X) ≤ H)
    (hout : ¬ H ≤ normalizer (L : Set X)) :
    ∃ g : X, conjugate V g ≤ (T : Subgroup X) ∧
      ¬ conjugate V g ≤ H.pCoreIn 2 := by
  apply exists_conjugate_escaping_of_weakClosure
  intro hw
  have hw' : ChapterE.indexedWeakClosure V
      ((T.subtype ht : Subgroup H).map H.subtype) 0 ≤ H.pCoreIn 2 := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht] using hw
  have hN := ChapterE.normalizer_le_weakClosure_normalizer_of_two_overgroup
    V H (T.subtype ht) (H.pCoreIn 2) 0 (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H) hw'
  have hNM : normalizer (H.pCoreIn 2 : Set X) ≤ normalizer (L : Set X) := by
    apply hN.trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le ht] using fusion.weakClosure_normalizer
  exact hout ((core_normalized H).trans hNM)

/-- A seed conjugate outside the core cannot contain the flag point. -/
theorem escaping_conjugate_disjoint_point
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (hab : IsMulCommutative F.U) (H : Subgroup X) (hH : H ≤ F.H)
    (g : X) (hAH : conjugate V g ≤ H) (hout : ¬ conjugate V g ≤ H.pCoreIn 2) :
    conjugate V g ⊓ F.Vi 1 = ⊥ := by
  let := h.chosen.elementary
  let : IsMulCommutative (conjugateSpanBy V F.H) := hab
  have hUp : IsPGroup 2 F.U :=
    (conjugateSpanBy_elementary_of_commutative V F.H).isPGroup
  have hNH : H ≤ normalizer (F.U ⊓ H : Set X) :=
    (le_inf (hH.trans (le_normalizer_conjugateSpanBy V F.H)) H.le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hcore : F.U ⊓ H ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (hUp.to_le inf_le_left) inf_le_right hNH
  by_contra he
  have hp : F.Vi 1 ≤ conjugate V g :=
    (F.point_inf_ne_bot_iff (by have := h.rank; omega) _).mp (by rwa [inf_comm])
  obtain ⟨k, hk, heq⟩ := h.flag_transporter F 1 g hp
  have hAU : conjugate V g ≤ F.U := by
    rw [heq]
    rintro x ⟨v, hv, rfl⟩
    exact subset_closure ⟨k⁻¹, F.H.inv_mem hk, v, hv, rfl⟩
  exact hout ((le_inf hAU hAH).trans hcore)

/-- The core acts trivially on the plane span modulo the original point. -/
theorem plane_span_core_commutator
    (h : HigherRankHypothesis K T L V n) (F : InvariantFlag T V n)
    (H : Subgroup X) (ht : (T : Subgroup X) ≤ H) (hH : H ≤ F.H) :
    ⁅conjugateSpanBy (F.Vi 2) H, H.pCoreIn 2⁆ ≤ F.Vi 1 := by
  have hp : F.Vi 1 ≤ F.Vi 2 := F.monotone (by omega)
  have hi : (F.Vi 1).relIndex (F.Vi 2) = 2 := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup X) (F.Vi 1) (F.Vi 2) bot_le hp
    simp only [relIndex_bot_left] at hh
    rw [F.card 1 (by have := h.rank; omega), F.card 2 (by have := h.rank; omega)] at hh
    norm_num at hh
    omega
  have hseed : ⁅F.Vi 2, H.pCoreIn 2⁆ ≤ F.Vi 1 :=
    commutator_le_of_normalized_index_two _ _ _ hp hi
      ((core_le_sylow ht).trans (F.invariant 2))
      ((core_le_sylow ht).trans (F.invariant 1))
  have hplane : F.Vi 2 ≤ H := ((F.le_seed 2).trans h.chosen.le_sylow).trans ht
  rw [conjugateSpanBy_eq_iSup_conj]
  apply commutator_iSup_le_of_relative_normal H (H.pCoreIn 2) (F.Vi 1) _ hH
  · intro j
    exact (map_mono hplane).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer j.property))
  · intro j
    have hh := map_mono (f := (MulAut.conj (j : X)).toMonoidHom) hseed
    have heQ : (H.pCoreIn 2).map (MulAut.conj (j : X)).toMonoidHom = H.pCoreIn 2 :=
      mem_normalizer_iff_map_conj_eq.mp ((core_normalized H) j.property)
    have heZ : (F.Vi 1).map (MulAut.conj (j : X)).toMonoidHom = F.Vi 1 :=
      mem_normalizer_iff_map_conj_eq.mp (hH j.property)
    rwa [map_commutator, heQ, heZ] at hh

end CFSG.Quasithin.Chapter12.Section09.NaturalSource
