module

public import CFSG.Quasithin.Chapter12.Section05.NaturalSource.Local.Completion

/-!
# The actual escaping conjugate in the terminal exterior argument

For an original H-star member, E.3.15 and the proved normalizer bound for
W₀ force a whole conjugate of V in T outside O₂(H). The same original
H-span of V₇ is elementary abelian, and its two-residual acts nontrivially
on that span. No escaping-conjugate or rank premise is supplied.

Source: Aschbacher--Smith, proof of 12.5.1, printed p.822. Selection of H
inside the centralizer-modulo-core supplement, its quotient and the
faithful-action bound remain with the final source assembly.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section05.NaturalSource
open Section02 ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V}

namespace SylowExteriorMarking
variable (s : SylowExteriorMarking D)
  (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
  (structural : Structural1222At KnownSimple.IsKnownSimple T)

include h structural

/-- E.3.15 at the original H and the original full Sylow T. -/
theorem weakClosure_not_le_HStar_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ H.pCoreIn 2 := by
  intro hW
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hnorm := normalizer_le_weakClosure_normalizer_of_two_overgroup V H
    (T.subtype hTH) (H.pCoreIn 2) 0 (isPGroup_pCoreIn 2 H) (pCoreIn_le 2 H)
    (by simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using hW)
  simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at hnorm
  have hHN : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  exact hH.1.2 (hHN.trans (hnorm.trans
    (s.exteriorFusion_from_source h structural).zero_normalizer))

/-- Select an actual whole conjugate, retaining both its Sylow placement and
its membership in the original weak closure. -/
theorem exists_conjugate_escaping_HStar_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ∃ g : G, V.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) ∧
      V.map (MulAut.conj g).toMonoidHom ≤ indexedWeakClosure V (T : Subgroup G) 0 ∧
      V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) ∧
      ¬ V.map (MulAut.conj g).toMonoidHom ≤ H.pCoreIn 2 := by
  have hex : ∃ A ∈ gamma V (T : Subgroup G) 0, ¬ A ≤ H.pCoreIn 2 := by
    by_contra! hn
    apply s.weakClosure_not_le_HStar_core h structural hH
    rw [weakClosure_eq_sSup_gamma]
    exact sSup_le hn
  obtain ⟨A, hA, hcore⟩ := hex
  obtain ⟨g, rfl, hAT⟩ := (mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
  have hAW := gamma_le_weakClosure hA
  exact ⟨g, hAT, hAW, hAW.trans
    ((s.exteriorFusion_from_source h structural).zero_centralizes.trans inf_le_right), hcore⟩

/-- The source span U_H is elementary because it lies in the original
elementary point span U, with the same H ≤ G₁. -/
theorem HStar_span_elementary {H : Subgroup G} (hHG : H ≤ s.marking.Gi 1) :
    IsElementaryAbelian 2 (s.marking.UH H) := by
  let := (s.exteriorFusion_from_source h structural).elementary_span
  exact IsElementaryAbelian.of_le (s.marking.UH_le_U hHG)

/-- In particular, the original H-span lies in its actual two-core. -/
theorem HStar_span_le_core {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M)
    (hHG : H ≤ s.marking.Gi 1) : s.marking.UH H ≤ H.pCoreIn 2 := by
  let := s.HStar_span_elementary h structural hHG
  exact le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 (s.marking.UH H))
    (conjugateSpanBy_le_self ((s.marking.subspace_le _).trans (D.le_sylow.trans hH.1.1.2)))
    (le_normalizer_conjugateSpanBy _ _)

/-- The literal two-residual cannot lie in M, since it supplements T in H. -/
theorem HStar_residual_not_le_M {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ¬ (pResidual 2 H).map H.subtype ≤ s.marking.M := by
  intro hK
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have he := congrArg (map H.subtype) (pResidual_sup_sylow_eq_top (T.subtype hTH))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype,
    Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] at he
  apply hH.1.2
  rw [← he]
  exact sup_le hK (structural L h).1

/-- The source uses V₃ ≤ V₇ and G₃ ≤ M to show [U_H,O²(H)] ≠ 1. -/
theorem HStar_residual_not_centralizing_span {H : Subgroup G}
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) s.marking.M) :
    ¬ (pResidual 2 H).map H.subtype ≤ centralizer (s.marking.UH H : Set G) := by
  intro hc
  apply s.HStar_residual_not_le_M h structural hH
  have h37 : s.marking.Vi 3 ≤ s.marking.Vi 7 := by
    apply s.marking.subspace_mono
    apply Submodule.span_mono
    apply Set.image_mono
    intro j hj
    simpa only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] using
      (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 from by
        simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl <;> simp)
  exact hc.trans ((centralizer_le (h37.trans (le_conjugateSpanBy _ _))).trans
    ((Subgroup.centralizer_le_normalizer _).trans
      (s.local_normalizer_le_M_from_source h 3 (.inl rfl))))

end SylowExteriorMarking
end CFSG.Quasithin.Chapter12.Section05.NaturalSource
