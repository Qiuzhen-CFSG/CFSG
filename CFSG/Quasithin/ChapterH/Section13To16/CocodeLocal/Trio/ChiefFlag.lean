module

public import CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal.Trio.Calculation

/-!
# H.15.6: the complete native trio cocode flag

The three irreducible section actions give covers in the lattice of invariant
subspaces for the actual trio stabilizer. Together with the proved dimensions,
both intrinsic commutator identities, full lower and upper action images, and
the equivariant natural tensor identification, this assembles all clauses of
H.15.6 for every native trio without additional hypotheses.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.15.6,
printed p.401 (PDF p.412), with H.14.1(3), printed p.396. The printed V₉/V
in clause (3) must read V₉/V₃, as required by the strict flag.
-/

public section
open Representation Representation.BinaryOffender
open MathieuCode Sporadic.Mathieu Sporadic.Mathieu.M24LocalGeometry.PairOvergroups
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
noncomputable section
open MathieuCode.TrioCalculation

theorem trioFlag_strict (T : Trio) :
    (⊥ : Submodule (ZMod 2) Cocode) < trioFixedSpace T ∧
      trioFixedSpace T < trioPairSpace T ∧ trioPairSpace T < ⊤ := by
  refine ⟨?_, ?_, (trioPairSpace_strict T).2⟩
  · refine bot_lt_iff_ne_bot.mpr ?_
    intro h
    have hd := finrank_trioFixedSpace T
    rw [h, finrank_bot] at hd
    omega
  · refine lt_iff_le_and_ne.mpr ⟨trioFixedSpace_le_trioPairSpace T, ?_⟩
    intro h
    have hd := finrank_trioFixedSpace T
    rw [h, finrank_trioPairSpace] at hd
    omega

theorem finrank_trioSection (T : Trio) : Module.finrank (ZMod 2) (TrioSection T) = 6 := by
  rw [(trioSectionEquiv T).finrank_eq]
  rw [Module.finrank_tensorProduct, Module.finrank_fin_fun, BinaryPermutation.finrank_core]
  norm_num

/-- Covers in the actual stabilizer-invariant subspace lattice. -/
theorem trioFlag_chief (T : Trio) :
    (⊥ : Subrepresentation (trioRepresentation T)) ⋖ trioFixedSubrepresentation T ∧
      trioFixedSubrepresentation T ⋖ trioPairSubrepresentation T ∧
      trioPairSubrepresentation T ⋖ ⊤ := by
  have hs := trioFlag_strict T
  refine ⟨bot_covBy_iff.mpr ((Subrepresentation.irreducible_iff_isAtom _).mp
    (trioFixed_irreducible T)), ?_, ?_⟩
  · refine ⟨(show trioFixedSubrepresentation T < trioPairSubrepresentation T from hs.2.1), ?_⟩
    intro P hAP hPB
    let N := trioSectionKernel T
    let W : Subrepresentation (trioPairSubrepresentation T).toRepresentation :=
      { toSubmodule := P.toSubmodule.comap (trioPairSpace T).subtype
        apply_mem_toSubmodule g _ hv := P.apply_mem_toSubmodule g hv }
    have hNW : N ≤ W := fun _ hv => hAP.le hv
    let : IsIrreducible N.quotientRepresentation := trioSection_irreducible T
    rcases N.le_or_sup_eq_top_of_irreducible_quotient W with hw | hw
    · have hPA : P ≤ trioFixedSubrepresentation T := by
        intro v hv
        exact hw (show (⟨v, hPB.le hv⟩ : trioPairSpace T) ∈ W from hv)
      exact (not_le_of_gt hAP) hPA
    · have hWtop : W.toSubmodule = ⊤ := by
        rwa [sup_eq_right.mpr (show N.toSubmodule ≤ W.toSubmodule from hNW)] at hw
      have hBP : trioPairSubrepresentation T ≤ P := by
        intro v hv
        have hm : (⟨v, hv⟩ : trioPairSpace T) ∈ W.toSubmodule := by rw [hWtop]; trivial
        exact hm
      exact (not_le_of_gt hPB) hBP
  · refine ⟨(show trioPairSubrepresentation T < ⊤ from hs.2.2), ?_⟩
    intro P hAP hPB
    let : IsIrreducible (trioPairSubrepresentation T).quotientRepresentation := trioTop_irreducible T
    rcases (trioPairSubrepresentation T).le_or_sup_eq_top_of_irreducible_quotient P with hp | hp
    · exact (not_le_of_gt hAP) hp
    · have hPtop : P = ⊤ := by
        apply Subrepresentation.toSubmodule_injective
        rwa [sup_eq_right.mpr (show (trioPairSubrepresentation T).toSubmodule ≤ P.toSubmodule from hAP.le)] at hp
      exact (ne_of_lt hPB) hPtop

/-- The mapped kernel is the intrinsic two-core when regarded inside its stabilizer. -/
theorem trioKernel_subgroupOf (T : Trio) :
    (trioKernel T).subgroupOf (trioStabilizer T) = pCore 2 (trioStabilizer T) := by
  change ((pCore 2 (trioStabilizer T)).map (trioStabilizer T).subtype).comap
    (trioStabilizer T).subtype = _
  exact Subgroup.comap_map_eq_self_of_injective (trioStabilizer T).subtype_injective _

/-- H.15.6(1–3), with the printed middle-section denominator corrected to V₃.
Every assertion concerns the native cocode and its actual intrinsic local groups. -/
theorem source_lemma_H_15_6 (T : Trio) :
    ((⊥ : Subrepresentation (trioRepresentation T)) ⋖ trioFixedSubrepresentation T ∧
      trioFixedSubrepresentation T ⋖ trioPairSubrepresentation T ∧
      trioPairSubrepresentation T ⋖ ⊤) ∧
    (Module.finrank (ZMod 2) (trioFixedSpace T) = 3 ∧
      Module.finrank (ZMod 2) (trioPairSpace T) = 9 ∧
      Module.finrank (ZMod 2) Cocode = 11 ∧
      Module.finrank (ZMod 2) (Cocode ⧸ trioPairSpace T) = 2) ∧
    (trioPairSpace T = subspaceCommutator cocodeRepresentation ⊤ (trioKernel T) ∧
      trioPairSpace T = subspaceCommutator cocodeRepresentation ⊤ (trioResidual T)) ∧
    (Function.Surjective (trioFixedSubrepresentation T).toRepresentation.asGroupHom ∧
      Function.Surjective (trioTopRepresentation T).asGroupHom) ∧
    ∃ q : (trioStabilizer T ⧸ pCore 2 (trioStabilizer T)) ≃* SourceQuotientModel,
      ∃ e : TrioSection T ≃ₗ[ZMod 2] NaturalTensor,
        ∀ (h : trioStabilizer T) (v : TrioSection T),
          e (trioSectionRepresentation T h v) =
            sourceTensorRepresentation (q (QuotientGroup.mk h)) (e v) := by
  exact ⟨trioFlag_chief T,
    ⟨finrank_trioFixedSpace T, finrank_trioPairSpace T, finrank_cocode, finrank_trioPairQuotient T⟩,
    ⟨trioPairSpace_eq_kernel_commutator T, trioPairSpace_eq_residual_commutator T⟩,
    ⟨trioFixedSubrepresentation_surjective T, trioTopRepresentation_surjective T⟩,
    trioSourceQuotientEquiv T, trioSectionEquiv T, trioSectionEquiv_source_intertwines T⟩
end
end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
