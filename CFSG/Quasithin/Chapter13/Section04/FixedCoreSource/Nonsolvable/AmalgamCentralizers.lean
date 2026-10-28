module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.SmallQuotientParabolics

/-!
# Relative centralizers for the nonsolvable parabolic amalgam

A maximal parabolic P of C_G(z) remains the entire z-centralizer in an
overgroup X of the amalgam with nontrivial two-core. Otherwise X contains
both C_G(z) and the other inside parabolic, hence M; maximal two-locality
forces X into M, contradicting P's escape. The marked fixed-line calculation
then identifies C_X(C_Z(O²(P))) with P. The quotient-row index calculation
proves the source O^{3′} identity in this literal relative centralizer.

The comparison application also derives four-choice solvability from the
recognized centralizer, removing that premise from the normalizer argument.
The component and quotient recognition, full central seed, noncentral chief
factor bounds, the second parabolic's applicability and resulting 13.4.7
alternatives remain with qt-d-1341-nonsolvable-source. The conditional
comparison is not a proof of 13.4.12. Earlier local inputs and final ambient
recognition retain discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith 13.4.10(8) and 13.4.12, pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

omit [Finite G] in
private theorem overgroup_le_maximal (M X : Subgroup G)
    (hM : IsMaximalTwoLocal M) (hX : X ∈ Chapter1.H G) (hMX : M ≤ X) : X ≤ M := by
  have hn : X ≤ normalizer (X.pCoreIn 2 : Set G) := by
    simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
      (pCore 2 X).le_normalizer_map X.subtype
  exact hn.trans (hM.2 ⟨X.pCoreIn 2, hX, isPGroup_pCoreIn 2 X, rfl⟩ (hMX.trans hn))

/-- The centralizer in every overgroup of the amalgam with nontrivial two-core is exactly
the selected parabolic. The proof uses maximality relative to C_G(z) and
the actual generating inside pair in M. -/
theorem parabolic_centralizer_in_overgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A B P : Subgroup G) (z : G)
    (hAC : A ≤ centralizer ({z} : Set G))
    (hgen : A ⊔ B = normalizer (L : Set G))
    (hmax : P ⋖ centralizer ({z} : Set G))
    (hPM : ¬ P ≤ normalizer (L : Set G))
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    X ⊓ centralizer ({z} : Set G) = P ∧
      X ⊓ centralizer ({z} : Set G) ≤
        normalizer ((pResidual 2 P).map P.subtype : Set G) := by
  have he : X ⊓ centralizer ({z} : Set G) = P := by
    rcases hmax.eq_or_eq (le_inf hPX hmax.le) inf_le_right with he | he
    · exact he
    · have hCX : centralizer ({z} : Set G) ≤ X := he ▸ inf_le_left
      have hMX : normalizer (L : Set G) ≤ X := hgen ▸ sup_le (hAC.trans hCX) hBX
      have hXM := overgroup_le_maximal _ X
        (h.source_normalizer_maximal_unique structural
          (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
          (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)).1 hX hMX
      exact (hPM (hPX.trans hXM)).elim
  exact ⟨he, he ▸ le_normalizer_embedded_pResidual 2 P⟩

/-- The fixed-line and parabolic calculations give the literal residual
normality premise of 13.4.7(c). Full Ω₁Z(T) containment is the still separate
13.4.10(5) obligation, not inferred from its four-element intersection with V. -/
theorem escaping_residual_relative_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hZV : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (A B P : Subgroup G)
    (hAC : A ≤ centralizer ({z.val} : Set G))
    (hgen : A ⊔ B = normalizer (L : Set G))
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hmax : P ⋖ centralizer ({z.val} : Set G))
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    X ⊓ centralizer ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G) : Subgroup G) : Set G) = P ∧
    (((pResidual 2 P).map P.subtype).subgroupOf
      (X ⊓ centralizer ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G) : Subgroup G) : Set G))).Normal := by
  have hline := escaping_residual_fixed_line h structural m z hz1 hzT P hP hmax.le
  rw [inf_eq_right.mpr hZV] at hline
  have hc : centralizer (zpowers z.val : Set G) = centralizer ({z.val} : Set G) := by
    rw [zpowers_eq_closure, centralizer_closure]
  rw [hline, hc]
  have he := parabolic_centralizer_in_overgroup h structural A B P z.val hAC hgen
    hmax hP.1.2 X hX hPX hBX
  refine ⟨he.1, ?_⟩
  apply (normal_subgroupOf_iff_le_normalizer ?_).mpr he.2
  rw [he.1]
  exact map_subtype_le _

/-- The original prime-to-three residual in 13.4.7(c), with its inclusion
into G. Index three proves that the parabolic is a {2,3}-group, so the
previous centralizer equality identifies its prime-to-three residual with
its two-residual. -/
theorem escaping_cubic_residual_in_overgroup
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hZV : Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ≤ V)
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (A B P : Subgroup G)
    (hAC : A ≤ centralizer ({z.val} : Set G))
    (hgen : A ⊔ B = normalizer (L : Set G))
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPC : P < centralizer ({z.val} : Set G))
    (model : Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* Equiv.Perm (Fin 6)))
    (X : Subgroup G) (hX : X ∈ Chapter1.H G) (hPX : P ≤ X) (hBX : B ≤ X) :
    let C := X ⊓ centralizer ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer ((pResidual 2 P).map P.subtype : Set G) : Subgroup G) : Set G)
    (((pResidual 2 P).map P.subtype).subgroupOf C).Normal ∧
      (primeToResidual 3 C).map C.subtype = (pResidual 2 P).map P.subtype := by
  dsimp only
  have hTP : (T : Subgroup G) < P := lt_of_le_of_ne hP.1.1.2 (by
    intro he
    exact hP.1.2 (he ▸ D.sylow_normalizes_component))
  have hmax := small_quotient_parabolic_maximal _ P hTP hPC model
  have hi := small_quotient_parabolic_index _ P hTP hPC model
  have he := escaping_residual_relative_centralizer h structural m z hz1 hzT hZV
    A B P hAC hgen hP hmax X hX hPX hBX
  refine ⟨he.2, ?_⟩
  rw [he.1, ← (escaping_parabolic_quotient_and_residual P hP hNT hi).2]

/-- Apply the literal parabolic comparison after deriving four-choice solvability
from its recognized centralizer. The quotient recognition and the two source
amalgam alternatives still require construction by this nonsolvable owner. -/
theorem false_of_small_centralizer_comparison
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (L₂ P₂ P₄ : Subgroup G) (hL₂ : L₂ ≤ L)
    (z w : V) (hz : m.weight z = 2) (hw : m.weight w = 4)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hwT : w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hP₂ : P₂ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP₄ : P₄ ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hP₂z : P₂ ≤ centralizer ({z.val} : Set G))
    (hP₄w : P₄ ≤ centralizer ({w.val} : Set G))
    (hP₂N : P₂ ≤ thompsonNormalizer T)
    (hTA : (T : Subgroup G) < L₂ ⊔ (T : Subgroup G))
    (hAN : L₂ ⊔ (T : Subgroup G) < thompsonNormalizer T)
    (hmax : IsMaximalTwoLocal (thompsonNormalizer T))
    (e : (thompsonNormalizer T ⧸ pCore 2 (thompsonNormalizer T)) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (A₄ : Subgroup G) (hTA₄ : (T : Subgroup G) < A₄)
    (hA₄C : A₄ < centralizer ({w.val} : Set G))
    (hA₄M : A₄ ≤ normalizer (L : Set G))
    (model₄ : Nonempty ((centralizer ({w.val} : Set G) ⧸
        pCore 2 (centralizer ({w.val} : Set G))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((centralizer ({w.val} : Set G) ⧸
        pCore 2 (centralizer ({w.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({w.val} : Set G) ⧸
        pCore 2 (centralizer ({w.val} : Set G))) ≃* Equiv.Perm (Fin 6)))
    (hfour : L₂ ⊔ (T : Subgroup G) ≤ normalizer ((pResidual 2 P₄).map P₄.subtype : Set G) ∨
      (L₂ ⊔ (T : Subgroup G)) ⊔ P₄ ≤ thompsonNormalizer T)
    (hpair : (pResidual 2 P₂).map P₂.subtype ≤
        normalizer ((pResidual 2 P₄).map P₄.subtype : Set G) ∨
      P₂ ⊔ P₄ ≤ thompsonNormalizer T) : False := by
  have hw1 : w ≠ 1 := by intro he; rw [he, m.weight_one] at hw; omega
  have hs := escaping_parabolic_solvable_of_small_quotient D w hw1 hwT A₄ P₄
    hTA₄ hA₄C hA₄M hP₄ hP₄w model₄
  exact false_of_linear_three_join h₀ h structural m L₂ P₂ P₄ hL₂ z w hz hw hzT hwT
    hP₂ hP₄ hP₂z hP₄w hP₂N hTA hAN hmax e hs hfour hpair

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
