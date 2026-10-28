module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.Reduction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Rank
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Pairs

/-!
# The source action inputs to the Fitting argument in 13.5.20

The literal faithful binary representation, F.9.5 commutator specialization,
and lifted S₃ conjugate pairs supply the two action inputs to the remaining
normal-nine obstruction. The final theorem applies the derived order-six
premise directly to normal_nine_of_fitting_failure, preserving full SQTK and
all original Y and normalizer hypotheses.

This conditional helper does not assert 13.5.20. The universal F.9.5 inputs
are owned by qt-f09-rank-one/qt-f-09, the original F.9.1 application and
earlier plane/centralizer geometry by qt-13-05-f9-application and
qt-13-05-local-geometry, with discharge at qt-13-05. The independent
normal-nine obstruction and final Fitting centralization belong to
qt-13-05-fitting-nine-binary and qt-13-05-fitting-centralization.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
F.9.5, printed pp.319–320; 13.5.13/20, printed pp.919/923.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
open Section08.Source Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G}

/-- The exact action and pair inputs required by the remaining representation
obstruction. The universal F.9.5 implications and earlier geometry remain
with their source owners; neither local target is assumed. -/
theorem action_and_pairs (htwo : F95Two (G := G)) (hsix : F95Six (G := G))
    (h : D.Hypothesis) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hrank : let := h.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁) :
    let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
    let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary h
    Function.Injective (representation h) ∧
      fixedCodim (representation h) (starImage D.H D.V) = 2 ∧
      ∀ x : Hstar D.H, ¬ IsPGroup 2 (starImage D.H D.V ⊔
        (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) →
        Nonempty ((starImage D.H D.V ⊔
          (starImage D.H D.V).map (MulAut.conj x).toMonoidHom : Subgroup (Hstar D.H)) ≃*
          Equiv.Perm (Fin 3)) := by
  have hcard := (card_V_iff_rank_four h).mpr hrank
  let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH h
  let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary h
  exact ⟨representation_injective h, fixedCodim_two h htwo hindex hU hcard,
    pairs_symmetric_three hsix h V₂ M hindex hU hcard hmove hplane hbound hc⟩

/-- The specialized F.9.5 pair theorem feeds the published Fitting reduction.
The full SQTK hypothesis and the literal 13.5.19 equalities are retained.
The resulting normal nine-group still requires the independent binary
obstruction before 13.5.20 can be concluded. -/
theorem normal_nine_of_source_pairs
    (hsix : F95Six (G := G)) (K : GroupClass) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hcard : Nat.card D.V = 16)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (Y : Subgroup G) (hYH : Y ≤ D.H) (hY : IsPPerfect 2 Y)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hYV : Y ≤ normalizer (D.V : Set G))
    (himage : starImage D.H (D.H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage D.H Y : Set (Hstar D.H)))
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hfit : ¬ starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H))) :
    ∃ P : Subgroup (Hstar D.H), P.Normal ∧ P ≤ pCore 3 (Hstar D.H) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      ⁅P, starImage D.H D.V⁆ ≠ ⊥ ∧
      ¬ (starImage D.H Y).pCoreIn 2 ≤ centralizer (P : Set (Hstar D.H)) := by
  apply normal_nine_of_fitting_failure K D h hSQTK hindex hU Y hYH hY hYquot hYV
    himage hcore ?_ hfit
  intro x hx
  exact pair_card_of_symmetric_three
    (pairs_symmetric_three hsix h V₂ M hindex hU hcard hmove hplane hbound hc x hx)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction
