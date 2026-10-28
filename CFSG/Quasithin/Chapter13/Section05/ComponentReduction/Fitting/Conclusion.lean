module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.NineObstruction
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction

/-!
# Fitting centralization in the Section 13.5 counterexample

The literal faithful action on U_H/V₁ has fixed codimension two for V*.
Failure of Fitting centralization would supply a normal elementary nine-group:
prime-core reduction, the normalizer/Thompson argument, and the supercritical
and cubic-rank deductions already exclude the other possibilities. The normal
nine-group forces fixed codimension at least four, a contradiction.

The counterexample application obtains both clauses of 13.5.19 from the proved
normalizer deductions, with Y = L₀ in the covered case and Y = L₁ otherwise.
The last theorem selects a genuine C-component, discharging its Fitting premise.

Only earlier source inputs remain explicit: F.9.1 applicability, the plane and
centralizer geometry of 13.5.2–13, the residual quotient facts, 13.2.2(9) in the
covered branch, the universal recognitions 13.5.16–17, and the universal clauses
F.9.5(2),(5),(6.i). Their producers are qt-13-05-f9-application,
qt-13-05-local-geometry, qt-13-05-normal-recognition, and qt-f09-rank-one/qt-f-09;
qt-13-05 retains their final discharge. No representation, pair-order,
13.5.19 normalizer, Fitting-centralization or obstruction conclusion is assumed in the
counterexample theorem. The full SQTK hypothesis is retained.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
Lemma 13.5.20 and the following paragraph, printed p.923 (PDF p.940).
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
open Section08.Source
open Section08.ComponentSieve.FieldComponents.SmallCovers
variable {G : Type*} [Group G] [Finite G]

/-- The action contradiction of 13.5.20, with the earlier Y and 13.5.19
facts explicit. Both the representation and the S₃ pairs are constructed
from the universal F.9.5 inputs on the actual source setup. -/
theorem centralizes_fitting_of_source_action
    (htwo : SourceAction.F95Two (G := G)) (hsix : SourceAction.F95Six (G := G))
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hrank : let := h.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4)
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
    (hcore : D.V ≤ (D.H ⊓ normalizer (Y : Set G)).pCoreIn 2) :
    starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H)) := by
  let : (D.V₁.subgroupOf D.UH).Normal := SourceAction.point_normal_in_UH h
  let : IsElementaryAbelian 2 (SourceAction.Quotient (D := D)) :=
    SourceAction.quotient_elementary h
  obtain ⟨hfaithful, hcodim, hpairs⟩ := SourceAction.action_and_pairs
    htwo hsix h V₂ M hindex hU hrank hmove hplane hbound hc
  by_contra hfit
  apply false_of_fitting_failure_of_binary_action K D h hSQTK hindex hU
    Y hYH hY hYquot hYV himage hcore
    (fun x hx => SourceAction.pair_card_of_symmetric_three (hpairs x hx))
    (SourceAction.representation h) hfaithful hcodim hfit

/-- The covered branch uses the literal residual L₀ = O²(O₂,Z(L)).
Only its earlier containment, cubic quotient and 13.2.2(9) are needed;
the normalizer-image and two-core conclusions of 13.5.19 are discharged. -/
theorem centralizes_fitting_of_covered_source
    (htwo : SourceAction.F95Two (G := G)) (hsix : SourceAction.F95Six (G := G))
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hrank : let := h.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (hYH : coverResidualIn D.L ≤ D.H)
    (hYquot : Nat.card (coverResidualIn D.L ⧸ pCore 2 (coverResidualIn D.L)) = 3)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hL0 : normalizer (coverResidualIn D.L : Set G) ≤ M) :
    starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H)) := by
  obtain ⟨himage, hcore⟩ := covered_normalizer D h M hYH hVM hL0
  have hY : IsPPerfect 2 (coverResidualIn D.L) := by
    have hi : IsPPerfect 2 (coverResidual D.L) := isPPerfect_embedded_pResidual 2 _
    let e := (coverResidual D.L).equivMapOfInjective D.L.subtype D.L.subtype_injective
    exact hi.of_surjective e.toMonoidHom e.surjective
  have hYV : coverResidualIn D.L ≤ normalizer (D.V : Set G) :=
    (coverResidualIn_le D.L).trans (le_sup_left.trans
      ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal))
  exact centralizes_fitting_of_source_action
    htwo hsix K D h hSQTK V₂ M hindex hU hrank hmove hplane hbound hc
    (coverResidualIn D.L) hYH hY hYquot hYV himage hcore

/-- Lemma 13.5.20 in the genuine counterexample to ModelConclusion.
The branch input consists only of the earlier residual facts. In the covered
branch Y is exactly L₀; in the ordinary A₅/A₆ branch Y is exactly L₁.
The latter uses the counterexample and 13.5.16–17 to obtain 13.5.18–19. -/
theorem centralizes_fitting_of_counterexample
    (htwo : SourceAction.F95Two (G := G)) (hsix : SourceAction.F95Six (G := G))
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hrank : let := h.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (n : ℕ) (hnot : ¬ ModelConclusion G n)
    (hH : D.H ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M)
    (hF : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (h16 : Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) →
      ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
        ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
          ClassicalGroup.IsPSU G 4 3)
    (h17 : n = 5 → ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hcases :
      (coverResidualIn D.L ≤ D.H ∧
        Nat.card (coverResidualIn D.L ⧸ pCore 2 (coverResidualIn D.L)) = 3 ∧
        normalizer (coverResidualIn D.L : Set G) ≤ M) ∨
      ((n = 5 ∨ (n = 6 ∧ Nonempty ((D.L ⧸ pCore 2 D.L) ≃*
          alternatingGroup (Fin 6)))) ∧ Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3)) :
    starImage D.H D.V ≤
      centralizer (fittingSubgroup (Hstar D.H) : Set (Hstar D.H)) := by
  rcases hcases with ⟨hYH, hYquot, hL0⟩ | ⟨hcase, hYquot⟩
  · exact centralizes_fitting_of_covered_source
      htwo hsix K D h hSQTK V₂ M hindex hU hrank hmove hplane hbound hc hYH hYquot hVM hL0
  · obtain ⟨_, himage, hcore⟩ := ordinary_counterexample_normalizers
      D M n hH hcase hnot h16 h17 hF hVM hbound hc
    have hYV : D.L₁ ≤ normalizer (D.V : Set G) :=
      (map_subtype_le _).trans (inf_le_left.trans (le_sup_left.trans
        ((normal_subgroupOf_iff_le_normalizer h.V_le_LT).mp h.reduced.normal)))
    exact centralizes_fitting_of_source_action
      htwo hsix K D h hSQTK V₂ M hindex hU hrank hmove hplane hbound hc
      D.L₁ (le_sup_left.trans h.local_le) (isPPerfect_embedded_pResidual 2 _)
      hYquot hYV himage hcore

/-- The component chosen in the paragraph after 13.5.20, with its Fitting
premise now proved. This retains the actual star image and the actual
K/O₂(K) equivalence, rather than replacing the component by a family tag. -/
theorem exists_component_of_counterexample
    (htwo : SourceAction.F95Two (G := G)) (hsix : SourceAction.F95Six (G := G))
    (K : GroupClass) (D : ChapterF.Section09.Setup G) (h : D.Hypothesis)
    (hSQTK : IsSQTK K D.H) (V₂ M : Subgroup G)
    (hindex : D.Vplus.relIndex D.V = 2) (hU : ¬ IsMulCommutative D.UH)
    (hrank : let := h.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4)
    (hmove : ∀ W : Subgroup G, D.V₁ < W → W ≤ D.Vplus →
      ∃ l ∈ D.L₁, V₂ ≤ W.map (MulAut.conj l).toMonoidHom)
    (hplane : ∀ k ∈ D.H, V₂ ≤ D.V ⊓ D.V.map (MulAut.conj k).toMonoidHom →
      ⁅D.V, D.V.map (MulAut.conj k).toMonoidHom⁆ = ⊥ ∨
      D.V.map (MulAut.conj k).toMonoidHom ≤ M ⊓ normalizer (D.V : Set G))
    (hbound : normalizer (D.V₁ : Set G) ⊓ normalizer (D.Vplus : Set G) ≤ M)
    (hc : ⁅D.V, M ⊓ centralizer (D.Vplus : Set G)⁆ ≤ D.V₁)
    (n : ℕ) (hnot : ¬ ModelConclusion G n)
    (hH : D.H ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M)
    (hF : ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ({D with H := J} : ChapterF.Section09.Setup G).Hypothesis)
    (h16 : Nonempty ((D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6)) →
      ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
        ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
          ClassicalGroup.IsPSU G 4 3)
    (h17 : n = 5 → ∀ J ∈ Hz D.L₁ D.T (normalizer (D.V₁ : Set G)) M,
      ¬ IsMulCommutative (UH J D.Vplus) → (D.L₁.subgroupOf J).Normal →
        ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3)
    (hVM : D.V ≤ M.pCoreIn 2)
    (hcases :
      (coverResidualIn D.L ≤ D.H ∧
        Nat.card (coverResidualIn D.L ⧸ pCore 2 (coverResidualIn D.L)) = 3 ∧
        normalizer (coverResidualIn D.L : Set G) ≤ M) ∨
      ((n = 5 ∨ (n = 6 ∧ Nonempty ((D.L ⧸ pCore 2 D.L) ≃*
          alternatingGroup (Fin 6)))) ∧ Nat.card (D.L₁ ⧸ pCore 2 D.L₁) = 3)) :
    ∃ C : Subgroup G, C ≤ D.H ∧ (C.subgroupOf D.H).IsCComponent ∧
      IsQuasisimple (starImage D.H C) ∧
      Nonempty ((C ⧸ pCore 2 C) ≃* starImage D.H C) ∧
      ⁅starImage D.H C, starImage D.H D.V⁆ ≠ ⊥ := by
  apply exists_component_of_fitting_centralized D h hU
  exact centralizes_fitting_of_counterexample
    htwo hsix K D h hSQTK V₂ M hindex hU hrank hmove hplane hbound hc
    n hnot hH hF h16 h17 hVM hcases

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
