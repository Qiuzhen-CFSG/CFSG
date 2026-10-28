module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.Inputs
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.WeakClosure
public import CFSG.Quasithin.ChapterE.Section03.WeakClosure.ConjugateSpan
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Basic

/-!
# The relative weak centralizer and normalizers for the G₂ branch

The first argument applies E.3.10 to each actual corank-one generator in
R₁. The value s=2n gives membership in A_(2n-1). The separate B.4.6(12)
localization then puts V₃ in C_{R₁}(W₁(R₁,V)), which is the source C₁.

Once W₀(T,V) centralizes V, it lies in the original O₂(LT). That core is
normal in LT and lies in R₁. Weak closure inside the core therefore gives
both normalizer bounds by maximal-local uniqueness, and identifies the
two zeroth weak closures. These deductions use no new model assumption.
The final theorem applies them to the literal rank-one R₁ consumer.

These are conditional transfer results. The root and plane argument proving
zeroth centralization and the B.4.6 localization are still required.
Source: Aschbacher--Smith, 11.2.2(5--6), pp.767--768, and 11.5.1, p.778.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
open ChapterE Representation.BinaryOffender
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

/-- E.3.10 converts the exact corank-one generators into the family used by
B.4.6(12). The localization is an explicit, separately required model result. -/
theorem threeSpace_le_weakCentralizer
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hloc : R1FamilyLocalization D S f) :
    f.Vi 2 ≤ weakCentralizer V (f.Ri 0) 1 := by
  let := D.elementary
  have hUV : f.Vi 2 ≤ V := D.centralQuotientPreimage_le _
  apply le_inf (hUV.trans (f.seed_le_Ri S 0))
  apply le_centralizer_iff.mpr
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g, hAg, hi⟩, hAR⟩
  by_cases hAC : A ≤ centralizer (V : Set G)
  · exact hAC.trans (Subgroup.centralizer_le hUV)
  have hAN : A ≤ normalizer (V : Set G) :=
    (hAR.trans (localRadical_le_sylow _)).trans S.sylow_normalizes
  have hcorank : subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A = 1 := by
    change Nat.log 2 _ = 1
    rw [hi]
    decide
  have hb : (subgroupCorank (V.map (MulAut.conj g).toMonoidHom) A : ℕ∞) < globalS V := by
    rw [hcorank, hs]
    exact_mod_cast (show 1 < 2 * S.field.degree by have := S.nonbinary; omega)
  have hcomm : ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := by
    intro he
    exact hAC (hAg.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp he)))
  have hfamily := (inducedAutomizer_mem_fixedSpaceFamily_of_corank_lt_globalS g
    (le_inf hAg hAN) hb hcomm).2
  rw [hs, ENat.toNat_natCast, hcorank] at hfamily
  exact le_centralizer_iff.mp (show f.Vi 2 ≤ centralizer (A : Set G) from
    (show ∀ A : Subgroup G, A ≤ f.Ri 0 →
      inducedAutomizer V A ∈ fixedSpaceFamily (automizerRepresentation V)
        (2 * S.field.degree - 1) → f.Vi 2 ≤ centralizer (A : Set G) from by
      simpa [R1FamilyLocalization] using hloc) A hAR hfamily)

/-- Clause (6), retaining the literal C₁(R₁,V)=C_{R₁}(W₁(R₁,V)).
The last hypothesis is exactly the preceding 11.1.4 bound. -/
theorem weakCentralizer_centralizer_le_of_family
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hloc : R1FamilyLocalization D S f)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G)) :
    centralizer (weakCentralizer V (f.Ri 0) 1 : Set G) ≤ normalizer (L : Set G) :=
  (Subgroup.centralizer_le (threeSpace_le_weakCentralizer D S f hs hloc)).trans hthree

/-- The original two-core is contained in the two-core of every LᵢT.
This uses normality in LT, not monotonicity of the two-core operation. -/
theorem originalCore_le_Ri (i : Fin 2) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ f.Ri i := by
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    rw [← seed_sylow_centralizer D S]
    exact inf_le_left
  apply le_pCoreIn_of_normalizes (isPGroup_pCoreIn _ _) (hQT.trans le_sup_right)
  apply (sup_le ((localResidual_le _).trans inf_le_left |>.trans le_sup_left)
    le_sup_right).trans
  exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))

/-- The source r-plane argument need only establish zeroth centralization.
All remaining assertions of (5), including the R₁ bound, follow here. -/
theorem normalizer_bounds_of_zero_centralizes
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G)) :
    normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ normalizer (L : Set G) ∧
      0 < globalW V (T : Subgroup G) ∧
      indexedWeakClosure V (f.Ri 0) 0 = indexedWeakClosure V (T : Subgroup G) 0 ∧
      normalizer (indexedWeakClosure V (f.Ri 0) 0 : Set G) ≤ normalizer (L : Set G) := by
  let Q := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hWQ : indexedWeakClosure V (T : Subgroup G) 0 ≤ Q := by
    dsimp [Q]
    rw [← seed_sylow_centralizer D S]
    exact hw
  have hQT : Q ≤ (T : Subgroup G) := by
    dsimp [Q]
    rw [← seed_sylow_centralizer D S]
    exact inf_le_left
  have heQ := weakClosure_eq_of_le_of_closure_le V Q (T : Subgroup G) 0 hQT hWQ
  have hn : L ⊔ (T : Subgroup G) ≤
      normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
    rw [← heQ]
    apply le_trans _ (normalizer_le_weakClosure_normalizer V Q 0)
    exact (L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hne : indexedWeakClosure V (T : Subgroup G) 0 ≠ ⊥ := by
    intro he
    exact D.ne_bot (bot_unique (he ▸ self_le_weakClosure_zero D.le_sylow))
  have hN := D.normal_subgroup_normalizer_le S.source.toHypothesis1221
    ((indexedWeakClosure_le V (T : Subgroup G) 0).trans le_sup_right) hne hn
  have hpos : 0 < globalW V (T : Subgroup G) := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    exact globalW_attained (n := 0) he hw
  have heR := weakClosure_eq_of_le_of_closure_le V (f.Ri 0) (T : Subgroup G) 0
    (localRadical_le_sylow _) (hWQ.trans (originalCore_le_Ri D S f 0))
  exact ⟨hN, hpos, heR, heR ▸ hN⟩

/-- Apply both derived bounds to the existing rank-one contradiction on the
original seed and the actual ambient image of the Sylow subgroup of H₁. -/
theorem rankOne_impossible_of_geometry
    (hs : @globalS G _ V D.elementary = (2 * S.field.degree : ℕ))
    (hloc : R1FamilyLocalization D S f)
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hw : indexedWeakClosure V (T : Subgroup G) 0 ≤
      (T : Subgroup G) ⊓ centralizer (V : Set G))
    (H₁ : Subgroup G) (P : Sylow 2 H₁)
    (hP : (P : Subgroup H₁).map H₁.subtype = f.Ri 0)
    (hn : generationParameter H₁ = 1) (hout : ¬ H₁ ≤ normalizer (L : Set G)) : False := by
  apply D.rankOne_R1_weakClosure_impossible S f H₁ P hP hn hout
  · rw [hs]
    exact_mod_cast (show 1 < 2 * S.field.degree by have := S.nonbinary; omega)
  · exact weakCentralizer_centralizer_le_of_family D S f hs hloc hthree
  · exact (normalizer_bounds_of_zero_centralizes D S f hw).2.2.2

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2
