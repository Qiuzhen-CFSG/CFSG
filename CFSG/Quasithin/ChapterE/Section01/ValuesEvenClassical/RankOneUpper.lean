module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.LinearRank
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.UnitaryLocal
public import CFSG.Quasithin.Defs

/-!
# The rank-one classical upper bounds in E.1.14(1)

The simple generalized Fitting subgroup is self-centralizing by the simple
socle structure theorem.  For the linear model, faithful conjugation gives
the sharp elementary rank bound, and the whole-group component calculation
then gives E-generation at rank `f`.

For the unitary model, an elementary subgroup of rank greater than `f` has
an outer involution.  The fixed-field PSL₂ calculation supplies the local
E-member outside the ambient Borel.  Families containing a smaller member
are handled by the whole-group component member, and the rank dichotomy
assembly handles the remaining families.

These are the source-shaped adapters for E.1.14(1); all local quotient,
residual, component, and Sylow conditions are discharged by the imported
model modules.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--E.1.6 and E.1.14(1), printed pp.209--211, 214, citing Aschbacher,
*GF(2)-representations of finite groups* (1982), Lemma 4.7,
DOI 10.2307/2374202. The proof here uses the independently proved model
calculations and the corrected local tau convention of E.1.2.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-! ## PSL₂ -/

/-- The upper-generation half of the PSL₂ clause of E.1.14(1), including ambient outer
two-automorphisms.  The SQTK hypothesis is retained at the source boundary;
the proof uses the displayed simple-socle and supplement hypotheses. -/
theorem isEGenerated_of_psl2 {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T₀ : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSL2Model f) : IsEGenerated f G := by
  let L := generalizedFitting G
  have ha : ¬ IsMulCommutative L := linear_socle_not_isMulCommutative L e
  have hC : centralizer (L : Set G) = ⊥ := SimpleSocle.centralizer_eq_bot ha
  intro S
  apply linear_isEGeneratedAt_of_top_component hf e hC S
  intro A hA hAS hne
  exact eCaseComponent_top ha T₀ hgen (S : Subgroup G) A hne

/-- Numerical upper-bound adapter for the PSL₂ source clause. -/
theorem generationParameter_le_of_psl2 {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T₀ : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSL2Model f) : generationParameter G ≤ f :=
  generationParameter_le (by omega) (isEGenerated_of_psl2 hG hf T₀ hgen e)

/-! ## PSU₃ -/

/-- The upper-generation half of the PSU₃ clause of E.1.14(1), including ambient outer
two-automorphisms.  The Borel is the literal normalizer of `S ∩ L`; the
matrix model uses `GaloisField 2 (2 * f)` through `PSU3Model`. -/
theorem isEGenerated_of_psu3 {K : GroupClass} (_hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T₀ : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSU3Model f) : IsEGenerated f G := by
  let L := generalizedFitting G
  have ha : ¬ IsMulCommutative L :=
    UnitaryLocal.generalizedFitting_nonabelian hf e
  have hC : centralizer (L : Set G) = ⊥ := SimpleSocle.centralizer_eq_bot ha
  obtain ⟨_, _, hO, _, _, _, _⟩ :=
    SimpleSocle.structure_of_sylow_supplement ha T₀ hgen
  intro S
  let B : Subgroup G := normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G)
  have hBprops := UnitaryLocal.borel_properties L hf e T₀ S hgen
  have hBproper : B ≠ ⊤ := by simpa [B] using hBprops.1
  have hSB : (S : Subgroup G) ≤ B := by simpa [B] using hBprops.2.1
  have hB : ∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ → M ≤ B := by
    simpa [B] using hBprops.2.2
  apply isEGeneratedAt_of_rank_dichotomy S B hBproper hB
  · intro A hA hAS hne
    exact eCaseComponent_top ha T₀ hgen (S : Subgroup G) A hne
  · intro A hA hAS hr
    obtain ⟨B', _hB'proper, _hSB', hB'over, _t, _htA, _htL, _ht2,
        K', hK', hK'escape⟩ :=
      UnitaryLocal.exists_local_member_of_large_rank hf L e hC hO T₀ S hgen
        A hA hAS hr
    have hBB' : B ≤ B' := hB'over B hSB hBproper
    refine ⟨K', hK', ?_⟩
    intro hK'B
    exact hK'escape (hK'B.trans hBB')

/-- Numerical upper-bound adapter for the PSU₃ source clause. -/
theorem generationParameter_le_of_psu3 {K : GroupClass} (hG : IsSQTK K G)
    [IsSimpleGroup (generalizedFitting G)] {f : ℕ} (hf : 2 ≤ f)
    (T₀ : Sylow 2 G)
    (hgen : generalizedFitting G ⊔ (T₀ : Subgroup G) = ⊤)
    (e : generalizedFitting G ≃* PSU3Model f) : generationParameter G ≤ f :=
  generationParameter_le (by omega) (isEGenerated_of_psu3 hG hf T₀ hgen e)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankOneUpper
