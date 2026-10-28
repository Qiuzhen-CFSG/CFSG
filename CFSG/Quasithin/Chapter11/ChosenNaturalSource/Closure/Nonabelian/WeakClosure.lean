module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.Cardinalities
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.SourceClauses
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry

/-!
# Weak-closure inputs for the nonabelian natural closure

The genuine 11.2.5 dichotomy and assumed abelianness put W0 outside O2(H).
Minimality of the original H-star subgroup then puts N_H(W0) inside M.
Separately, line alignment for every noncentral corank-one intersection
makes the source plane centralize W1 when the normal closure is abelian.
This retains the exact conjugation maps and the original weak closures.

LineAlignment is a local geometric output to be proved by the transvection
and field-automorphism analysis, including SL3(4). It is not supplied by
Geometry or by the marked flag. No result here asserts 11.5.3(3).
Source: Aschbacher--Smith, 11.5.3(3), printed pp.779--780;
E.3.19, printed pp.234--235.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
open Subgroup Theory.GroupTheory
open CFSG.Quasithin
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.Chapter11.ChosenNaturalSource
open CFSG.Quasithin.ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

theorem normalizer_weakClosure_le
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hcore : ¬ indexedWeakClosure V (T : Subgroup G) 0 ≤ E.H.pCoreIn 2) :
    E.H ⊓ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ E.M := by
  have hTH : (T : Subgroup G) ≤ E.H := hH.1.1.2
  apply Chapter3.HStar.proper_overgroup_le T hH
  · exact le_inf hTH (T.toSubgroup.le_normalizer.trans
      (normalizer_le_weakClosure_normalizer V (T : Subgroup G) 0))
  · apply lt_of_le_of_ne inf_le_left
    intro he
    have hnorm : E.H ≤ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) := by
      rw [← he]
      exact inf_le_right
    exact hcore (le_pCoreIn_of_normalizes
      (T.2.to_le (indexedWeakClosure_le V T 0))
      ((indexedWeakClosure_le V T 0).trans hTH) hnorm)

theorem normalizer_weakClosure_le_of_abelian
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (habelian : IsMulCommutative E.W) :
    E.H ⊓ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ E.M := by
  apply normalizer_weakClosure_le E hH
  have he : Chapter11.Source.conjugateSpan (normalizer (E.V₁ : Set G)) V = E.W :=
    (conjugateSpanBy_eq_iSup_conj V E.G₁).symm
  have hc := hobstruction.resolve_right (fun hn => hn (he ▸ habelian))
  rwa [ShadowReduction.weakClosureZero_eq_indexed] at hc

/-- Output of the transvection calculation, with no abelianness assumption. -/
def LineAlignment : Prop :=
  ∀ g : G,
    subgroupCorank (V.map (MulAut.conj g : G →* G))
      (V.map (MulAut.conj g : G →* G) ⊓ (T : Subgroup G)) ≤ 1 →
    ¬ E.V₂ ≤ centralizer
      ((V.map (MulAut.conj g : G →* G) ⊓ (T : Subgroup G) : Subgroup G) : Set G) →
    ∃ c ∈ E.G₁, V.map (MulAut.conj c : G →* G) = V.map (MulAut.conj g : G →* G)

theorem plane_le_weakCentralizer_of_alignment
    (halign : LineAlignment E) (habelian : IsMulCommutative E.W) :
    E.V₂ ≤ weakCentralizer V (T : Subgroup G) 1 := by
  have hp : E.V₂ ≤ V := D.centralQuotientPreimage_le E.plane
  apply le_inf (hp.trans D.le_sylow)
  apply le_centralizer_iff.mpr
  rw [weakClosure_eq_sSup_gamma]
  apply sSup_le
  rintro A ⟨⟨g, hAV, hindex⟩, hAT⟩
  have hcor : subgroupCorank (V.map (MulAut.conj g : G →* G))
      (V.map (MulAut.conj g : G →* G) ⊓ (T : Subgroup G)) ≤ 1 := by
    have hi := relIndex_le_of_le_left (L := V.map (MulAut.conj g : G →* G))
      (le_inf hAV hAT) (by
        change (A.subgroupOf (V.map (MulAut.conj g : G →* G))).index ≠ 0
        exact index_ne_zero_of_finite)
    have hh := Nat.log_mono_right (b := 2) hi
    change A.relIndex (V.map (MulAut.conj g : G →* G)) = 2 ^ 1 at hindex
    rw [hindex] at hh
    exact hh
  by_contra hn
  have hn' : ¬ E.V₂ ≤ centralizer
      ((V.map (MulAut.conj g : G →* G) ⊓ (T : Subgroup G) : Subgroup G) : Set G) := by
    intro h
    exact hn ((le_inf hAV hAT).trans (le_centralizer_iff.mp h))
  obtain ⟨c, hc, hcg⟩ := halign g hcor hn'
  have hgW : V.map (MulAut.conj g : G →* G) ≤ E.W := by
    rw [← hcg]
    change _ ≤ conjugateSpanBy V E.G₁
    rw [conjugateSpanBy_eq_iSup_conj]
    exact le_iSup (fun c : E.G₁ => V.map (MulAut.conj (c : G)).toMonoidHom) ⟨c, hc⟩
  have hWW : E.W ≤ centralizer (E.W : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr habelian
  have hpW : E.V₂ ≤ E.W := hp.trans (le_conjugateSpanBy V E.G₁)
  exact hn ((hAV.trans hgW).trans
    (hWW.trans (centralizer_le hpW)))

/-- Both subgroup bounds required by E.3.19 on the original chosen V.
The remaining geometric input is precisely the source line alignment. -/
theorem weakClosure_bounds_of_abelian (F₀ : MarkedFlag E)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥)
    (hNV : normalizer (V : Set G) ≤ E.M)
    (hr : (subgroupCorank V E.V₁ : ℕ∞) ≤ globalR V)
    (hH : E.H ∈ Chapter3.HStar (T : Subgroup G) E.M)
    (hobstruction : Chapter11.Source.WeakClosureObstruction (T : Subgroup G) V E.V₁ E.H)
    (halign : LineAlignment E) (habelian : IsMulCommutative E.W) :
    centralizer (weakCentralizer V (T : Subgroup G) 1 : Set G) ≤ E.M ∧
      E.H ⊓ normalizer (indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤ E.M := by
  refine ⟨?_, normalizer_weakClosure_le_of_abelian E hH hobstruction habelian⟩
  exact (centralizer_le (plane_le_weakCentralizer_of_alignment E halign habelian)).trans
    (plane_centralizer_le F₀ hfixed hNV hr)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian
