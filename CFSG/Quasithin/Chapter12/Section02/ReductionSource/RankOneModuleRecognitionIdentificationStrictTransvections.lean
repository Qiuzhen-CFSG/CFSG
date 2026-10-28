module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationStrictCrossing
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictTransvections

/-!
# Crossing transvections on the whole reduced Chapter12 layer

The source hypotheses construct the moving residual cubic, disjoint centers,
both center cuts, and a nonzero marked vector in the original crossing space.
For the actual invariant commutator form and faithful dotted action, the
perpendicular hyperplane moves into that space and the common fixed space is
exactly the source line. Every centered transvection is realized in X-dot.

Source: Aschbacher--Smith, 6.2.17(1)--(3),(7)--(8), and 12.2.2(3d).
The remaining fixed bound, rank identity and strict contradiction stay with
qt-d-1222-recognition-strict-elimination. LocalAnalysis is discharged by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L : Subgroup G} {n : ℕ} {z : G}

/-- The complete crossing-center and full-transvection family on the whole
reduced layer. The final strict-branch owner still supplies the remaining
G.10 fixed bound, quotient rank equation, and classification elimination. -/
theorem strict_reduced_crossing_transvections
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (A : LocalAnalysis (T : Subgroup G) L (normalizer (L : Set G)) (wholeReduced T L) z)
    (hz : z ∈ ZS (T : Subgroup G) L (wholeReduced T L)) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L (wholeReduced T L) <
      sourceClosure (T : Subgroup G) L (wholeReduced T L) z ⊓ commutatorLayer T L) :
    ∃ d ∈ strictCrossingResidual (T : Subgroup G) L (wholeReduced T L),
      d ∈ L ∧ orderOf d = 3 ∧ d ∉ centralizer ({z} : Set G) ∧
      let U := sourceClosure (T : Subgroup G) L (wholeReduced T L) z
      let C := (center U).map U.subtype
      let C' := strictCrossingCenter (T : Subgroup G) L (wholeReduced T L) z d
      Disjoint C C' ∧
      C ⊓ U.map (MulAut.conj d⁻¹).toMonoidHom = zpowers z ∧
      C' ⊓ U = (zpowers z).map (MulAut.conj d⁻¹).toMonoidHom ∧
      ∃ he : IsElementaryAbelian 2 (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z),
        letI := he
        let ρ := strictRepresentation (T : Subgroup G) L (wholeReduced T L) z
        let E := strictHatSpace (T : Subgroup G) L (wholeReduced T L) z
          (strictCrossingIntersection (T : Subgroup G) L (wholeReduced T L) z d)
        let X := strictCrossingImage (T : Subgroup G) L (wholeReduced T L) z d
        ∃ B : LinearMap.BilinForm (ZMod 2)
            (Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)),
          B.IsAlt ∧ B.Nondegenerate ∧
          (∀ a u w, B (ρ a u) (ρ a w) = B u w) ∧
          (∀ a ∈ X, ∀ u ∈ B.orthogonal (strictSourceLine (T : Subgroup G) L (wholeReduced T L) z),
            ρ a u - u ∈ E) ∧
          (∀ e : E, (∀ a ∈ X, ρ a e = e) ↔
            (e : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ∈
              strictSourceLine (T : Subgroup G) L (wholeReduced T L) z) ∧
          ∃ v : E, (v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) ≠ 0 ∧
            (∀ a : X, ∃ φ : Module.Dual (ZMod 2) E, φ v = 0 ∧
              ∀ e : E, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) +
                φ e • (v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z))) ∧
            (∀ φ : Module.Dual (ZMod 2) E, φ v = 0 → ∃ a : X,
              ∀ e : E, ρ a e = (e : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z)) +
                φ e • (v : Additive (StrictVectorQuotient (T : Subgroup G) L (wholeReduced T L) z))) := by
  obtain ⟨d, hdres, hdL, _, hdZ, hd, hdH⟩ := strict_exists_crossing_cubic h611 hnatural hz horder
  obtain ⟨he, B, hBa, hBn, _, hinv, hB, _, _, hlineE, _⟩ :=
    A.strict_crossing_symplectic_geometry h611 hnatural hz horder hstrict hdZ hdH
  let := he
  refine ⟨d, hdres, hdL, hd, hdH,
    A.strict_crossing_centers_disjoint h611 hnatural hz horder hTH hstrict hdL hdZ hdH,
    A.strict_center_intersection_crossing h611 hnatural hz horder hTH hstrict hdL hdZ hdH,
    A.strict_crossing_center_intersection h611 hnatural hz horder hTH hstrict hdL hdZ hdH,
    he, B, hBa, hBn, hinv, ?_, ?_, ?_⟩
  · intro a ha u hu
    exact strict_crossing_perpendicular_displacement h611 hz hstrict B hB hdZ ha hu
  · exact A.strict_crossing_fixed_space h611 hnatural hz horder hTH hstrict hdL hdZ hdH
  · have hdim := A.strictSourceLine_finrank h611 hnatural hz horder hstrict
    have hne : strictSourceLine (T : Subgroup G) L (wholeReduced T L) z ≠ ⊥ := by
      intro heq
      rw [heq, finrank_bot] at hdim
      contradiction
    obtain ⟨v, hvS, hv⟩ := (strictSourceLine (T : Subgroup G) L (wholeReduced T L) z).ne_bot_iff.mp hne
    exact ⟨⟨v, hlineE hvS⟩, hv,
      A.strict_crossing_full_transvections h611 hnatural hz horder hTH hstrict hdL hdZ hdH
        ⟨v, hlineE hvS⟩ hv hvS⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
