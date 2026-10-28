module
public import CFSG.Quasithin.Chapter12.Section02.ModuleClassification.RankOneRecovery
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleField

/-!
# Recovering the rank-one actor of the orthogonal orbit

The actual orbit projection is a perfect central cover. Its two-group
kernel vanishes in L/O2(L), so the orthogonal-minus row supplies the literal
PSL2 marking needed by the rank-one source exit. That exit forces the field
exponent to be two, contradicting the orthogonal row's parameter. This
argument never identifies the seed with its orbit.
Source: Aschbacher--Smith 6.2.20, 7.0.1 and 12.2.2, pp.691,695,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Representation.OrthogonalFourMinus.FiniteModel
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)

/-- The original quotient, rather than only its central quotient, is the
rank-one group in the genuine orthogonal orbit marking. -/
theorem orbit_orthogonal_actor
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    {n : ℕ} [NeZero n] (hn : 1 < n)
    (M : ChapterK.RankOne.OrthogonalModel n D.orbitRepresentation D.orbitComponent) :
    ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ (2 * n)) := by
  let := h.quasisimple
  let := D.orbitComponent_quasisimple h
  let p : Matrix.SpecialLinearGroup (Fin 2) (Field n) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n) :=
    MulEquiv.ofBijective (BenderSuzuki.Converse.pi (Field n))
      ⟨BenderSuzuki.Converse.pi_injective,BenderSuzuki.Converse.pi_surjective⟩
  let e := M.groupEquiv.trans p
  let q := D.orbitComponentQuotientHom h
  have hq : Function.Surjective q := D.orbitComponentQuotientHom_surjective h
  let f : PerfectCentralCovering.Cover (L ⧸ pCore 2 L)
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (Field n)) :=
    ⟨e.toMonoidHom.comp q,e.surjective.comp hq,inferInstance,by
      intro x hx
      have he : q x = 1 := e.injective (hx.trans e.map_one.symm)
      rw [← IsQuasisimple.comap_center_of_surjective q hq]
      change q x ∈ center D.orbitComponent
      rw [he]
      exact one_mem _⟩
  have hcard : Nat.card (Field n) = 2 ^ (2 * n) :=
    GaloisField.card 2 (2 * n) (by omega)
  have hk := Theory.SL2.perfect_central_kernel_isTwoGroup (2 * n) (by omega) hcard f
  have hf : Function.Injective f.toMonoidHom := by
    apply f.toMonoidHom.ker_eq_bot_iff.mp
    apply bot_unique
    rw [← pCore_quotient_pCore_eq_bot 2]
    exact le_sSup ⟨inferInstance,hk⟩
  exact ⟨Field n,inferInstance,inferInstance,hcard,
    ⟨MulEquiv.ofBijective f.toMonoidHom ⟨hf,f.surjective⟩⟩⟩

/-- Apply the rank-one source exit to the actual orthogonal orbit actor.
The incompatible exponents exclude the entire non-FF orthogonal row. -/
theorem not_orthogonal_orbit_of_rankOne_exit
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module) :
    ¬ Chapter7.NormalizedSource.OrthogonalMinusAlternative
      D.orbitRepresentation D.orbitComponent := by
  rintro ⟨n,hn,⟨M⟩⟩
  let : NeZero n := ⟨by omega⟩
  have hpsl := D.orbit_orthogonal_actor h hn M
  obtain ⟨e,_⟩ := hrank (2 * n) (by omega) hpsl
  have he := Chapter6.Source.exponent_eq_two_of_psl_and_a5 (by omega : 1 < 2 * n) hpsl e
  omega

/-- The exact normalized 7.0.1 exit and rank-one source exit yield FF on
the original orbit; no seed/orbit equality is an input. -/
theorem orbit_ff_of_normalized_source_and_rankOne
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hrank : ∀ n, 1 < n → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n) →
      Chapter6.Source.IsConjugationModel L V Chapter6.Source.a5Module)
    (hexit : IsFFModule D.sourceOrbitNormalizerRepresentation ∨
      Chapter7.NormalizedSource.OrthogonalMinusAlternative
        D.orbitRepresentation D.orbitComponent) :
    IsFFModule D.sourceOrbitNormalizerRepresentation :=
  hexit.resolve_right (D.not_orthogonal_orbit_of_rankOne_exit h.toHypothesis1221 hrank)

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
