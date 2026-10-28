module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
public import Theory.Representation.NormalPSubgroupKernel
public import Theory.Representation.NormalAbelianKernelOrder
public import Theory.Representation.BinaryOffender.CubicConjugateDimension
public import Theory.Representation.GroupEquivalence

/-!
# Cover elimination and the degree window for the source Hall--Janko action

Faithful irreducibility kills the two-core of the actual generalized Fitting
subgroup and makes its center odd. Thus the two-primary multiplier bound,
when supplied, kills the whole center and identifies the component with the
literal J₂ carrier.

Independently, the automorphism two-rank bound and four-conjugate generation
bound the binary degree by 32. A small-degree spectrum and a displacement
bound in degree 28 then reduce the degree to 12. These family-specific inputs
remain explicit: this module does not assert the missing multiplier,
conjugate-generation, or representation catalogue calculations.

Source: Aschbacher--Smith, Chapter K setup, printed p.451, and K.4 opening,
pp.457--458; Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1
(J₂ paragraph, author manuscript p.16), Theorem 6.6 and Table 6.7 (p.21).
The latter table gives absolute degree 6 over F₄, hence binary degree 12.
See `SourceDegree/Source.md` for the retrieved primary source and obligations.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko

open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender

universe u v
variable {G : Type u} [Group G] [Finite G]
variable {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
variable {ρ : Representation (ZMod 2) G W}

/-- The defining-characteristic core vanishes before any cover is excluded. -/
theorem SourceHypotheses.fitting_twoCore_eq_bot (h : SourceHypotheses ρ) :
    pCore 2 (generalizedFitting G) = ⊥ := by
  let := h.irreducible
  have hk := normal_p_subgroup_le_ker (ρ.comp (generalizedFitting G).subtype)
    (pCore 2 (generalizedFitting G)) pCore_isPGroup
  rw [(MonoidHom.ker_eq_bot_iff (ρ.comp (generalizedFitting G).subtype)).mpr
    (h.faithful.comp (generalizedFitting G).subtype_injective)] at hk
  exact le_bot_iff.mp hk

omit [FiniteDimensional (ZMod 2) W] in
/-- The actual intrinsic center has odd order; no multiplier fact is used. -/
theorem SourceHypotheses.fitting_center_odd (h : SourceHypotheses ρ) :
    Odd (Nat.card (center (generalizedFitting G))) := by
  let := h.irreducible
  have hn := card_normal_abelian_ne_zero_of_faithful_irreducible
    (ρ.comp (generalizedFitting G).subtype) (center (generalizedFitting G))
    (h.faithful.comp (generalizedFitting G).subtype_injective)
  apply Nat.not_even_iff_odd.mp
  intro he
  exact hn ((CharP.cast_eq_zero_iff (ZMod 2) 2 _).mpr (even_iff_two_dvd.mp he))

/-- This discharges the cover branch once its two-primary multiplier bound
has been proved for the actual central quotient. -/
theorem SourceHypotheses.fitting_center_eq_bot_of_twoGroup
    (h : SourceHypotheses ρ) (hc : IsPGroup 2 (center (generalizedFitting G))) :
    center (generalizedFitting G) = ⊥ := by
  let := h.irreducible
  have hk := normal_p_subgroup_le_ker (ρ.comp (generalizedFitting G).subtype)
    (center (generalizedFitting G)) hc
  rw [(MonoidHom.ker_eq_bot_iff (ρ.comp (generalizedFitting G).subtype)).mpr
    (h.faithful.comp (generalizedFitting G).subtype_injective)] at hk
  exact le_bot_iff.mp hk

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- Killing the intrinsic center upgrades the supplied quotient marking to
an actual component isomorphism, on the original subgroup. -/
theorem SourceHypotheses.fitting_equiv_of_center_eq_bot
    (h : SourceHypotheses ρ) (hc : center (generalizedFitting G) = ⊥) :
    Nonempty (generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier) := by
  obtain ⟨e⟩ := h.centralQuotient
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).symm.trans e⟩

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- The component inherits simplicity from its genuine central quotient. -/
theorem SourceHypotheses.fitting_simple_of_center_eq_bot
    (h : SourceHypotheses ρ) (hc : center (generalizedFitting G) = ⊥) :
    IsSimpleGroup (generalizedFitting G) := by
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  exact ((QuotientGroup.quotientMulEquivOfEq hc).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

omit [FiniteDimensional (ZMod 2) W] in
/-- The two-rank estimate descends through every perfect central cover. -/
theorem SourceHypotheses.twoRank_le_four_of_model_bound
    (h : SourceHypotheses ρ)
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4) :
    primeRank 2 G ≤ 4 := by
  let := h.quasisimple
  obtain ⟨e⟩ := h.centralQuotient
  exact (primeRank_le_central_quotient_automorphisms ρ (generalizedFitting G)
    h.faithful h.irreducible e).trans hr

/-- The original cubic action supplies an actual small-displacement involution. -/
theorem SourceHypotheses.exists_involution_codim_le_eight
    (h : SourceHypotheses ρ)
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4) :
    ∃ t : G, t ≠ 1 ∧ t ^ 2 = 1 ∧ fixedCodim ρ (zpowers t) ≤ 8 :=
  exists_involution_of_cubicRatio_le ρ (h.twoRank_le_four_of_model_bound hr) h.cubic_le_two

/-- Four-conjugate geometry bounds the degree of the literal binary action,
including involutions outside the component. -/
theorem SourceHypotheses.finrank_le_thirty_two_of_model_bounds
    (h : SourceHypotheses ρ)
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 4) :
    Module.finrank (ZMod 2) W ≤ 32 := by
  let := h.quasisimple
  let : IsSimpleGroup ((generalizedFitting G) ⧸ center (generalizedFitting G)) :=
    h.quasisimple.simple
  let : Nontrivial (generalizedFitting G) :=
    (QuotientGroup.mk'_surjective (center (generalizedFitting G))).nontrivial
  have hfix : fixedSpace ρ (generalizedFitting G) = ⊥ :=
    invariants_eq_bot_of_faithful_irreducible (ρ.comp (generalizedFitting G).subtype)
      (h.faithful.comp (generalizedFitting G).subtype_injective) h.irreducible
  exact finrank_le_of_cubicRatio_le_of_conjugates ρ (generalizedFitting G)
    hfix hgen (h.twoRank_le_four_of_model_bound hr) h.cubic_le_two

omit [Finite G] [FiniteDimensional (ZMod 2) W] in
/-- Transport the finite degree window along the actual component marking.
The spectrum is a representation-theoretic premise, not an assumed source conclusion. -/
theorem SourceHypotheses.finrank_cases_of_small_degree_spectrum
    (h : SourceHypotheses ρ)
    (e : generalizedFitting G ≃* _root_.Sporadic.LeechRelated.J2.Carrier)
    (hd : Module.finrank (ZMod 2) W ≤ 32)
    (hspectrum : ∀ σ : Representation (ZMod 2) _root_.Sporadic.LeechRelated.J2.Carrier W,
      Function.Injective σ → IsIrreducible σ → Module.finrank (ZMod 2) W ≤ 32 →
      Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28) :
    Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28 := by
  let σ := (ρ.comp (generalizedFitting G).subtype).comp e.symm.toMonoidHom
  have hf : Function.Injective σ :=
    (h.faithful.comp (generalizedFitting G).subtype_injective).comp e.symm.injective
  have hi : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective _).mpr h.irreducible
  exact hspectrum σ hf hi hd

/-- Conditional source assembly: the large involution displacement excludes
binary degree 28, leaving degree 12. Every additional input remains visible. -/
theorem SourceHypotheses.center_eq_bot_and_finrank_of_model_inputs
    (h : SourceHypotheses ρ)
    (hc : IsPGroup 2 (center (generalizedFitting G)))
    (hr : primeRank 2 (MulAut _root_.Sporadic.LeechRelated.J2.Carrier) ≤ 4)
    (hgen : InvolutionConjugateGenerationBound (generalizedFitting G) 4)
    (hspectrum : ∀ σ : Representation (ZMod 2) _root_.Sporadic.LeechRelated.J2.Carrier W,
      Function.Injective σ → IsIrreducible σ → Module.finrank (ZMod 2) W ≤ 32 →
      Module.finrank (ZMod 2) W = 12 ∨ Module.finrank (ZMod 2) W = 28)
    (hdisplacement : Module.finrank (ZMod 2) W = 28 →
      ∀ t : G, t ≠ 1 → t ^ 2 = 1 → 10 ≤ fixedCodim ρ (zpowers t)) :
    center (generalizedFitting G) = ⊥ ∧ Module.finrank (ZMod 2) W = 12 := by
  have hz := h.fitting_center_eq_bot_of_twoGroup hc
  refine ⟨hz, ?_⟩
  obtain ⟨e⟩ := h.fitting_equiv_of_center_eq_bot hz
  rcases h.finrank_cases_of_small_degree_spectrum e
    (h.finrank_le_thirty_two_of_model_bounds hr hgen) hspectrum with hd | hd
  · exact hd
  · obtain ⟨t, ht, ht2, htbound⟩ := h.exists_involution_codim_le_eight hr
    have hten := hdisplacement hd t ht ht2
    omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HallJanko
