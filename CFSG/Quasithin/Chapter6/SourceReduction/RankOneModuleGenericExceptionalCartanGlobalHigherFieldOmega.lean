module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHigherFieldTorus
public import CFSG.Quasithin.ChapterD.Section03.HermitianMultiplicity
public import CFSG.Quasithin.Chapter7.NormalizedSource.Automizer
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.Representation.SL2.BinarySmallFixed

/-!
# Omega-centralization in the higher-field Hermitian Cartan branch

The full binary normalizer of the actual Hermitian SL₂ module is non-FF
when the half-degree exceeds one. Uniqueness of the maximal two-local
containing LT puts the full ambient module normalizer inside N_G(L).
The literal quotient marking therefore transfers non-FF to the module's
actual automizer. Thompson movement would supply an FF offender, so J(T)
centralizes the module. The proved source 3.1.8 then forces every original
H-star comparison group to centralize the Sylow omega-center.

Hermitian coordinates also prove that the actual L-span of omega is
noncentral, allowing its reduced-input reselection without a centralization
premise. Thus the degree-eight torus construction and its original prime
pair require only the model, with omega-centralization discharged. Model
selection, the general field-degree bound and zero-core recognition remain
separate source obligations.
Source: Aschbacher--Smith 5.1.6(4), pp.632--633, using 3.1.8(3), p.576,
B.2.7 and K.3.1.2 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Representation.OrthogonalFourMinus
variable {G : Type*} [Group G] [Finite G]
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) := ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))

/-- The original reduced Hermitian module is centralized by J(T) above
half-degree one; its full automizer has no FF offenders. -/
theorem Input.hermitian_thompson_centralizes
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) :
    elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G) := by
  let := h.reduced.2.1
  have hW : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
  have hWN := reduced_normalizes h.reduced
  have hNW : normalizer (W : Set G) ≤ normalizer (L : Set G) :=
    normalizer_le_of_unique_maximalTwoLocal h.unique_local_join
      (IsElementaryAbelian.isPGroup 2 W) hW hWN
  obtain ⟨e,f,hf⟩ := hm
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.quotient_quasisimple
  let : IsQuasisimple SL(2,FiniteModel.Field s) := IsQuasisimple.of_mulEquiv e
  have hL : IsSQTK KnownSimple.IsKnownSimple L :=
    ((h.qtke.twoLocal_sqtk h.maximal.1).subgroup (L.subgroupOf (normalizer (L : Set G)))).knownSimple_of_equiv
      (subgroupOfEquivOfLe L.le_normalizer)
  have hmodel : IsSQTK KnownSimple.IsKnownSimple SL(2,FiniteModel.Field s) :=
    (ChapterE.Structure.sqtk_two_quotient hL (pCore 2 L) pCore_isPGroup).knownSimple_of_equiv e
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  let b : Additive W ≃ₗ[ZMod 2] FiniteModel.Space s :=
    { __ := f.toAdditiveLeft
      map_smul' := ZMod.map_smul f.toAdditiveLeft }
  have hn : ¬ IsFFModule (ChapterE.automizerRepresentation W) := by
    apply Chapter7.NormalizedSource.automizer_nonFF W L (le_sup_left.trans hWN) hNW
      (SL2.BinarySmall.hermitian s) q (e.surjective.comp (QuotientGroup.mk'_surjective _)) b.symm
    · intro l v
      apply Additive.toMul.injective
      apply Subtype.ext
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian s (q l) v)) : G) =
          (l : G) * (f.symm (Multiplicative.ofAdd v) : G) * (l : G)⁻¹
      have he := hf l (b.symm v).toMul
      change (f.symm (Multiplicative.ofAdd
        (SL2.BinarySmall.hermitian s (q l) (f (f.symm (Multiplicative.ofAdd v))).toAdd)) : G) = _ at he
      simp only [f.apply_symm_apply] at he
      exact he
    · exact ChapterD.hermitian_normalizer_not_ff s hmodel hs
  exact Chapter7.NormalizedSource.thompson_centralizes
    ⟨hW,h.reduced_le_sylow,le_sup_right.trans hWN⟩ hn

/-- Source 3.1.8 turns Hermitian non-FF into centralization of the original
Sylow omega-center by every actual H-star comparison group. -/
theorem Input.hstar_centralizes_omega_of_hermitian
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L W (SL2.BinarySmall.hermitian s)) :
    H ≤ omegaCentralizer T := by
  have hz : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hn
    exact h.thompson_moves_of_noncentral_omega hH hn
      (h.hermitian_thompson_centralizes s hs hm)
  intro x hx z hz'
  obtain ⟨a,ha,rfl⟩ := hz hz'
  exact (congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)).symm

omit [Finite G] in
private theorem hermitian_noncentral
    {L U : Subgroup G} (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L U (SL2.BinarySmall.hermitian s)) : ⁅U,L⁆ ≠ ⊥ := by
  intro hz
  have hc := commutator_eq_bot_iff_le_centralizer.mp hz
  obtain ⟨e,f,hf⟩ := hm
  let : Nontrivial (FiniteModel.Space s) := (FiniteModel.coordinates s).toEquiv.nontrivial
  obtain ⟨v,hv⟩ := exists_ne (0 : FiniteModel.Space s)
  apply hv
  apply SL2.BinarySmall.hermitian_fixed_eq_zero
  intro g
  obtain ⟨l,hl⟩ := e.surjective.comp (QuotientGroup.mk'_surjective (pCore 2 L)) g
  rw [←hl]
  apply Multiplicative.ofAdd.injective
  apply f.symm.injective
  apply U.subtype_injective
  let u : U := f.symm (Multiplicative.ofAdd v)
  have he := hf l u
  simp only [u,f.apply_symm_apply] at he
  change (f.symm (Multiplicative.ofAdd
    (SL2.BinarySmall.hermitian s (e (QuotientGroup.mk' (pCore 2 L) l)) v)) : G) = _
  change (f.symm (Multiplicative.ofAdd
    (SL2.BinarySmall.hermitian s (e (QuotientGroup.mk' (pCore 2 L) l)) v)) : G) = _ at he
  exact he.trans ((mul_inv_eq_iff_eq_mul).mpr (hc u.property l l.property))

/-- The original omega-span model itself proves noncentrality, so the
reselected reduced input needs no outside-centralization premise. -/
private theorem Input.hermitian_omega_span_input
    {T : Sylow 2 G} {L W : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) :
    Input KnownSimple.IsKnownSimple T L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  apply h.omega_span_input
  intro hc
  have hz := conjugateSpanBy_le le_rfl (hc.trans (Subgroup.centralizer_le_normalizer _))
  exact hermitian_noncentral s hm
    (commutator_eq_bot_iff_le_centralizer.mpr (hz.trans (le_centralizer_iff.mp hc)))

/-- Centralization required by the higher-field torus argument follows
from its actual Hermitian model at every half-degree greater than one. -/
theorem Input.hermitian_omega_span_centralizes
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (s : ℕ) [NeZero s] (hs : 1 < s)
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) :
    H ≤ omegaCentralizer T :=
  (h.hermitian_omega_span_input s hm).hstar_centralizes_omega_of_hermitian hH s hs hm

/-- At original degree eight, the actual Hermitian omega-span alone
supplies the order-seventeen factor with nonzero join core and the cubic
and quintic factors; H-centralization is proved, not assumed. -/
theorem Input.cartanSmallGeneration_of_hermitian_degree_eight_model
    {T : Sylow 2 G} {L W H A B : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple T L W 8)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (s : ℕ) [NeZero s]
    (hm : IsConjugationModel L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L)
      (SL2.BinarySmall.hermitian s)) : CartanSmallGeneration A H 8 := by
  have hn := h.exponent_of_hermitian_model s hm
  exact h.cartanSmallGeneration_of_hermitian_degree_eight hH c
    (h.hermitian_omega_span_centralizes hH s (by omega) hm) s hm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
