module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSubmodule
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalNaturalExclusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowSieve
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.SeedAlternativesMovedSylowOffender
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceIrreducible
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.PSL2Recognition
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Orthogonal.Assembly
-- Internal continuation of the orbit action: the quotient and coordinate
-- formulas are used only in private proof transport, never in the public API.
import all CFSG.Quasithin.Chapter12.Section02.ReductionSource.Actor.Orbit

/-!
# Complete module recognition from the original local Cartan witness

Outside centralization kills the fixed space of the original chosen constituent.
If its Sylow orbit is larger, the genuine cubic-orbit bound makes that constituent
an FF-module. Chapter K gives natural or Hermitian coordinates: natural twists
force invariance, and the Hermitian FF case has half-degree one. If the chosen
constituent is invariant, the faithful orbit action satisfies Chapter K directly.
The escaping cubic excludes its natural model; its actual Hermitian coordinates
then give degree two by the preceding torus argument.

Selection from the original input discharges every model and invariance premise.
The existing degree-two theorem recognizes the entire original [W,L], including
splitting and multiplicity, and relocates the component to the omega centralizer.
Thus the module-recognition and centralization source cuts are proved universally.
Only the original component-and-inverted-cubic sieve remains explicit in the
source escape assembly.

Source: Aschbacher--Smith 5.1.3 and the final paragraph of 5.1.13,
printed pp.630--631,638, using D.3.10 and K.3.1, refs/quasithin.pdf.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative MatrixGroups
open Representation.OrthogonalFourMinus
local instance (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) :=
  ZMod.algebra _ 2
local instance (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s)
    (algebraMap (ZMod 2) (FiniteModel.fixedField s))
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source Chapter6.Source.RankOneGeneric
open Chapter3.Section02.ChosenSource325 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L W V H A B Y X C : Subgroup G} {n : ℕ}
  (D : ChosenModule T L V)

private theorem quotient_action_injective
    (h : Input KnownSimple.IsKnownSimple T L W n)
    {E : Type*} [Group E] [Nontrivial E]
    (q : (L ⧸ pCore 2 L) →* E) (hq : Function.Surjective q) :
    Function.Injective q := by
  let := h.quotient_quasisimple
  apply q.ker_eq_bot_iff.mp
  rcases IsQuasisimple.normal_le_center_or_eq_top q.ker with hc | ht
  · exact bot_unique (hc.trans h.quotient_center_eq_bot.le)
  · obtain ⟨x,hx⟩ := exists_ne (1 : E)
    obtain ⟨y,rfl⟩ := hq x
    exact (hx (ht.ge (mem_top y))).elim

private theorem orbit_bound
    (h : Input KnownSimple.IsKnownSimple T L W n) :
    cubicRatio D.orbitRepresentation ≤ 2 := by
  apply D.orbit_cubicRatio_le_source h.original_section1221
  intro M hM hTM
  by_cases he : M = normalizer (L : Set G)
  · exact he.symm ▸ h.outside
  · exact Chapter3.hasMaximalOutside_of_two_distinct hM h.maximal hTM
      h.sylow_normalizes (Ne.symm he)

include D

private theorem fixed_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) : V ⊓ centralizer (L : Set G) = ⊥ := by
  have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
  have hw : RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ :=
    Subgroup.inf_centralizer_eq_bot_of_omega_disjoint T L _
      RankOneModule.wholeReduced_mem.2.1 RankOneModule.wholeReduced_le_sylow
      (le_sup_right.trans RankOneModule.wholeReduced_normalized) h.sylow_normalizes hz
  exact bot_unique ((inf_le_inf_right _ D.le_reduced).trans_eq hw)

private theorem seed_chapterK_of_ff
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hff : IsFFModule D.seedRepresentation) :
    ChapterK.RankOne.SourceHypotheses D.seedRepresentation D.componentImage := by
  refine ⟨D.seed_sqtk h.original_section1221
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X)),
    D.seed_fitting h.quotient_quasisimple,
    D.componentImage_quasisimple h.quotient_quasisimple,
    subspaceImageRepresentation_injective _ _,D.seed_irreducible hc,?_⟩
  exact (cubicRatio_le_quadraticRatio _).trans
    (((isFFModule_iff_quadraticRatio_le_one _).mp hff).trans (by norm_num))

/-- A moved chosen constituent forces field degree two. The natural row
is invariant under all component automorphisms; the orthogonal FF row has
half-degree one. -/
theorem localCartan_degree_two_of_moved_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hm : V < componentOrbit V (T : Subgroup G)) : n = 2 := by
  have hff := D.seed_ff_of_moved h.original_section1221 (D.orbit_bound h) hc hm
  have hs := D.seed_chapterK_of_ff h hc hff
  let a := MulEquiv.ofBijective D.componentQuotientHom
    ⟨quotient_action_injective h _ D.componentQuotientHom_surjective,
      D.componentQuotientHom_surjective⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ea := a.symm.trans (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
  obtain ⟨_,hnat | ⟨s,he,_,hp,_,⟨M⟩⟩⟩ :=
    hs.binary_recognition ea n (by have := h.exponent; omega) hF
  · obtain ⟨M⟩ := hnat.2
    let b : ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
        (SL2.BinarySmall.natural (K := F)) :=
      ⟨M.groupEquiv,M.coordinates,M.intertwines⟩
    have hn := D.sylow_normalizes_of_model_twists h.quotient_quasisimple hc
      (SL2.BinarySmall.natural (K := F)) (Theory.PSL2.sl2_center_eq_bot F) b
      (linear_two_natural_twist (F := F))
    exact (hm.not_ge (iSup_conjugates_le_of_le_normalizer V T V le_rfl hn)).elim
  · let : NeZero s := ⟨hp.ne'⟩
    rcases (hs.orthogonal_case M).2 with hn | ⟨hs1,_⟩
    · exact (hn.2.2.2 hff).elim
    · omega


omit D in
private theorem irreducible_restricted_congr {E U : Type*} [Group E]
    [AddCommGroup U] [Module (ZMod 2) U] (ρ : Representation (ZMod 2) E U)
    (K : Subgroup E) {I J : Submodule (ZMod 2) U} (he : I = J)
    (hi : Representation.IsIrreducible
      ((subspaceImageRepresentation ρ J).comp (restrictedSubgroup ρ J K).subtype)) :
    Representation.IsIrreducible
      ((subspaceImageRepresentation ρ I).comp (restrictedSubgroup ρ I K).subtype) := by
  subst I
  exact hi

private theorem orbit_chapterK_of_invariant
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hv : D.sourceOrbit = V) :
    ChapterK.RankOne.SourceHypotheses D.orbitRepresentation D.orbitComponent := by
  have he : D.orbitSpace = D.space := ReducedNormal.subspaceImage_injective
    (L ⊔ (T : Subgroup G)) (hv.trans D.image_eq.symm)
  have hi := irreducible_restricted_congr (reducedRepresentation (L ⊔ (T : Subgroup G)))
    (L.subgroupOf (L ⊔ (T : Subgroup G))) he (D.seed_irreducible hc)
  exact ⟨D.sourceOrbit_sqtk h.original_section1221,D.orbit_fitting h.original_section1221,
    D.orbitComponent_quasisimple h.original_section1221,
    subspaceImageRepresentation_injective _ _,hi,D.orbit_bound h⟩

private theorem orbit_conjugation_model
    (h : Input KnownSimple.IsKnownSimple T L W n)
    {P U k : Type*} [Group P] [AddCommGroup U] [Module (ZMod 2) U]
    [Semiring k] [Module k U] (ρ : Representation k P U)
    (a : D.orbitComponent ≃* P) (b : D.orbitSpace ≃ₗ[ZMod 2] U)
    (hb : ∀ g v, b (D.orbitRepresentation g.val v) = ρ (a g) (b v)) :
    IsConjugationModel L D.sourceOrbit ρ := by
  let q := D.orbitComponentQuotientHom h.original_section1221
  let e := MulEquiv.ofBijective q
    ⟨quotient_action_injective h q (D.orbitComponentQuotientHom_surjective h.original_section1221),
      D.orbitComponentQuotientHom_surjective h.original_section1221⟩
  let f : D.sourceOrbit ≃* Multiplicative U :=
    (D.sourceOrbitCoordinates.symm.trans b).toAddEquiv.toMultiplicative
  refine ⟨e.trans a,f,?_⟩
  intro l v
  let w := D.sourceOrbitCoordinates.symm (Additive.ofMul v)
  have he : (e.trans a) (QuotientGroup.mk' (pCore 2 L) l) =
      a (D.orbitComponentHom l) := rfl
  have hh := hb (D.orbitComponentHom l) w
  change b (D.orbitRepresentation (D.orbitComponentHom l).val w) =
    ρ (a (D.orbitComponentHom l)) (f v).toAdd at hh
  change (f.symm (Multiplicative.ofAdd
    (ρ ((e.trans a) (QuotientGroup.mk' (pCore 2 L) l)) (f v).toAdd)) : G) = _
  rw [he,←hh]
  change ((D.sourceOrbitCoordinates (b.symm
    (b (D.orbitRepresentation (D.orbitComponentHom l).val w)))).toMul : G) = _
  rw [LinearEquiv.symm_apply_apply]
  have hw : ((D.sourceOrbitCoordinates w).toMul : G) = (v : G) := by
    dsimp only [w]
    rw [LinearEquiv.apply_symm_apply]
    rfl
  rw [sourceOrbitCoordinates_apply] at hw ⊢
  change (l : G) * w.val.toMul.val.val * (l : G)⁻¹ = _
  rw [hw]

/-- An invariant chosen constituent has an actual natural or Hermitian orbit
model. The original source hypotheses supply the cubic bound and all group
and action hypotheses of Chapter K. -/
theorem localCartan_invariant_seed_models
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hc : V ⊓ centralizer (L : Set G) = ⊥) (hv : D.sourceOrbit = V) :
    IsNaturalModule L D.sourceOrbit n ∨
      ∃ s : ℕ, n = 2*s ∧ ∃ hs : 0 < s, letI : NeZero s := ⟨hs.ne'⟩;
        IsConjugationModel L D.sourceOrbit (SL2.BinarySmall.hermitian s) := by
  have hs := D.orbit_chapterK_of_invariant h hc hv
  let q := D.orbitComponentQuotientHom h.original_section1221
  let a := MulEquiv.ofBijective q
    ⟨quotient_action_injective h q (D.orbitComponentQuotientHom_surjective h.original_section1221),
      D.orbitComponentQuotientHom_surjective h.original_section1221⟩
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h.linear
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let ea := a.symm.trans (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
  obtain ⟨_,hnat | ⟨s,he,_,hp,_,⟨M⟩⟩⟩ :=
    hs.binary_recognition ea n (by have := h.exponent; omega) hF
  · obtain ⟨M⟩ := hnat.2
    exact Or.inl ⟨F,inferInstance,inferInstance,inferInstance,hF,
      D.orbit_conjugation_model h (specialLinearNatural (k := F) 2)
        M.groupEquiv M.coordinates M.intertwines⟩
  · let : NeZero s := ⟨hp.ne'⟩
    exact Or.inr ⟨s,he,hp,D.orbit_conjugation_model h (SL2.BinarySmall.hermitian s)
      M.groupEquiv M.coordinates M.intertwines⟩

/-- Exhaustive chosen-seed analysis forces degree two under the original
component witness, with no supplied model or seed-invariance premise. -/
theorem localCartan_degree_two_of_chosen_seed
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) : n = 2 := by
  have hXC := localCartan_centralizes h hH hgen c hY d
  have hHC := (residual_le_omegaCentralizer_iff hH.1.1.2).mp (d.residual_le.trans hXC)
  have hc := D.fixed_seed h hH hHC
  by_cases hv : D.sourceOrbit = V
  · rcases D.localCartan_invariant_seed_models h hc hv with hn | ⟨s,he,hp,hm⟩
    · exact (not_natural_of_cubic_centralizes_omega
        (inferInstance : IsElementaryAbelian 2 D.sourceOrbit)
        D.sourceOrbit_weakClosure_setup.le_sylow D.sourceOrbit_weakClosure_setup.normalizes
        D.sourceOrbit_weakClosure_setup.nontrivial
        ((d.cubic_le.trans inf_le_left).trans (c.left_le.trans inf_le_left))
        d.cubic_card ((d.cubic_le.trans inf_le_right).trans hXC) hn).elim
    · let : NeZero s := ⟨hp.ne'⟩
      exact (localCartan_escape_of_hermitian_subgroup h hH hgen c hY d s
        inferInstance D.sourceOrbit_weakClosure_setup.le_sylow
        D.sourceOrbit_weakClosure_setup.normalizes D.sourceOrbit_weakClosure_setup.nontrivial hm).1
  · apply D.localCartan_degree_two_of_moved_seed h hc
    exact lt_of_le_of_ne (le_componentOrbit V T) (fun he => hv (D.sourceOrbit_eq.trans he.symm))

end CFSG.Quasithin.Chapter12.Section02.ChosenModule

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L W H A B Y X C : Subgroup G} {n : ℕ}

/-- The original component and inverted cubic force degree two. The chosen
constituent is selected from the original input, with no invariance or model
assumption and without replacing the original reduced subgroup W. -/
theorem localCartan_degree_two
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) : n = 2 := by
  obtain ⟨V,⟨D⟩⟩ := h.original_section1221.exists_chosen_of_normalizes h.sylow_normalizes
  exact D.localCartan_degree_two_of_chosen_seed h hH hgen c hY d

/-- A single genuine component witness gives the full exceptional conclusion
for the original W, including relocation to the whole omega centralizer. -/
theorem localCartan_escape_of_witness
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) :
    n = 2 ∧ CartanExceptionalConclusion T L W H := by
  have hn := localCartan_degree_two h hH hgen c hY d
  refine ⟨hn,?_⟩
  subst n
  exact localCartan_escape_of_witness_degree_two h hH hgen c hY d

/-- The full original moved layer is one or two A₅ modules. This discharges
the module-recognition source cut, including multiplicity and splitting. -/
theorem localCartan_moduleRecognition : LocalCartanModuleRecognition G := by
  intro T L W n h H hH hgen A B c Y hY X C d _
  exact (localCartan_escape_of_witness h hH hgen c hY d).2.1

/-- Both original local centralization obligations hold for every Sylow and
reduced module choice, ready for the changed-Sylow use in 5.2.2. -/
theorem localCartan_centralization :
    LocalCartanCentralization KnownSimple.IsKnownSimple G := by
  intro T L W n h H hH hgen A B c Y hY X C d
  exact ⟨localCartan_centralizes h hH hgen c hY d,
    (localCartan_escape_of_witness h hH hgen c hY d).2.1⟩

/-- The original escape now requires only the component-and-inverted-cubic
sieve. The centralization and complete module-recognition cuts are discharged. -/
theorem sourceLocalCartanEscape_of_sieve
    (hsieve : LocalCartanSieve KnownSimple.IsKnownSimple G) :
    SourceLocalCartanEscape KnownSimple.IsKnownSimple G := by
  intro T L W n h H hH hgen A B c Y hY hescape
  obtain ⟨X,C,d⟩ := hsieve T L W n h H hH hgen A B c Y hY hescape
  exact (localCartan_escape_of_witness h hH hgen c hY d).2

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
