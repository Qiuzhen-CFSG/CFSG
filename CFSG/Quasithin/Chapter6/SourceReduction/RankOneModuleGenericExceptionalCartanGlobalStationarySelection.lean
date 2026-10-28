module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalNaturalSeed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalHermitianSeed
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRecognition
public import CFSG.Quasithin.Chapter12.Section02.ChosenModule.InsideReducedWitness

/-!
# Selecting the stationary Cartan constituent and closing its natural row

Thompson centralization of the original reduced module forces every
actual H-star comparison group to centralize Ω₁Z(T). Maximal-local
uniqueness removes the fixed vectors. It also makes the original
omega-span noncentral, allowing homogeneous selection inside that exact
span rather than an arbitrary ambient module.

A moved Sylow orbit forces degree two. Otherwise Chapter K gives actual
natural or Hermitian coordinates with the original quotient marking.
The preceding natural-constituent theorem gives degree two or four and
small Cartan generation in the natural row. The higher-degree
Hermitian constituent retains its containment, Sylow invariance and zero
fixed space. Applying the torus argument on that constituent gives degree
four or eight and completes small generation in the stationary branch,
without identifying it with the whole omega-span. The eventual prime-pair
recognition remains with final assembly.

Source: Aschbacher--Smith 5.1.2(1), 5.1.3 and 5.1.6, pp.630--633,
using 3.1.8, D.3.10 and K.3.1 (`refs/quasithin.pdf`).
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative MatrixGroups
open Representation.OrthogonalFourMinus
local instance cartanGlobalStationaryFixedFieldAlgebra (s : ℕ) : Algebra (ZMod 2) (FiniteModel.fixedField s) :=
  ZMod.algebra _ 2
local instance cartanGlobalStationaryBinarySpace (s : ℕ) [NeZero s] : Module (ZMod 2) (FiniteModel.Space s) :=
  Module.compHom (FiniteModel.Space s) (algebraMap (ZMod 2) (FiniteModel.fixedField s))
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
open Chapter12.Section02
variable {G : Type*} [Group G] [Finite G]

/-- Source 3.1.8 centralizes omega in the stationary Thompson branch. -/
theorem Input.omega_centralizes_of_thompson_centralizes
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    H ≤ omegaCentralizer T := by
  have hz : omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    by_contra hn
    exact h.thompson_moves_of_noncentral_omega hH hn hj
  intro x hx z hz'
  obtain ⟨a,ha,rfl⟩ := hz hz'
  exact (congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)).symm

/-- Above degree two, an actual constituent inside the omega-span is
Sylow invariant and has natural or Hermitian coordinates. -/
theorem Input.omega_seed_models_of_outside_centralizes
    {T : Sylow 2 G} {L W H : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hHC : H ≤ omegaCentralizer T) (hn : n ≠ 2) :
    ∃ (U : Subgroup G) (D : ChosenModule T L U),
      U ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ∧
      D.sourceOrbit = U ∧ U ⊓ centralizer (L : Set G) = ⊥ ∧
      (IsNaturalModule L U n ∨
        ∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨by omega⟩;
          IsConjugationModel L U (SL2.BinarySmall.hermitian s)) := by
  have hLC : ¬ L ≤ omegaCentralizer T := by
    intro hc
    have hz := h.centralOmega_disjoint_of_outside_centralizes hH hHC
    have hW0 : W ≠ ⊥ := fun he => h.noncentral (by rw [he,commutator_bot_left])
    obtain ⟨z,hz1⟩ := ne_bot_iff_exists_ne_one.mp
      (inf_centerIn_ne_bot T.isPGroup' hW0 h.reduced_le_sylow
        (le_sup_right.trans (reduced_normalizes h.reduced)))
    let := h.reduced.2.1
    have hzZ : (z:G) ∈ omegaOneCenterAmbient (T : Subgroup G) :=
      (mem_omegaOneCenterAmbient_iff _ _).mpr
        ⟨h.reduced_le_sylow z.property.1,
          elemPow_eq_one_of_isElementaryAbelian (p:=2) (z:G) z.property.1,z.property.2.2⟩
    exact hz1 (Subtype.ext (mem_bot.mp (hz.le ⟨hzZ,(le_centralizer_iff.mp hc) hzZ⟩)))
  let hi := h.omega_span_input hLC
  let M := L ⊔ (T : Subgroup G)
  let V := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let : Group.IsPerfect L := Chapter1.mem_L_isPerfect h.maximal_local.1
  have hm : ⁅V.subgroupOf M,L.subgroupOf M⁆ ≠ ⊥ := by
    intro he
    apply hi.noncentral
    have hh := congrArg (map M.subtype) he
    have hVm : (V.subgroupOf M).map M.subtype = V :=
      map_subgroupOf_eq_of_le hi.reduced.1
    rw [map_commutator,hVm,
      map_subgroupOf_eq_of_le (show L ≤ M from le_sup_left),Subgroup.map_bot] at hh
    exact hh
  obtain ⟨U,⟨D⟩,hUV⟩ := exists_chosen_le_reduced_witness h.sylow_normalizes
    (V.subgroupOf M) hi.reduced_internal hm
  rw [map_subgroupOf_eq_of_le hi.reduced.1] at hUV
  have hc : U ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hUV).trans_eq
      (hi.reduced_fixed_eq_bot_of_outside_centralizes hH hHC))
  have hv : D.sourceOrbit = U := by
    by_contra he
    exact hn (D.localCartan_degree_two_of_moved_seed h hc
      (lt_of_le_of_ne (le_componentOrbit U T)
        (fun hh => he (D.sourceOrbit_eq.trans hh.symm))))
  refine ⟨U,D,hUV,hv,hc,?_⟩
  rcases D.localCartan_invariant_seed_models h hc hv with hm | ⟨s,he,hp,hm⟩
  · exact Or.inl (hv ▸ hm)
  · exact Or.inr ⟨s,he,by have := h.exponent; omega,hv ▸ hm⟩

/-- In the stationary Thompson branch, natural constituents already give
small generation. The sole remaining high-degree module row has an actual
Hermitian constituent inside the same original omega-span. -/
theorem Input.cartan_stationary_small_or_hermitian_seed
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hz : (A ⊔ H).pCoreIn 2 = ⊥)
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    H ≤ omegaCentralizer T ∧
      ((n = 2 ∨ n = 4) ∧ CartanSmallGeneration A H n ∨
       ∃ (U : Subgroup G) (D : ChosenModule T L U),
        U ≤ conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L ∧
        D.sourceOrbit = U ∧ U ⊓ centralizer (L : Set G) = ⊥ ∧
        ∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨by omega⟩;
          IsConjugationModel L U (SL2.BinarySmall.hermitian s)) := by
  have hHC := h.omega_centralizes_of_thompson_centralizes hH hj
  refine ⟨hHC,?_⟩
  by_cases hn : n = 2
  · exact Or.inl ⟨Or.inl hn,h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inl hn)⟩
  obtain ⟨U,D,hUV,hv,hc,hm⟩ := h.omega_seed_models_of_outside_centralizes hH hHC hn
  rcases hm with hm | hm
  · let := D.elementary
    have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
      rw [←hv]
      exact D.sourceOrbit_weakClosure_setup.normalizes
    have hb := h.natural_seed_cartan_degree_le_four hH c D.le_sylow hTU D.ne_bot hm hHC hz
    obtain ⟨k,hk⟩ := h.cartan_even_of_zero_core hH c hz
    have hn4 : n = 4 := by have := h.exponent; omega
    exact Or.inl ⟨Or.inr hn4,h.cartanSmallGeneration_of_degree_two_or_four hH c (Or.inr hn4)⟩
  · exact Or.inr ⟨U,D,hUV,hv,hc,hm⟩


/-- Both stationary constituent rows give small Cartan generation. The
Hermitian torus factors are constructed on the selected constituent itself,
so no equality with the entire omega-span or model callback remains. -/
theorem Input.cartanSmallGeneration_of_thompson_centralizes
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hcontrol : CartanLocalControl A H)
    (hescape : ¬ A ≤ normalizer (residual H : Set G))
    (hj : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G)) :
    H ≤ omegaCentralizer T ∧ CartanSmallGeneration A H n := by
  have hz := hcontrol.core_eq_bot_of_not_normalizes le_rfl hescape
  obtain ⟨hHC,hs | ⟨U,D,hUV,hv,hc,s,he,hpos,hm⟩⟩ :=
    h.cartan_stationary_small_or_hermitian_seed hH c hz hj
  · exact ⟨hHC,hs.2⟩
  · let : NeZero s := ⟨by omega⟩
    let := D.elementary
    have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
      rw [←hv]
      exact D.sourceOrbit_weakClosure_setup.normalizes
    exact ⟨hHC,(h.hermitian_seed_degree_and_smallGeneration hH c D.le_sylow hTU
      D.ne_bot s hpos hm hHC hcontrol hescape).2⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
