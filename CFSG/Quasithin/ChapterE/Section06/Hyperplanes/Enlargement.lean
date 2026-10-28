module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.FixedSpaces
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic

/-!
# Conditional component and block enlargement implications

The component-lifting alternative in a corank-two centralizer has only the
A₅-in-A₇ exception. E.6.18 excludes it, so the original component and its
conjugate are components of the same centralizer and either agree or commute.
The bound on the actual conjugacy family then gives the forbidden fixed
space from `FixedSpaces`. Odd-core vanishing turns absence of components
into the intrinsic equality F*(C_G(U)) = O₂(C_G(U)).

For the second implication, r = 1 selects an escaping hyperplane; the
earlier E.6.10 decomposition supplies an actual A₃/A₅ block. Once the block
enlargement and conjugacy bound are supplied, the same fixed-space argument
excludes r = 1. No unconditional numbered E.6.23 is asserted.

The component model inspection, proper block enlargement, and local bound
on the number of conjugates remain explicit outstanding contracts. This
assembly owner is incomplete until they are proved. Earlier E.6.10, E.6.13,
the indicated Chapter 1 facts, E.6.18 and E.6.21 are permitted source inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.22–23,
printed pp.253–255 (PDF pp.264–266).
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
open ComponentBalance

variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

omit [Finite G] in
/-- Conjugation transports ordinary components between the actual centralizers. -/
theorem centralizerComponent_conjugate {U L : Subgroup G}
    (hL : CentralizerComponent U L) (g : G) :
    CentralizerComponent (U.map (MulAut.conj g).toMonoidHom)
      (L.map (MulAut.conj g).toMonoidHom) := by
  let e := MulAut.conj g
  let C := centralizer (U : Set G)
  let C' := centralizer (U.map e.toMonoidHom : Set G)
  have he : C.map e.toMonoidHom = C' := Theory.Quasithin.map_centralizer e U
  let f : C ≃* C' := (e.subgroupMap C).trans (MulEquiv.subgroupCongr he)
  have hf : (L.subgroupOf C).map f.toMonoidHom =
      (L.map e.toMonoidHom).subgroupOf C' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, heq⟩
      exact ⟨⟨y, hL.1 hy⟩, hy, Subtype.ext heq⟩
  exact ⟨(map_mono (f := e.toMonoidHom) hL.1).trans he.le, hf ▸ hL.2.map_equiv f⟩

omit [Finite G] in
/-- Distinct ordinary components of the same centralizer commute in G. -/
theorem centralizerComponents_equal_or_commute {A L J : Subgroup G}
    (hL : CentralizerComponent A L) (hJ : CentralizerComponent A J) :
    L = J ∨ ⁅L, J⁆ = ⊥ := by
  by_cases he : L = J
  · exact Or.inl he
  · right
    have hne : L.subgroupOf (centralizer (A : Set G)) ≠
        J.subgroupOf (centralizer (A : Set G)) := by
      intro hh
      have hm := congrArg (Subgroup.map (centralizer (A : Set G)).subtype) hh
      rw [map_subgroupOf_eq_of_le hL.1, map_subgroupOf_eq_of_le hJ.1] at hm
      exact he hm
    have hc := congrArg (Subgroup.map (centralizer (A : Set G)).subtype)
      (hL.2.commutator_eq_bot_of_ne hJ.2 hne)
    simpa only [map_commutator, map_subgroupOf_eq_of_le hL.1,
      map_subgroupOf_eq_of_le hJ.1, Subgroup.map_bot] using hc

omit [Finite G] in
/-- The E.6.18 exclusion removes precisely the exceptional proper enlargement. -/
theorem component_persists_of_lift_alternative
    (h18 : SevenExcluded M V) (hlift : ComponentLiftAlternative M V)
    {U A L : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hL : CentralizerComponent U L) (hA : A ∈ obstructionFamily M V)
    (hAU : A ≤ U) (hc : subgroupCorank V A ≤ 2) : CentralizerComponent A L := by
  obtain ⟨X, _, hX, he | ⟨_, hseven⟩⟩ := hlift U hU hUh L hL A hA hAU hc
  · exact he ▸ hX
  · exact (h18 A hA hc X hX hseven).elim

omit [Finite G] in
private theorem escape_conjugate {L : Subgroup G} (he : ¬ L ≤ M)
    {g : G} (hg : g ∈ M) : ¬ L.map (MulAut.conj g).toMonoidHom ≤ M := by
  intro hle
  apply he
  intro x hx
  have hc := hle (mem_map_of_mem (MulAut.conj g).toMonoidHom hx)
  have hh := M.mul_mem (M.mul_mem (M.inv_mem hg) hc) hg
  simpa [MulAut.conj_apply, mul_assoc] using hh

/-- Enlarge both conjugate components into the same corank-two centralizer. -/
theorem component_commutingConjugates [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (hm : 2 < localM V) (h18 : SevenExcluded M V)
    (hlift : ComponentLiftAlternative M V)
    {U L : Subgroup G} (hU : U ∈ obstructionFamily M V) (hUh : IsHyperplane V U)
    (hL : CentralizerComponent U L) (he : ¬ L ≤ M) : CommutingConjugates M V L := by
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  have hUg : IsHyperplane V (U.map f) :=
    ⟨(map_mono (f := f) hUh.1).trans (mem_normalizer_iff_map_conj_eq.mp hg.2).le,
      (corank_conjugate V U g hg.2).trans hUh.2⟩
  have hLg := centralizerComponent_conjugate hL g
  have heg : ¬ L.map f ≤ M := escape_conjugate he hg.1
  have hUgG : U.map f ∈ obstructionFamily M V :=
    small_escape_mem h hUg.1 (by rw [hUg.2]; omega) (fun hc => heg (hLg.1.trans hc))
  have hcor : subgroupCorank V (U ⊓ U.map f) ≤ 2 := by
    have hc := corank_inf_le (V := V) U (U.map f)
    rw [hUh.2, hUg.2] at hc
    exact hc
  have hAG : U ⊓ U.map f ∈ obstructionFamily M V :=
    small_escape_mem h (inf_le_left.trans hUh.1) (by omega)
      (fun hc => he ((hL.1.trans (Subgroup.centralizer_le inf_le_left)).trans hc))
  exact centralizerComponents_equal_or_commute
    (component_persists_of_lift_alternative h18 hlift hU hUh hL hAG inf_le_left hcor)
    (component_persists_of_lift_alternative h18 hlift hUgG hUg hLg hAG inf_le_right hcor)

private theorem exists_component_of_oddCore_eq_bot {H : Subgroup G}
    (ho : pPrimeCore 2 H = ⊥) (hf : generalizedFitting H ≠ pCore 2 H) :
    ∃ L : Subgroup G, L ≤ H ∧ IsComponent H (L.subgroupOf H) := by
  have hex : ∃ J : Subgroup H, IsComponent H J := by
    by_contra! hn
    have he : componentLayer H = ⊥ := sSup_eq_bot.mpr fun J hJ => (hn J hJ).elim
    apply hf
    rw [generalizedFitting, he, sup_bot_eq, Fitting_eq_pcore H 2 ho]
  obtain ⟨J, hJ⟩ := hex
  refine ⟨J.map H.subtype, map_subtype_le J, ?_⟩
  have he : (J.map H.subtype).subgroupOf H = J := by
    ext x
    constructor
    · rintro ⟨y, hy, heq⟩
      exact (Subtype.ext heq : y = x) ▸ hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  rw [he]
  exact hJ

/-- Conditional E.6.22 implication. The component inspection and actual
orbit bound are outstanding obligations, not assumptions of characteristic two. -/
theorem characteristicTwo_of_component_enlargement [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h15 : HypothesisE615 V) (earlier : EarlierLocalFacts T)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (hlift : ComponentLiftAlternative M V) (hbound : TwoConjugates M V) :
    ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)) := by
  intro U hUh
  by_contra hf
  have hescape : ¬ centralizer (U : Set G) ≤ M := by
    intro hc
    have hh := h.lemma_E_6_6_2 earlier (hUh.1.trans (h.le_sylow.trans h.sylow_le))
      ((IsElementaryAbelian.isPGroup 2 V).to_le hUh.1)
    rw [inf_eq_right.mpr hc] at hh
    exact hf hh
  obtain ⟨_, hm, hU⟩ := lemma_E_6_16_1 h h15 hUh hescape
  obtain ⟨L, hL⟩ := exists_component_of_oddCore_eq_bot (h21 U hU.1 hU.2.1) hf
  have he := Components.component_not_le h earlier hU hL
  have hcomm := component_commutingConjugates h hm h18 hlift hU hUh hL he
  exact no_two_conjugates h h13 hm hUh hL.1 he (hbound U hU hUh L (Or.inl hL) he hcomm)

/-- With characteristic two established, E.6.10 selects an actual block;
the enlargement and orbit arguments then rule out r = 1. -/
theorem rank_gt_one_of_block_enlargement [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h10 : EarlierBlockSelection M V)
    (hchar : ∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G)))
    (hblocks : BlockEnlargement M V) (hbound : TwoConjugates M V)
    (hm : 2 < localM V) : 1 < globalR V := by
  by_contra hn
  have hr : globalR V = 1 := le_antisymm (le_of_not_gt hn) (one_le_globalR V)
  have hs : globalR V < (localM V : ℕ∞) := by
    rw [hr]
    exact_mod_cast (show 1 < localM V by omega)
  obtain ⟨U, hU, hc⟩ := h.exists_minimal_obstruction hs
  have hUh : IsHyperplane V U := ⟨hU.1, by exact_mod_cast hc.trans hr⟩
  obtain ⟨L, hL, he⟩ := h10 U hU hUh (hchar U hUh)
  exact no_two_conjugates h h13 hm hUh hL.1 he
    (hbound U hU hUh L (Or.inr hL) he (hblocks U hU hUh L hL he))

/-- The conditional enlargement implication feeding the E.6.23 assembly.
The three new contracts must still be discharged by this module's owner. -/
theorem conditional_enlargement_implication [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T)
    (h10 : EarlierBlockSelection M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (h18 : SevenExcluded M V) (h21 : OddCoreFree V)
    (hlift : ComponentLiftAlternative M V) (hbound : TwoConjugates M V)
    (hblocks : (∀ U : Subgroup G, IsHyperplane V U →
      generalizedFitting (centralizer (U : Set G)) = pCore 2 (centralizer (U : Set G))) →
        BlockEnlargement M V)
    (hm : 2 < localM V) : 1 < globalR V := by
  have hchar := characteristicTwo_of_component_enlargement h (Or.inr hm) earlier
    h13 h18 h21 hlift hbound
  exact rank_gt_one_of_block_enlargement h h13 h10 hchar (hblocks hchar) hbound hm

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement
