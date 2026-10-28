module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Preliminaries
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.OddCoreGeneration
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.Contracts
public import Theory.Quasithin.EvenCharacteristic

/-!
# Reduction of E.6.18–19 to the component inspections

An ordinary component restricts to the centralizer of its full fixed space.
For the other direction, lifting to the centralizer of each conjugate
intersection and uniqueness there imply normalization by N_G(V). The
corank-two bound and E.6.17 ensure those intersections are nonidentity.
The full fixed space then belongs to Γ and is T-invariant, contradicting
E.6.13. This proves the E.6.18 reduction.

Distinct hyperplanes have intersection of corank two and relative index two.
A failure of odd-core balance forces both subspaces into Γ, using E.6.6(2)
and E.6.16. The odd-core obstruction contract then supplies the exceptional
component to which the first reduction applies.

The new lifting, uniqueness and odd-core obstruction contracts are explicit
and remain unproved here. Thus these are conditional reductions, not completed
source E.6.18 or E.6.19. Their source assembly remains in this module.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.18–19,
printed p.252 (PDF p.263). The initial restriction argument uses the ordinary
component calculus instead of the source's longer C-component enlargement.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
variable {G : Type*} [Group G] [Finite G] {V M : Subgroup G}

omit [Finite G] in
private theorem component_conjugate {U L : Subgroup G}
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
  refine ⟨?_, hf ▸ hL.2.map_equiv f⟩
  exact (map_mono (f := e.toMonoidHom) hL.1).trans he.le

omit [Finite G] in
private theorem seven_conjugate {L : Subgroup G} (hL : IsSeven L) (g : G) :
    IsSeven (L.map (MulAut.conj g).toMonoidHom) := by
  let e := (MulAut.conj g).subgroupMap L
  rcases hL with ha | hc
  · obtain ⟨f⟩ := ha
    exact Or.inl ⟨e.symm.trans f⟩
  · obtain ⟨hq, ⟨c⟩, ⟨q⟩⟩ := hc
    let _ := hq
    have hc : (center L).map e.toMonoidHom = center (L.map (MulAut.conj g).toMonoidHom) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (centerCongr e ⟨y, hy⟩).property
      · intro hx
        exact ⟨e.symm x, ((centerCongr e).symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩
    exact Or.inr ⟨IsQuasisimple.of_mulEquiv e,
      ⟨(centerCongr e).symm.trans c⟩,
      ⟨(QuotientGroup.congr (center L) (center (L.map (MulAut.conj g).toMonoidHom)) e hc).symm.trans q⟩⟩

omit [Finite G] in
/-- Ordinary components restrict to the centralizer of their full fixed space.
This proves the initial saturation step without a C-component enlargement. -/
theorem component_fixedSpace {U L : Subgroup G} (hUV : U ≤ V)
    (hL : CentralizerComponent U L) :
    U ≤ V ⊓ centralizer (L : Set G) ∧
      CentralizerComponent (V ⊓ centralizer (L : Set G)) L := by
  have hUF : U ≤ V ⊓ centralizer (L : Set G) :=
    le_inf hUV (le_centralizer_iff.mp hL.1)
  let H := centralizer (U : Set G)
  let J := centralizer (V ⊓ centralizer (L : Set G) : Set G)
  have hLJ : L ≤ J := le_centralizer_iff.mpr inf_le_right
  have hJH : J ≤ H := Subgroup.centralizer_le hUF
  let e := subgroupOfEquivOfLe hJH
  have hc := (hL.2.subgroupOf (show L.subgroupOf H ≤ J.subgroupOf H from
    fun _ hx => hLJ hx)).map_equiv e
  have he : ((L.subgroupOf H).subgroupOf (J.subgroupOf H)).map e.toMonoidHom =
      L.subgroupOf J := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨⟨x, hJH x.property⟩, x.property⟩, hx, rfl⟩
  exact ⟨hUF, hLJ, he ▸ hc⟩

/-- Lifting to each nonidentity conjugate intersection and uniqueness there
force N_G(V) to normalize the original component. -/
theorem normalizes_component_of_lifting [IsElementaryAbelian 2 V]
    (hlift : SevenLifting V) (huniq : SevenUniqueness V)
    {U L : Subgroup G} (hUV : U ≤ V) (hL : CentralizerComponent U L)
    (hseven : IsSeven L)
    (hdim : 2 * subgroupCorank V U < Module.finrank (ZMod 2) (Additive V)) :
    normalizer (V : Set G) ≤ normalizer (L : Set G) := by
  intro g hg
  let f := (MulAut.conj g).toMonoidHom
  have hUg : U.map f ≤ V := by
    exact (map_mono (f := f) hUV).trans (mem_normalizer_iff_map_conj_eq.mp hg).le
  have hne : U ⊓ U.map f ≠ ⊥ := inf_conjugate_ne_bot g hg hdim
  have hfirst := hlift (U ⊓ U.map f) U L inf_le_left hUV hne hL hseven
  have hsecond := hlift (U ⊓ U.map f) (U.map f) (L.map f)
    inf_le_right hUg hne (component_conjugate hL g) (seven_conjugate hseven g)
  apply mem_normalizer_iff_map_conj_eq.mpr
  exact (huniq _ (inf_le_left.trans hUV) hne _ _ hfirst hsecond
    hseven (seven_conjugate hseven g)).symm

/-- The final E.6.18 contradiction, with the outstanding component lifting
and uniqueness obligations explicit. E.6.8(4) and E.6.13 are earlier inputs. -/
theorem exclude_seven_of_lifting [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h8 : SevenEscape M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hlift : SevenLifting V) (huniq : SevenUniqueness V)
    {U L : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hcor : subgroupCorank V U ≤ 2) (hL : CentralizerComponent U L) :
    ¬ IsSeven L := by
  intro hseven
  obtain ⟨W, hW, _, hLW⟩ := h8 U hU L hL hseven
  have hWescape : ¬ centralizer (W : Set G) ≤ M :=
    fun hc => hLW (inf_le_right.trans hc)
  obtain ⟨hr, hm, _⟩ := lemma_E_6_16_1 h h15 hW hWescape
  have hdim := (lemma_E_6_17 h h15 h13 hr).2
  have hnorm := normalizes_component_of_lifting hlift huniq hU.1 hL hseven (by omega)
  let F := V ⊓ centralizer (L : Set G)
  have hUF : U ≤ F := (component_fixedSpace hU.1 hL).1
  have hFc : subgroupCorank V F < localM V :=
    lt_of_le_of_lt (subgroupCorank_antitone hUF) (by omega)
  have hLF : L ≤ centralizer (F : Set G) := le_centralizer_iff.mpr inf_le_right
  have hFescape : ¬ centralizer (F : Set G) ≤ M :=
    fun hc => hLW (inf_le_left.trans (hLF.trans hc))
  have hFG := small_escape_mem h (show F ≤ V from inf_le_left) hFc hFescape
  apply h13 F hFG
  exact (le_inf h.sylow_le_normalizer
    ((h.sylow_le_normalizer.trans hnorm).trans (normalizer_le_normalizer_centralizer L))).trans
      inf_normalizer_le_normalizer_inf

private theorem relative_index (A : Subgroup G) [IsElementaryAbelian 2 V] :
    A.relIndex V = 2 ^ subgroupCorank V A := by
  rw [subgroupCorank_eq_quotient_finrank]
  exact Subgroup.relIndex_eq_two_pow_quotient_finrank V A

/-- Distinct hyperplanes meet in corank two, with index two inside either one. -/
theorem hyperplane_intersection_index [IsElementaryAbelian 2 V]
    {W W₀ : Subgroup G} (hW : IsHyperplane V W) (hW₀ : IsHyperplane V W₀)
    (hne : W ≠ W₀) :
    subgroupCorank V (W ⊓ W₀) = 2 ∧ (W ⊓ W₀).relIndex W = 2 := by
  have hw : W.relIndex V = 2 := by rw [relative_index, hW.2]; rfl
  have hw₀ : W₀.relIndex V = 2 := by rw [relative_index, hW₀.2]; rfl
  have hnle : ¬ W ≤ W₀ := by
    intro hle
    have ht := relIndex_mul_relIndex W W₀ V hle hW₀.1
    rw [hw, hw₀] at ht
    have hi : W.relIndex W₀ = 1 := by omega
    exact hne (le_antisymm hle (relIndex_eq_one.mp hi))
  have hi_ne : (W ⊓ W₀).relIndex W ≠ 1 :=
    fun hi => hnle ((relIndex_eq_one.mp hi).trans inf_le_right)
  have hi_pos : (W ⊓ W₀).relIndex W ≠ 0 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  have ht := relIndex_mul_relIndex (W ⊓ W₀) W V inf_le_left hW.1
  rw [hw] at ht
  have hb := relIndex_inf_le (H := W) (K := W₀) (L := V)
  rw [hw, hw₀] at hb
  have hi : (W ⊓ W₀).relIndex W = 2 := by omega
  refine ⟨?_, hi⟩
  have hcor := corank_inf_le (V := V) W W₀
  rw [hW.2, hW₀.2] at hcor
  rw [hi, relative_index] at ht
  interval_cases hc : subgroupCorank V (W ⊓ W₀) <;> simp_all

/-- The geometric setup for a failure of E.6.19. E.6.6(2) is used only in
its equivalent characteristic-two form to force the first centralizer outside M. -/
theorem balance_failure_setup [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h6 : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ M → IsPGroup 2 A →
      HasCharacteristicTwo ↥(M ⊓ centralizer (A : Set G)))
    {W W₀ : Subgroup G} (hW : IsHyperplane V W) (hW₀ : IsHyperplane V W₀)
    (hfail : ¬ oddCentralizer W ≤ oddCentralizer (W ⊓ W₀)) :
    W ∈ obstructionFamily M V ∧ W ⊓ W₀ ∈ obstructionFamily M V ∧
      subgroupCorank V (W ⊓ W₀) = 2 ∧ (W ⊓ W₀).relIndex W = 2 := by
  have hWne : W ≠ ⊥ := by
    intro hb
    apply hfail
    simp only [hb, bot_inf_eq]
    exact le_rfl
  have hescape : ¬ centralizer (W : Set G) ≤ M := by
    intro hc
    have hchar := h6 W hWne (hW.1.trans (h.le_sylow.trans h.sylow_le))
      ((IsElementaryAbelian.isPGroup 2 V).to_le hW.1)
    rw [inf_eq_right.mpr hc] at hchar
    have hz : oddCentralizer W = ⊥ := (oddCentralizer_eq_bot_iff W).mpr
      (pPrimeCore_eq_bot_of_centralizer_pCore_le 2 hchar)
    exact hfail (hz ▸ bot_le)
  obtain ⟨_, hm, hWG⟩ := lemma_E_6_16_1 h h15 hW hescape
  have hne : W ≠ W₀ := by
    intro he
    apply hfail
    rw [he, inf_idem]
  obtain ⟨hcor, hidx⟩ := hyperplane_intersection_index hW hW₀ hne
  refine ⟨hWG, small_escape_mem h (inf_le_left.trans hW.1) ?_ ?_, hcor, hidx⟩
  · omega
  · exact fun hc => hescape ((Subgroup.centralizer_le inf_le_left).trans hc)

/-- Conditional assembly of E.6.19. The lifting, uniqueness and odd-core
obstruction contracts still require proofs; this theorem does not discharge them. -/
theorem balance_of_component_inputs [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (h15 : HypothesisE615 V)
    (h6 : ∀ A : Subgroup G, A ≠ ⊥ → A ≤ M → IsPGroup 2 A →
      HasCharacteristicTwo ↥(M ⊓ centralizer (A : Set G)))
    (h8 : SevenEscape M V)
    (h13 : ∀ A ∈ obstructionFamily M V, ¬ (T : Subgroup G) ≤ normalizer (A : Set G))
    (hlift : SevenLifting V) (huniq : SevenUniqueness V)
    (hodd : OddCoreObstruction M V)
    {W W₀ : Subgroup G} (hW : IsHyperplane V W) (hW₀ : IsHyperplane V W₀) :
    oddCentralizer W ≤ oddCentralizer (W ⊓ W₀) := by
  by_contra hfail
  obtain ⟨_, hA, hcor, hidx⟩ := balance_failure_setup h h15 h6 hW hW₀ hfail
  obtain ⟨L, hL, hs⟩ := hodd (W ⊓ W₀) hA hcor W inf_le_left hW.1 hidx hfail
  exact exclude_seven_of_lifting h h15 h8 h13 hlift huniq hA hcor.le hL hs

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance
