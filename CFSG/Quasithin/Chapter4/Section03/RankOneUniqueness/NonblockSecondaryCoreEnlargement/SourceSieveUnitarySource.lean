module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryCoreEnlargement.SourceGeometry
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitaryParabolic

/-!
# The quintic bound and index contradiction from corrected source data

The natural and doubled-dual sections give a fixed index at most 2^12 on Q.
For B=R₂∩K, the quotient R₂/B is centralized by the quintic. The remaining
section B/(B∩Q) embeds as a two-subgroup of SL₃(4), has order at most 64,
and contributes at most 2^4. This controls the whole literal R₂, including
its possible contribution outside K, and proves the bound 2^16.

An actual extraspecial Sylow five-group with center in K₂ would force a
fixed index at least 2^20 on O₂(K_Z)≤R₂. The final consumer discharges the
numerical bound and applies this contradiction using the original two
subtype maps. It retains the marking as an explicit input: the legacy
marking proof's inner-action step uses universal radical movement and
cannot be transferred merely by forgetting that field.

These are additive source variants; all legacy interfaces remain unchanged.
The source marking, MS construction and final nonblock contradiction remain
with `qt-d-1222-rankone-uniqueness-nonblock`.
Source: Aschbacher--Smith, conclusion of original 4.3.2, printed p.618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Representation.BinaryFixedPoints
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

/-- A Sylow five-group in the actual secondary component, whose embedded
center lies in the literal K₂. This is a construction target, not a source theorem. -/
structure UnitaryFiveMarking (s : SecondaryActionData c n) where
  actor : Subgroup G
  le_component : actor ≤ s.component.map (rootNormalizer c).subtype
  extraspecial : IsExtraspecial 5 actor
  card : Nat.card actor = 5 ^ 3
  center_le_secondary : (center actor).map actor.subtype ≤ secondary c
  sylow : ∃ P : Sylow 5 s.component,
    ((P : Subgroup s.component).map s.component.subtype).map (rootNormalizer c).subtype = actor

/-- Characteristic two for the original secondary component, transported to G. -/
theorem unitaryFive_component_core_selfCentralizing (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L) :
    let H := s.component.map (rootNormalizer c).subtype
    centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hlocal : IsTwoLocal (rootNormalizer c) := by
    let := c.c28.module_elementary
    exact ⟨root c, root_ne_bot c D,
      (IsElementaryAbelian.isPGroup 2 (W c)).to_le inf_le_left, rfl⟩
  have hchar : HasCharacteristicTwo (rootNormalizer c) :=
    Chapter1.mem_He_iff.mp (Chapter1.twoLocal_mem_He_of_sylow_le T
      (h.simpleQTKE.evenCharacteristic T) hlocal (root_normalized c D))
  have hc := subnormal_core_selfCentralizing hchar s.component s.isComponent.subnormal
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2
    (s.component.equivMapOfInjective (rootNormalizer c).subtype
      (rootNormalizer c).subtype_injective)).mp hc

omit [Finite G] in
/-- The embedded component core lies in the same R₂ used in the index bound. -/
theorem unitaryFive_component_core_le (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V) :
    (s.component.map (rootNormalizer c).subtype).pCoreIn 2 ≤ R₂ c := by
  let := s.normal
  have hn : rootNormalizer c ≤ normalizer
      (s.component.map (rootNormalizer c).subtype : Set G) := by
    have hh := s.component.le_normalizer_map (rootNormalizer c).subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  exact (pCoreIn_mono_of_normalizes le_sup_left
    ((sup_le (map_subtype_le _) (root_normalized c D)).trans hn)).trans s.enlarged_core_le

/-- Conditional assembly of the central-index contradiction. Both the marked
Sylow construction and the parabolic bound remain separate source obligations. -/
theorem unitaryFive_false_of_marking_and_bound (s : SecondaryActionData c n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (m : UnitaryFiveMarking s) (hbound : QuinticRadicalBound c) : False := by
  let H := s.component.map (rootNormalizer c).subtype
  let C := H.pCoreIn 2
  let P := m.actor
  let : IsExtraspecial 5 P := m.extraspecial
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hc : H ⊓ centralizer (C : Set G) ≤ C := by
    intro x hx
    have hh : (⟨x,hx.1⟩ : H) ∈ centralizer (pCore 2 H : Set H) := by
      intro y hy
      apply Subtype.ext
      exact hx.2 y (mem_map_of_mem _ hy)
    exact mem_map_of_mem H.subtype (unitaryFive_component_core_selfCentralizing s D h hh)
  have hdis : P ⊓ C = ⊥ :=
    (IsPGroup.disjoint_of_ne 5 2 (by decide) P C
      (IsPGroup.of_card m.card) (isPGroup_pCoreIn 2 H)).eq_bot
  have hf : P ⊓ centralizer (C : Set G) = ⊥ :=
    bot_unique ((le_inf inf_le_left ((inf_le_inf_right _ m.le_component).trans hc)).trans_eq hdis)
  have hn : P ≤ normalizer (C : Set G) :=
    m.le_component.trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))
  have hl := ExtraspecialQuinticCenter.centralizer_relIndex_lower_bound P C m.card
    (isPGroup_pCoreIn 2 H) hn hf
  have hX : Nat.card ((center P).map P.subtype) = 5 := by
    rw [card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 5 P
  have hu := hbound _ m.center_le_secondary hX
  have hm := (centralizer ((center P).map P.subtype : Set G)).relIndex_le_of_le_right
    (unitaryFive_component_core_le s D)
    (Subgroup.FiniteIndex.index_ne_zero (H :=
      (centralizer ((center P).map P.subtype : Set G)).subgroupOf (R₂ c)))
  have hnum : 2 ^ 20 ≤ (2 : ℕ) ^ 16 := hl.trans (hm.trans hu)
  norm_num at hnum

private theorem two_subgroup_sl3_card {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 4) (P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F))
    (hP : IsPGroup 2 P) : Nat.card P ≤ 64 := by
  obtain ⟨m, hm⟩ := hP.exists_card_eq
  have hd := P.card_subgroup_dvd_card
  rw [Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear, hF, hm] at hd
  have hc : Nat.Coprime (2 ^ m) 945 := (by decide : Nat.Coprime 2 945).pow_left m
  have hd' : 2 ^ m ∣ 64 := hc.dvd_of_dvd_mul_right (by norm_num at hd ⊢; exact hd)
  rw [hm]
  exact Nat.le_of_dvd (by decide) hd'

/-- The actual radical has at most sixteen moving binary dimensions for any quintic in K₂. -/
theorem quintic_radical_index_bound (d : MSData c 2) (s : SecondaryActionData c 2)
    (X : Subgroup G) (hX : X ≤ secondary c) (hcard : Nat.card X = 5) :
    (centralizer (X : Set G)).relIndex (R₂ c) ≤ 2 ^ 16 := by
  have hsec : secondary c ≤ K c := (map_subtype_le _).trans inf_le_left
  have hXK := hX.trans hsec
  have hXR : X ≤ normalizer (R₂ c : Set G) :=
    (hX.trans le_sup_left).trans ((secondary c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (secondary c ⊔ S c)
        (pCore 2 (secondary c ⊔ S c : Subgroup G))))
  have hRK : R₂ c ≤ normalizer (K c : Set G) :=
    (pCoreIn_le 2 (secondary c ⊔ S c)).trans
      (sup_le (hsec.trans (K c).le_normalizer)
        (inf_le_right.trans c.normalizer_component.le))
  let B := R₂ c ⊓ K c
  have hXB : X ≤ normalizer (B : Set G) :=
    (le_inf hXR (hXK.trans (K c).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  have hRB : R₂ c ≤ normalizer (B : Set G) :=
    (le_inf (R₂ c).le_normalizer hRK).trans inf_normalizer_le_normalizer_inf
  let : (B.subgroupOf (R₂ c)).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hRB
  have hRtwo : IsPGroup 2 (R₂ c) := isPGroup_pCoreIn 2 _
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (R₂ c)) := by
    obtain ⟨m, hm⟩ := hRtwo.exists_card_eq
    rw [hcard, hm]
    exact (by decide : Nat.Coprime 5 2).pow_right m
  have hcomm : ⁅R₂ c,X⁆ ≤ B :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hXR)
      ((commutator_mono le_rfl hXK).trans (le_normalizer_iff_commutator_le_right.mp hRK))
  have heq := centralizer_relIndex_eq_of_commutator_le X (R₂ c) B hRtwo hcop
    inf_le_left hXR hXB hcomm
  have hB : B ≤ K c := inf_le_right
  let f := linearThreeActor d.model
  have hf : f.ker = pCore 2 (K c) := by
    dsimp only [f, linearThreeActor]
    rw [MonoidHom.ker_comp_of_injective _ _ d.model.injective, QuotientGroup.ker_mk']
  have hi : (Q c).relIndex B = Nat.card ((B.subgroupOf (K c)).map f) := by
    rw [s.core_eq_original, ← relIndex_subgroupOf hB]
    have hk : ((K c).pCoreIn 2).subgroupOf (K c) = pCore 2 (K c) := by
      exact comap_map_eq_self_of_injective (K c).subtype_injective _
    rw [hk, ← hf, relIndex_ker]
  have hF : Nat.card d.field.Carrier = 4 := by rw [d.field.card_eq, d.degree_eq]; rfl
  have hmodel : IsPGroup 2 ((B.subgroupOf (K c)).map f) :=
    ((hRtwo.to_le (show B ≤ R₂ c from inf_le_left)).of_equiv
      (subgroupOfEquivOfLe hB).symm).map f
  have hbound : (Q c).relIndex B ≤ 64 := by
    rw [hi]
    exact two_subgroup_sl3_card hF _ hmodel
  let N := Q c ⊓ B
  have hN : N ≤ B := inf_le_right
  have hBN : B ≤ normalizer (N : Set G) :=
    (le_inf (hB.trans d.doubleDual.2.1) B.le_normalizer).trans inf_normalizer_le_normalizer_inf
  let : (N.subgroupOf B).Normal := (normal_subgroupOf_iff_le_normalizer hN).mpr hBN
  have hXN : X ≤ normalizer (N : Set G) :=
    (le_inf (hXK.trans d.doubleDual.2.1) hXB).trans inf_normalizer_le_normalizer_inf
  let := quotientConjugationAction X B N hXB hXN
  have hcardquot : Nat.card (B ⧸ N.subgroupOf B) ≤ 64 := by
    change N.relIndex B ≤ 64
    simpa only [N, inf_relIndex_right] using hbound
  have hBtwo := hRtwo.to_le (show B ≤ R₂ c from inf_le_left)
  have hXfive : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by simpa using hcard)
  have hquot := FixedPoints.quintic_index_le_sixteen hXfive (hBtwo.to_quotient _) hcardquot
  have hNbound : (centralizer (X : Set G)).relIndex N ≤ 2 ^ 12 :=
    ((centralizer (X : Set G)).relIndex_le_of_le_right (show N ≤ Q c from inf_le_left)
      (Subgroup.FiniteIndex.index_ne_zero (H := (centralizer (X : Set G)).subgroupOf (Q c)))).trans
        (quintic_core_bound d X hXK hcard)
  have hcopB : Nat.Coprime (Nat.card X) (Nat.card B) := by
    obtain ⟨m, hm⟩ := hBtwo.exists_card_eq
    rw [hcard, hm]
    exact (by decide : Nat.Coprime 5 2).pow_right m
  rw [heq, centralizer_relIndex_eq_quotient_mul X B N hBtwo hcopB hN hXB hXN]
  exact (Nat.mul_le_mul hquot hNbound).trans_eq (by norm_num)

/-- The parabolic calculation discharges the bound in the unitary endgame contract. -/
theorem quinticRadicalBound (d : MSData c 2) (s : SecondaryActionData c 2) :
    QuinticRadicalBound c :=
  quintic_radical_index_bound d s


/-- The actual whole-radical bound discharges the numerical premise in the
source marking contradiction. Construction of the marking remains explicit. -/
theorem unitaryFive_false_of_source_marking
    (d : MSData c 2) (s : SecondaryActionData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (m : UnitaryFiveMarking s) : False :=
  unitaryFive_false_of_marking_and_bound s D h m (quinticRadicalBound d s)

/-- Forgetting the legacy movement field preserves an existing literal marking. -/
def legacyMarking_toSource {s : SecondaryData c n}
    (m : Nonblock.UnitaryFiveMarking s) : UnitaryFiveMarking s.toSourceData.toActionData where
  actor := m.actor
  le_component := m.le_component
  extraspecial := m.extraspecial
  card := m.card
  center_le_secondary := m.center_le_secondary
  sylow := m.sylow

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock.EndgameSieve
