module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockEndgameUnitaryMarkingSource
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.DefiningSylow
public import Theory.GroupAction.QuinticFixedIndex

/-!
# The quintic bound on the original nonblock radical

The common SL₃(4) marking identifies U with a 64-element natural module
and Q/U with two copies of its dual. The actual conjugation action of an
order-five subgroup therefore has fixed index at most 2^12 on Q.

Put B = R₂ ∩ K. The actor centralizes R₂/B, while B/(B ∩ Q) embeds in
SL₃(4) as a two-subgroup and has order at most 64. Coprime fixed-point
lifting and the orbit congruence bound its extra contribution by 2^4.
This proves the required bound 2^16 on the literal R₂ and supplies it to
the completed unitary Sylow-center marking.

The final exclusion retains the original MSData and SecondaryData explicitly.
Their construction and the linear-four branch remain with the source assembly
owner `qt-d-1222-rankone-uniqueness-nonblock`; this module does not assert
that these data exist.

Source: Aschbacher--Smith, original 4.3.10--11 and the conclusion of 4.3.2,
printed pp.617--618; C.1.34(3), printed p.137.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open Representation.BinaryFixedPoints
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L}

/-- The natural and two dual sections contribute at most twelve moving binary dimensions. -/
theorem quintic_core_bound (d : MSData c 2)
    (X : Subgroup G) (hX : X ≤ K c) (hcard : Nat.card X = 5) :
    (centralizer (X : Set G)).relIndex (Q c) ≤ 2 ^ 12 := by
  have hF : Nat.card d.field.Carrier = 4 := by rw [d.field.card_eq, d.degree_eq]; rfl
  have hUcard : Nat.card (U c) = 64 := by
    have hm := d.natural
    rw [HasSectionModel, bot_subgroupOf] at hm
    obtain ⟨_, _, _, hn, e, _⟩ := hm
    let := hn
    have hc := Nat.card_congr ((QuotientGroup.quotientBot.symm.trans e).toEquiv)
    change Nat.card (U c) = Nat.card (Fin 3 → d.field.Carrier) at hc
    norm_num [Nat.card_fun, Nat.card_fin, hF] at hc ⊢
    exact hc
  have hQN := hX.trans d.doubleDual.2.1
  have hUN := hX.trans d.natural.2.1
  have hQtwo : IsPGroup 2 (Q c) :=
    (isPGroup_pCoreIn 2 (K c)).to_le
      (le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c)))))
  have hcop : Nat.Coprime (Nat.card X) (Nat.card (Q c)) := by
    obtain ⟨m, hm⟩ := hQtwo.exists_card_eq
    rw [hcard, hm]
    exact (by decide : Nat.Coprime 5 2).pow_right m
  obtain ⟨hUQ, _, _, hn, e, he⟩ := d.doubleDual
  let := hn
  let := quotientConjugationAction X (Q c) (U c) hQN hUN
  let f : X →* Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier :=
    (linearThreeActor d.model).comp (inclusion hX)
  let σ : Representation (ZMod 2) X (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :=
    ((Representation.specialLinearNatural (k := d.field.Carrier) 3).dual.restrictScalars
      (k := ZMod 2)).comp f
  have hdual : Nat.card (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) = 64 := by
    rw [Module.natCard_eq_pow_finrank (K := d.field.Carrier), Subspace.dual_finrank_eq,
      Module.finrank_pi, hF]
    norm_num
  let : Finite (Module.Dual d.field.Carrier (Fin 3 → d.field.Carrier)) :=
    Finite.of_injective (fun f => (f : (Fin 3 → d.field.Carrier) → d.field.Carrier))
      DFunLike.coe_injective
  have heq : (FixedPoints.subgroup X (Q c ⧸ (U c).subgroupOf (Q c))).index =
      fixedIndex (σ.prod σ) := by
    let := action (σ.prod σ)
    apply FixedPoints.index_eq_of_equivariant e
    intro a q
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective ((U c).subgroupOf (Q c)) q
    apply Multiplicative.toAdd.injective
    exact he (inclusion hX a) r
      ⟨a * (r : G) * (a : G)⁻¹, (mem_normalizer_iff.mp (hQN a.property) r).mp r.property⟩ rfl
  have hquot : (FixedPoints.subgroup X (Q c ⧸ (U c).subgroupOf (Q c))).index ≤ 256 := by
    rw [heq, fixedIndex_prod]
    have hh := quintic_fixedIndex_le_sixteen σ hcard hdual
    nlinarith
  have hu : (centralizer (X : Set G)).relIndex (U c) ≤ 16 := by
    let := conjMulDistribMulActionOfLeNormalizer X (U c) hUN
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hp : IsPGroup 5 X := IsPGroup.of_card (n := 1) (by simpa using hcard)
    have hm := hp.card_modEq_card_fixedPoints (U c)
    change Nat.card (U c) % 5 = Nat.card (FixedPoints.subgroup X (U c)) % 5 at hm
    rw [fixedPoints_conjugation_eq_centralizer X (U c) hUN, hUcard] at hm
    have hc := ((centralizer (X : Set G)).subgroupOf (U c)).index_mul_card
    rw [hUcard] at hc
    have hlow : 4 ≤ Nat.card ((centralizer (X : Set G)).subgroupOf (U c)) := by omega
    change ((centralizer (X : Set G)).subgroupOf (U c)).index ≤ 16
    nlinarith
  rw [centralizer_relIndex_eq_quotient_mul X (Q c) (U c) hQtwo hcop hUQ hQN hUN]
  exact (Nat.mul_le_mul hquot hu).trans_eq (by norm_num)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock

namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
open Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {c : SourceConfiguration T L}

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

omit [Finite G] in
/-- Source 4.3.11 also identifies Q with the original component's two-core. -/
theorem source_core_eq {n : ℕ} (s : SecondaryData c n) : Q c = (K c).pCoreIn 2 := by
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le)
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp ((K c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c) (pCore 2 (K c))))
  · exact (pCoreIn_mono_of_normalizes le_sup_left hn).trans_eq s.core_eq

/-- The actual radical has at most sixteen moving binary dimensions for any quintic in K₂. -/
theorem quintic_radical_index_bound (d : MSData c 2) (s : SecondaryData c 2)
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
    rw [source_core_eq s, ← relIndex_subgroupOf hB]
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
theorem quinticRadicalBound (d : MSData c 2) (s : SecondaryData c 2) :
    QuinticRadicalBound c :=
  quintic_radical_index_bound d s

/-- The completed marking and the actual radical bound exclude the unitary-five row.
The source assembly still constructs d and s from the original nonblock hypotheses. -/
theorem unitaryFive_false_of_source_data {V : Subgroup G}
    (d : MSData c 2) (s : SecondaryData c 2)
    (D : Chapter12.Section02.ChosenModule T L V)
    (h : Chapter12.Section02.Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hunitary : ClassicalGroup.IsPSU (s.component ⧸ pCore 2 s.component) 3 5) : False :=
  unitaryFive_false_of_unitary_and_bound s D h hunitary (quinticRadicalBound d s)

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
