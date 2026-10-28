module
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.ExchangedSelection.Catalogue.Ordinary.ResidualControl
public import Theory.GroupTheory.ElementarySylowResidualAction
public import Theory.GroupTheory.SubgroupTransport
public import Theory.SpecificGroups.PSL3Three.NormalElementary
public import Theory.SpecificGroups.PSL3Three.OuterTwo
public import Theory.SpecificGroups.PSL2.NormalElementary
public import Theory.SpecificGroups.PSL2.PrimeCartanNormalizer
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
public import Theory.SpecificGroups.SL2.SmallOddComparisons

/-!
# The odd-characteristic ordinary component row

The actual actor O²(M ∩ G₁) acts fully on W = [V,O²(M ∩ G₁)]. Both
subgroups normalize L, and the original S_L normalizes W. On PSL₃(3) and
PSL₂(q) for Fermat--Mersenne primes q > 7, the outer automorphism group
is a two-group and every normal elementary subgroup of a Sylow two-subgroup
has order at most two. Consequently the image of W is inner, then cyclic,
and its full commutator action is trivial. This contradicts the original
moving-noncentrality clause of 15.1.19(7), before exchanged selection.

The remaining odd parameters are five and seven: the three-element-field
model is not perfect. Actual exceptional isomorphisms identify these with
PSL₂(4) and PSL₃(2), respectively. Their Borel and small-model exclusions
remain part of the initial catalogue assembly; no exhaustive Ordinary20
or Ordinary22 conclusion is asserted here.

Source: Aschbacher--Smith 15.1.20(3), final paragraph, printed p.1097.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open Section03 Section03.InitialSource ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G} {p : ℕ}
variable {d : CaseIComponentData T M Mc V} {h : PreparedChosenModule T M V}

/-- The original residual and its moving subgroup contradict cyclic normal
elementary Sylow geometry on the actual centerless component. -/
theorem PreExclusionSource.false_of_normal_elementary_bound
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hz : center d.L = ⊥) (ho : IsPGroup 2 (MulAut.Outer d.L))
    (hsmall : ∀ (P : Sylow 2 d.L) (E : Subgroup P),
      E.Normal → IsElementaryAbelian 2 E → Nat.card E ≤ 2) : False := by
  let := h.elementary
  let C := M ⊓ d.G1
  let R := (pResidual 2 C).map C.subtype
  let W := ⁅V,R⁆
  let N := normalizer (d.L : Set G)
  let f := d.L.normalizerMonoidHom
  have hRC : R ≤ C := map_subtype_le _
  have hRN : R ≤ N := le_sup_left.trans s.residual_normalizes
  have hWN : W ≤ N := le_sup_right.trans s.residual_normalizes
  have hRV : R ≤ normalizer (V : Set G) := (hRC.trans inf_le_left).trans h.normalized
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp hRV
  have hmove : ⁅W,R⁆ = W := commutator_isPPerfect_idempotent R V
    (isPPerfect_embedded_pResidual 2 C) (IsElementaryAbelian.isPGroup 2 V) hRV
  have hVC : V ≤ C := le_inf h.le_selected
    (V.le_centralizer.trans (centralizer_le (d.Z1_le_fixed.trans inf_le_left)))
  have hWC : W ≤ C := hWV.trans hVC
  have hCW : C ≤ normalizer (W : Set G) := by
    have hnV : (V.subgroupOf C).Normal :=
      normal_subgroupOf_of_le_normalizer (inf_le_left.trans h.normalized)
    have hR : R.subgroupOf C = pResidual 2 C := by
      apply map_injective C.subtype_injective
      rw [map_subgroupOf_eq_of_le hRC]
    have he : W.subgroupOf C = ⁅V.subgroupOf C,pResidual 2 C⁆ := by
      change ⁅V,R⁆.subgroupOf C = _
      rw [SubgroupTransport.subgroupOf_commutator V R hVC hRC,hR]
    have hn : (W.subgroupOf C).Normal := he ▸ inferInstance
    exact (normal_subgroupOf_iff_le_normalizer hWC).mp hn
  let A := (W.subgroupOf N).map f
  let B := (R.subgroupOf N).map f
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_le hWV
  let : IsElementaryAbelian 2 (W.subgroupOf N) := IsElementaryAbelian.subgroupOf hWN
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map f
  have hB : IsPPerfect 2 B := by
    have hp := (isPPerfect_embedded_pResidual 2 C).of_surjective
      (subgroupOfEquivOfLe hRN).symm.toMonoidHom (subgroupOfEquivOfLe hRN).symm.surjective
    exact hp.of_surjective (f.subgroupMap _) (f.subgroupMap_surjective _)
  obtain ⟨P,hP⟩ := s.component_sylow
  have hPC : ((P : Subgroup d.L).map d.L.subtype) ≤ C := by
    rw [hP]
    exact le_inf ((inf_le_left.trans d.S_le_T).trans hTM)
      (inf_le_right.trans d.L_component.1)
  have hPA : (P : Subgroup d.L).map (MulAut.conj : d.L →* MulAut d.L) ≤
      normalizer (A : Set (MulAut d.L)) := by
    rintro _ ⟨x,hx,rfl⟩
    let xn : N := ⟨x,d.L.le_normalizer x.property⟩
    have hxW : xn ∈ normalizer (W.subgroupOf N : Set N) := by
      rw [←subgroupOf_normalizer_eq hWN]
      exact hCW (hPC (mem_map_of_mem d.L.subtype hx))
    have hfx : f xn = MulAut.conj x := by
      ext l
      rfl
    rw [←hfx]
    exact (W.subgroupOf N).le_normalizer_map f (mem_map_of_mem f hxW)
  have hAB : ⁅A,B⁆ = A := by
    dsimp only [A,B]
    rw [←map_commutator,←SubgroupTransport.subgroupOf_commutator W R hWN hRN,hmove]
  have hA := elementary_moved_eq_bot_of_normal_elementary_bound hz ho P (hsmall P) A B hB hPA hAB
  have hcentral : W ≤ centralizer (d.L : Set G) := by
    intro w hw l hl
    have hh : f ⟨w,hWN hw⟩ = 1 := mem_bot.mp (hA ▸ mem_map_of_mem f hw)
    have he := congrArg Subtype.val (DFunLike.congr_fun hh (⟨l,hl⟩ : d.L))
    change w*l*w⁻¹=l at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  exact s.moving_noncentral (by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcentral)

/-- PSL₃(3) is impossible for the original pre-exclusion component. -/
theorem PreExclusionSource.false_of_pslThreeThree_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (e : d.L ≃* Matrix.PSL3Three.PSL) : False := by
  have hz : center d.L = ⊥ := by
    apply (center d.L).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr (e.trans Matrix.PSL3Three.equiv.symm)).toEquiv,
      Matrix.PSL3Three.center_eq_bot,card_bot]
  apply s.false_of_normal_elementary_bound (h := h) hTM hz
    (Matrix.PSL3Three.outer_isTwoGroup.of_equiv (MulAut.outerCongr e).symm)
  intro P E hn he
  let := hn
  let := he
  exact Matrix.PSL3Three.normal_elementary_sylow_card_le_two
    (e.trans Matrix.PSL3Three.equiv.symm) P E

/-- The large Fermat--Mersenne models cannot support the original moving action. -/
theorem PreExclusionSource.false_of_largePrimePSL_equiv
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    {q k : ℕ} [Fact q.Prime] (hq : 7 < q)
    (hqk : q - 1 = 2 ^ k ∨ q + 1 = 2 ^ k)
    (e : d.L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod q)) : False := by
  obtain ⟨hz,ho⟩ := Theory.PSL2.primeField_center_outer_of_equiv
    (Fact.out : q.Prime) ((Fact.out : q.Prime).odd_of_ne_two (by omega))
    (Nat.card_zmod q) e
  apply s.false_of_normal_elementary_bound (h := h) hTM hz ho
  intro P E hn he
  let := hn
  let := he
  exact Theory.PSL2.normal_elementary_sylow_card_le_two hq hqk e P E

/-- The actual PSL₃(3) model predicate is excluded at the original fixed component. -/
theorem PreExclusionSource.not_pslThreeThree
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M) : ¬ ClassicalGroup.IsPSL d.L 3 3 := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  exact s.false_of_pslThreeThree_equiv (h := h) hTM (e.trans (Atlas.fieldEquivPSL 3 f))

/-- The source's Fermat--Mersenne parameter, with its literal field model,
discharges the large-prime exclusion without any action or geometry callback. -/
theorem PreExclusionSource.not_largeFermatMersennePSL
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    {q : ℕ} (hq : IsFermatOrMersennePrime q) (hlarge : 7 < q) :
    ¬ ClassicalGroup.IsPSL d.L 2 q := by
  rintro ⟨F,_,_,hF,⟨e⟩⟩
  let : Fact q.Prime := ⟨hq.1⟩
  let : Fintype F := Fintype.ofFinite F
  let f : F ≃+* ZMod q := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
  have hpower : ∃ k : ℕ, q - 1 = 2 ^ k ∨ q + 1 = 2 ^ k := by
    rcases hq.2 with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact ⟨2 ^ a,Or.inl (by rw [ha,Nat.add_sub_cancel])⟩
    · exact ⟨a,Or.inr ha⟩
  obtain ⟨k,hk⟩ := hpower
  exact s.false_of_largePrimePSL_equiv (h := h) hTM hlarge hk
    (e.trans (Atlas.fieldEquivPSL 2 f))

/-- The odd branch of the actual 1.1.5 marking reduces to parameters five
and seven. Perfection rules out the nonsimple three-element-field model. -/
theorem PreExclusionSource.ordinary_odd_small_parameter
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : ClassicalGroup.IsPSL d.L 3 3 ∨
      ∃ q : ℕ, IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL d.L 2 q) :
    ∃ q : ℕ, (q = 5 ∨ q = 7) ∧ ClassicalGroup.IsPSL d.L 2 q := by
  rcases hm with hm | ⟨q,hq,hm⟩
  · exact (s.not_pslThreeThree (h := h) hTM hm).elim
  · have hq7 : q ≤ 7 := by
      by_contra! hh
      exact s.not_largeFermatMersennePSL (h := h) hTM hq hh hm
    have hq2 : q ≠ 2 := by
      rintro rfl
      rcases hq.2 with ⟨a,ha⟩ | ⟨a,ha⟩
      · have hl : 2 ≤ 2 ^ (2 ^ a) := Nat.le_pow (by norm_num)
        omega
      · have hd : 2 ∣ 2 ^ a := dvd_pow_self _ (by rintro rfl; norm_num at ha)
        omega
    have hq3 : q ≠ 3 := by
      intro he
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      let : IsQuasisimple d.L := IsQuasisimple.of_mulEquiv (hG := hL.2)
        (subgroupOfEquivOfLe d.L_component.1)
      exact Matrix.ProjectiveSpecialLinearGroup.not_perfect_of_card_three (hF.trans he)
        (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective)
    have hpq := hq.1
    have hh : q = 5 ∨ q = 7 := by
      interval_cases q <;> norm_num at hpq <;> omega
    exact ⟨q,hh,hm⟩

/-- The entire odd-characteristic marking feeds the two earlier small
binary models under actual equivalences, at the same original component. -/
theorem PreExclusionSource.ordinary_odd_binary_models
    (s : d.PreExclusionSource h.normalized p)
    (hTM : (T : Subgroup G) ≤ M)
    (hL : IsComponent d.G1 (d.L.subgroupOf d.G1))
    (hm : ClassicalGroup.IsPSL d.L 3 3 ∨
      ∃ q : ℕ, IsFermatOrMersennePrime q ∧ ClassicalGroup.IsPSL d.L 2 q) :
    Nonempty (d.L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) ∨
      Nonempty (d.L ≃* Matrix.PSL3Two.PSL) := by
  obtain ⟨q,hq,hm⟩ := s.ordinary_odd_small_parameter (h := h) hTM hL hm
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  rcases hq with rfl | rfl
  · exact Or.inl ⟨e.trans (Matrix.ProjectiveSpecialLinearGroup.cardFiveEquivFour hF)⟩
  · exact Or.inr ⟨e.trans (Atlas.Comparisons.Exceptional.psl2Card7EquivPsl3Two hF)⟩

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
