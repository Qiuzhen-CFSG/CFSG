module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.ExchangedHall.Orbit
public import Theory.GroupTheory.GeneralizedFitting.ComponentOverlapRank
public import Theory.Quasithin.Rank
public import Theory.GroupTheory.PrimeRankCoprimeIndex
public import Theory.SpecificGroups.SL2.FieldAutomorphismCore
public import Theory.SpecificGroups.SL2.FieldCardinality
public import Theory.SpecificGroups.Suzuki.LinearSeparation
public import Theory.GroupTheory.ComponentLocalDirectPower
public import Theory.GroupTheory.Hall.TwoClosedNormal
public import Theory.ElementaryAbelian.PrimeRankCard
public import Theory.ElementaryAbelian.Injective

/-!
# The literal Hall plane in an exchanged four-field source row

Modulo the actual source kernel O₂(X), the conjugate Borel overlaps form
an ordinary direct power, with a two-group upper quotient. Each coordinate
Borel has order twelve. Odd subgroups therefore embed in a product of
cyclic groups of order dividing three, so the prescribed odd Hall group is
elementary abelian of exponent three. The quotient map is injective on it.

A genuinely moved component gives two independent cubic directions in
the overlap. The quasithin bound of two and the Hall index then identify
this original Hall subgroup as E₉. An intrinsic A₅ component quotient
recovers the field-four marking: the SL₂ order comparison recovers the
field size, and the absence of cubic elements excludes the Suzuki row.
Neither a Hall plane nor an isomorphism
of the whole residual is assumed. The Cartan local-to-global owner retains
the source-row selection and the other branches of normalization.

Source: Aschbacher–Smith E.2.2(1a) and 5.2.2, printed pp.215–216,648–649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExchangedCartan
variable {X : Type*} [Group X] [Finite X]

private theorem elementary_of_odd_embedding_power_twelve
    {Y U : Type*} [Group Y] [Finite Y] [Group U] [Finite U]
    (ho : Odd (Nat.card Y)) (hu : Nat.card U = 12) {n : ℕ}
    (f : Y →* (Fin n → U)) (hf : Function.Injective f) : IsElementaryAbelian 3 Y := by
  let fi (i : Fin n) : Y →* U := (Pi.evalMonoidHom (fun _ : Fin n => U) i).comp f
  have hdiv (i : Fin n) : Nat.card (fi i).range ∣ 3 := by
    have hd : Nat.card (fi i).range ∣ 12 := hu ▸ (fi i).range.card_subgroup_dvd_card
    have hc : Nat.Coprime (Nat.card (fi i).range) 4 :=
      ((Nat.coprime_two_right.mpr ho).of_dvd_left (card_range_dvd (fi i))).pow_right 2
    exact hc.dvd_of_dvd_mul_left (show Nat.card (fi i).range ∣ 4 * 3 from hd)
  have he (i : Fin n) : IsElementaryAbelian 3 (fi i).range := by
    let : IsCyclic (fi i).range := isCyclic_of_card_dvd_prime (hdiv i)
    exact { toIsMulCommutative := inferInstance
            exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x =>
              by
                obtain ⟨k,hk⟩ := hdiv i
                rw [hk,pow_mul,pow_card_eq_one',one_pow]) }
  let g : Y →* (∀ i : Fin n, (fi i).range) := MonoidHom.pi (fun i => (fi i).rangeRestrict)
  have hg : Function.Injective g := by
    intro x y hxy
    apply hf
    funext i
    exact congrArg (fun z => ((z i : (fi i).range) : U)) hxy
  let (i : Fin n) : IsElementaryAbelian 3 (fi i).range := he i
  let : IsElementaryAbelian 3 (∀ i : Fin n, (fi i).range) := {
    toIsMulCommutative := inferInstance
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun x => by
      funext i
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 3 (fi i).range) (x i)) }
  exact IsElementaryAbelian.of_injective g hg

omit [Finite X] in
private theorem odd_embedding_quotient (N Y : Subgroup X) [N.Normal]
    (hN : IsPGroup 2 N) (ho : Odd (Nat.card Y)) :
    Function.Injective ((QuotientGroup.mk' N).comp Y.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  let f := (QuotientGroup.mk' N).comp Y.subtype
  have hp : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact hN.comap_of_injective Y.subtype Y.subtype_injective
  have hn : ¬ 2 ∣ Nat.card f.ker :=
    fun hh => ho.not_two_dvd_nat (hh.trans f.ker.card_subgroup_dvd_card)
  exact f.ker.eq_bot_of_card_eq (hp.card_eq_or_dvd.resolve_right hn)

private theorem odd_elementary_of_local_power
    {C U T : Subgroup X} (hC : IsComponent X C) (hz : center C = ⊥)
    (hUC : U ≤ C) (hi : T ⊓ normalizer (C : Set X) ≤ normalizer (U : Set X))
    (hT : IsPGroup 2 T) (hu : Nat.card U = 12)
    (Y : Subgroup (U ⊔ T : Subgroup X)) (ho : Odd (Nat.card Y)) :
    IsElementaryAbelian 3 Y := by
  obtain ⟨N,hN,hq,n,⟨e⟩⟩ := hC.local_adjoin_normal_power hz hUC hi hT
  let := hN
  have hYN := OddHall.odd_subgroup_le N Y hq ho
  exact elementary_of_odd_embedding_power_twelve ho hu
    (e.toMonoidHom.comp (inclusion hYN)) (e.injective.comp (inclusion_injective hYN))

private theorem borel_card_four {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) : Nat.card (BenderSuzuki.Converse.PBorel F) = 12 := by
  open BenderSuzuki.Converse in
  have hn : PTorus F ≤ normalizer (PUnip F : Set _) := PTorus_le_PBorel.trans
    ((normal_subgroupOf_iff_le_normalizer PUnip_le_PBorel).mp PUnip_normal_in_PBorel)
  rw [← BenderSuzuki.Converse.PUnip_sup_PTorus,
    card_sup_eq_mul_of_normalizes_of_disjoint _ _ hn BenderSuzuki.Converse.PUnip_disjoint_PTorus,
    BenderSuzuki.Converse.PUnip_card,BenderSuzuki.Converse.PTorus_card,Nat.card_units,hF]

/-- The actual odd Hall subgroup is elementary in the exchanged four-field row. -/
theorem hall_elementary_of_linear_four
    {M C T : Subgroup X} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C)) (hc : ExchangedClauses M C T)
    (hTM : T ≤ M) (hT : IsPGroup 2 T)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (hm : ModelBorelPair M C (BenderSuzuki.Converse.PBorel F))
    (Y : Subgroup M) (ho : Odd (Nat.card Y)) : IsElementaryAbelian 3 Y := by
  obtain ⟨e,he⟩ := hm
  let q := QuotientGroup.mk' (sourceKernel M)
  let U := sourceImage M (M ⊓ C)
  let A := sourceImage M T
  have hz : center (sourceImage M C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center (BenderSuzuki.Converse.PSL2 F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot] at hh
    exact e.map_eq_one_iff.mp (mem_bot.mp hh)
  have hu : Nat.card U = 12 := by
    have hh : Nat.card ((componentOverlap M C).map e.toMonoidHom) =
        Nat.card (componentOverlap M C) := card_map_of_injective e.injective
    rw [he] at hh
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show U ≤ sourceImage M C from map_mono inf_le_right)).toEquiv).symm.trans
      (hh.symm.trans (borel_card_four hF))
  have hjoin : U ⊔ A = M.map q := by
    change (M ⊓ C).map q ⊔ T.map q = M.map q
    rw [← Subgroup.map_sup,ExchangedHall.exchanged_join hc hTM]
  let f : M →* (U ⊔ A : Subgroup (X ⧸ sourceKernel M)) :=
    (MulEquiv.subgroupCongr hjoin.symm).toMonoidHom.comp (q.subgroupMap M)
  let Y' := Y.map f
  have ho' : Odd (Nat.card Y') := ho.of_dvd_nat (card_map_dvd Y f)
  let : IsElementaryAbelian 3 Y' := odd_elementary_of_local_power
    (ExchangedHall.source_component hc hC hqs) hz (map_mono inf_le_right)
    (ExchangedHall.source_overlap_invariant hTM) (hT.map q) hu Y' ho'
  have hq : Function.Injective (q.comp (M.subtype.comp Y.subtype)) := by
    let Z := Y.map M.subtype
    have hZ : Odd (Nat.card Z) := by rwa [card_map_of_injective M.subtype_injective]
    have hn : IsPGroup 2 (sourceKernel M) := hc.kernel_eq.symm ▸ pCore_isPGroup
    have hi := odd_embedding_quotient (sourceKernel M) Z hn hZ
    intro x y hxy
    have hh : (⟨M.subtype (Y.subtype x),mem_map_of_mem M.subtype x.property⟩ : Z) =
        ⟨M.subtype (Y.subtype y),mem_map_of_mem M.subtype y.property⟩ := hi hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Z => (z : X)) hh
  have hfi : Function.Injective (f.comp Y.subtype) := by
    intro x y hxy
    apply hq
    exact congrArg (fun z : (U ⊔ A : Subgroup _) => (z : X ⧸ sourceKernel M)) hxy
  exact IsElementaryAbelian.of_injective (f.subgroupMap Y)
    (fun x y hxy => hfi (congrArg Subtype.val hxy))


private theorem rank_pos_of_three_dvd (hd : 3 ∣ Nat.card X) : 1 ≤ primeRank 3 X := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 hd
  let E := zpowers x
  let : CommGroup E := IsMulCommutative.instCommGroup
  have hc : Nat.card E = 3 := (Nat.card_zpowers x).trans hx
  exact primeRank_ge_of_elementary_embedding
    (fun y : E => by simpa only [hc] using pow_card_eq_one' (x := y))
    (by simpa using hc) E.subtype E.subtype_injective

private theorem rank_ge_two_of_moved_component
    {C M : Subgroup X} (hC : IsComponent X C) (hz : center C = ⊥)
    {m : X} (hm : m ∈ M) (hne : C.map (MulAut.conj m).toMonoidHom ≠ C)
    (ho : 1 ≤ primeRank 3 (M ⊓ C : Subgroup X)) : 2 ≤ primeRank 3 M := by
  by_contra hr
  have hn := hC.normalizes_of_overlap_primeRank (M := M) hz 3 (by omega)
  exact hne (mem_normalizer_iff_map_conj_eq.mp (hn hm))

/-- Quasithin rank and the genuinely exchanged components identify the prescribed Hall plane. -/
theorem hall_plane_of_linear_four
    {M C T : Subgroup X} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C)) (hc : ExchangedClauses M C T)
    (hTM : T ≤ M) (hT : IsPGroup 2 T) (hr : primeRank 3 M ≤ 2)
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = 4) (hm : ModelBorelPair M C (BenderSuzuki.Converse.PBorel F))
    (Y : Subgroup M) (hY : IsHallSubgroup OddHall.oddPrimes Y) :
    IsElementaryAbelian 3 Y ∧ Nat.card Y = 9 := by
  let := hall_elementary_of_linear_four hC hqs hc hTM hT hF hm Y
    (OddHall.odd_hall_odd hY)
  refine ⟨inferInstance,?_⟩
  obtain ⟨e,he⟩ := hm
  let q := QuotientGroup.mk' (sourceKernel M)
  have hz : center (sourceImage M C) = ⊥ := by
    apply eq_bot_iff.mpr
    intro x hx
    have hh := ((centerCongr e) ⟨x,hx⟩).property
    change e x ∈ center (BenderSuzuki.Converse.PSL2 F) at hh
    rw [Atlas.RankOneFieldAutomorphisms.psl_center_eq_bot] at hh
    exact e.map_eq_one_iff.mp (mem_bot.mp hh)
  obtain ⟨t,ht,hne,_⟩ := hc.exchanged_product
  have hne' : (sourceImage M C).map (MulAut.conj (q t⁻¹)).toMonoidHom ≠ sourceImage M C := by
    intro hh
    have hn : q t⁻¹ ∈ normalizer (sourceImage M C : Set _) :=
      mem_normalizer_iff_map_conj_eq.mpr hh
    have htN : t⁻¹ ∈ normalizer (C : Set X) := by
      let : Group.IsNilpotent (sourceKernel M) := hc.kernel_eq.symm ▸ pCore_isNilpotent
      rw [←normalizer_cComponent_quotient hC (sourceKernel M)]
      exact hn
    exact hne (mem_normalizer_iff_map_conj_eq.mp htN).symm
  have hu : Nat.card (sourceImage M (M ⊓ C)) = 12 := by
    have hh : Nat.card ((componentOverlap M C).map e.toMonoidHom) =
        Nat.card (componentOverlap M C) := card_map_of_injective e.injective
    rw [he] at hh
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show sourceImage M (M ⊓ C) ≤ sourceImage M C from map_mono inf_le_right)).toEquiv).symm.trans
      (hh.symm.trans (borel_card_four hF))
  have hl : 2 ≤ primeRank 3 (sourceImage M M) := by
    apply rank_ge_two_of_moved_component (ExchangedHall.source_component hc hC hqs) hz
      (mem_map_of_mem q (hTM (T.inv_mem ht))) hne'
    change 1 ≤ primeRank 3 (sourceImage M M ⊓ sourceImage M C : Subgroup _)
    rw [←ExchangedHall.source_overlap_eq]
    exact rank_pos_of_three_dvd (by rw [hu];decide)
  have hker : IsPGroup 2 (q.subgroupMap M).ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',hc.kernel_eq]
    exact pCore_isPGroup.comap_subtype
  have hqm : primeRank 3 (sourceImage M M) ≤ primeRank 3 M := by
    apply primeRank_le_of_surjective_of_coprime 3 (q.subgroupMap M)
      (q.subgroupMap_surjective M)
    obtain ⟨k,hk⟩ := hker.exists_card_eq
    rw [hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hi : ¬ 3 ∣ Y.index := fun hh =>
    hY.p_in_pi_of_p_dvd_index ⟨3,by decide⟩ hh (by change (3 : ℕ) ≠ 2;decide)
  have hy : primeRank 3 Y = primeRank 3 M := Y.primeRank_eq_of_not_dvd_index hi
  have hrY : primeRank 3 Y = 2 := by omega
  rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 3),hrY]
  norm_num

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExchangedCartan

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExchangedCartan
variable {X : Type*} [Group X] [Finite X]

/-- Recover the four-field Borel marking from the original component's intrinsic A₅ quotient. -/
theorem linear_four_marking_of_A5
    {M C T : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hc : ExchangedClauses M C T) (hm : ExchangedModel M C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 4 ∧ ModelBorelPair M C (BenderSuzuki.Converse.PBorel F) := by
  let q := QuotientGroup.mk' (sourceKernel M)
  let a := q.subgroupMap C
  have hk : a.ker = pCore 2 C := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk',hc.kernel_eq]
    exact (pCore_subnormal_eq_comap 2 hC.subnormal).symm
  let eQ : (C ⧸ pCore 2 C) ≃* sourceImage M C :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective a (q.subgroupMap_surjective C))
  obtain ⟨E,_,_,hE,⟨eA⟩⟩ := hA5
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by simpa only [Nat.card_eq_fintype_card, show (2 : ℕ) ^ 2 = 4 by norm_num] using hE)
  let e0 := eQ.symm.trans eA
  rcases hm with hlin | hsuz
  · obtain ⟨F,_,_,_,_,_,e,he⟩ := hlin
    have hcard : Nat.card F = 4 := by
      have hFE := Matrix.SL2.field_card_eq_of_equiv
        ((Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).trans
          (e.symm.trans (e0.trans (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := E)).symm)))
      exact hFE.trans hE
    exact ⟨F,inferInstance,inferInstance,inferInstance,hcard,e,he⟩
  · obtain ⟨m,hm,_,e,_⟩ := hsuz
    exact (BenderSuzuki.MatrixGroups.not_nonempty_psl2_char_two_equiv_suzuki E (by omega)
      ⟨e0.symm.trans e⟩).elim

/-- The actual component quotient supplies the field-four input to the literal Hall-plane theorem. -/
theorem hall_plane_of_A5
    {M C T : Subgroup X} {f : ℕ} (hC : C.IsCComponent)
    (hqs : IsQuasisimple (C ⧸ pCore 2 C)) (hc : ExchangedClauses M C T)
    (hm : ExchangedModel M C f)
    (hA5 : ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 4)
    (hTM : T ≤ M) (hT : IsPGroup 2 T) (hr : primeRank 3 M ≤ 2)
    (Y : Subgroup M) (hY : IsHallSubgroup OddHall.oddPrimes Y) :
    IsElementaryAbelian 3 Y ∧ Nat.card Y = 9 := by
  obtain ⟨F,_,_,_,hF,hb⟩ := linear_four_marking_of_A5 hC hc hm hA5
  exact hall_plane_of_linear_four hC hqs hc hTM hT hr hF hb Y hY

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.ExchangedCartan
