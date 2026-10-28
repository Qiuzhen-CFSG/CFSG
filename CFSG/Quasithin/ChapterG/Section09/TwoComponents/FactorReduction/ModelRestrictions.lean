module

public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions.CentralQuotients
public import CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.Rank
public import Theory.SpecificGroups.SL2.DefiningRank
public import Theory.SpecificGroups.Suzuki.TwoRank
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.OuterModels.AlternatingSporadic.JankoOne

/-!
# Component-model restrictions in the two-factor branch of G.9.3

A.2.1(2) applies to the genuine semisimple sections of the supplied SQTK
cover. I.1.2 and the faithful irreducible binary constituent kill the center.
A.1.34 is then applied inside the actual join, with relative components and
an explicit SQTK cover. Its initial list retains PSL₂(pᵃ), 1 ≤ a ≤ 2.
The odd-prime rank bound from the pair, compared with the root subgroup,
forces a = 1. The remaining model rank bounds use actual isomorphisms with
binary SL₂, Suzuki, prime-field PSL₂ and the certified J₁ carrier.

The assembly still requires the A.2.1 section-rank witness, the precise
A.1.34 specialization and the independent binary SL₂ automorphism estimate.
These are explicit source obligations; the conditional assembly does not
assert that they have been proved. No original actor bound or tensor-dimension
alternative is assumed.

Source: Aschbacher--Smith, G.9.3, printed p.356; A.1.34(3), pp.29--30;
A.2.1(2), p.33; I.1.2, p.407.
-/

public noncomputable section

open scoped MatrixGroups
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
universe u v w

theorem QuotientModel.of_equiv {S : Type u} {D : Type w} [Group S] [Group D]
    (h : QuotientModel S) (e : D ≃* S) : QuotientModel D := by
  rcases h with ⟨n, hn, ⟨f⟩⟩ | ⟨s, hs, ⟨f⟩⟩ | hj | ⟨p, hp, a, hpa, ha, ha', ⟨f⟩⟩
  · exact .inl ⟨n, hn, ⟨e.trans f⟩⟩
  · exact .inr (.inl ⟨s, hs, ⟨e.trans f⟩⟩)
  · obtain ⟨f⟩ := hj
    exact .inr (.inr (.inl ⟨e.trans f⟩))
  · exact .inr (.inr (.inr ⟨p, hp, a, hpa, ha, ha', ⟨e.trans f⟩⟩))

private def quotientCenterEquiv {S : Type u} {D : Type w} [Group S] [Group D]
    (e : S ≃* D) : (S ⧸ center S) ≃* (D ⧸ center D) :=
  QuotientGroup.congr _ _ e (by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (centerCongr e ⟨x, hx⟩).property
    · intro x hx
      exact ⟨e.symm x, (centerCongr e).symm ⟨x, hx⟩ |>.property, e.apply_symm_apply x⟩)

/-- The full source theorem A supplies the precise rank witness used here. -/
theorem semisimpleSectionRank_of_theoremA {K : GroupClass.{u}}
    (hA : ∀ (X : Type u) [Group X] [Finite X], ChapterA.Section02.TheoremA K X) :
    SemisimpleSectionRankTheorem K := by
  intro X _ _ hX S _ _ hsec hsemi
  exact (hA X).stronglyQuasithin_section hX.stronglyQuasithin hX.isKGroup hsec hsemi

variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}
  {A L L₂ H : Subgroup G} {m : ℕ}

omit [Finite G] in
/-- The join is semisimple with components relative to H, not assumed
normal in the ambient group. -/
theorem pair_join_semisimple (hL : IsComponent G L) (hL₂ : IsComponent G L₂)
    (hH : H = L ⊔ L₂) : ChapterA.Section02.IsSemisimple H := by
  have hLH : L ≤ H := hH ▸ le_sup_left
  have h₂H : L₂ ≤ H := hH ▸ le_sup_right
  apply top_unique
  calc
    ⊤ = (L ⊔ L₂).subgroupOf H := by rw [← hH]; simp
    _ = L.subgroupOf H ⊔ L₂.subgroupOf H := subgroupOf_sup hLH h₂H
    _ ≤ componentLayer H := sup_le (le_sSup (hL.subgroupOf hLH))
      (le_sSup (hL₂.subgroupOf h₂H))

/-- A.2.1 is applied to the genuine section of the supplied SQTK cover. -/
theorem pair_join_stronglyQuasithin (hA : SemisimpleSectionRankTheorem K)
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) : IsStronglyQuasithin H := by
  obtain ⟨c⟩ := h.quotient
  exact hA c.Cover c.sqtk H
    ((ChapterA.Section02.IsSectionOf.subgroup H).ambient_surjective
      c.projection c.surjective) (pair_join_semisimple h.component hL₂ hH)

/-- The source's actual central-quotient list, with the exponent-two odd
linear branch retained. -/
theorem source_quotient_models (hA : SemisimpleSectionRankTheorem K)
    (hs : SourceA134Three K) (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (e : L ≃* L₂) : QuotientModel (L ⧸ center L) := by
  have hLH : L ≤ H := hH ▸ le_sup_left
  have h₂H : L₂ ≤ H := hH ▸ le_sup_right
  let e₁ := subgroupOfEquivOfLe hLH
  let e₂ := subgroupOfEquivOfLe h₂H
  have hn : L.subgroupOf H ≠ L₂.subgroupOf H := by
    intro he
    have hm := congrArg (Subgroup.map H.subtype) he
    exact hne (by simpa only [map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le h₂H] using hm)
  obtain ⟨c⟩ := h.quotient
  let cH : SQTKCover K H := {
    Cover := H.comap c.projection
    sqtk := c.sqtk.subgroup _
    projection := c.projection.subgroupComap H
    surjective := c.projection.subgroupComap_surjective_of_surjective H c.surjective }
  have hc := hs H (pair_join_stronglyQuasithin hA h hL₂ hH).quasithin
    (cH.sqtk.isKGroup.of_surjective cH.projection cH.surjective) ⟨cH⟩
    (L.subgroupOf H) (L₂.subgroupOf H) (h.component.subgroupOf hLH)
    (hL₂.subgroupOf h₂H) hn ⟨e₁.trans (e.trans e₂.symm)⟩
  exact hc.of_equiv (quotientCenterEquiv e₁.symm)

omit [FiniteDimensional (ZMod 2) V] in
/-- A faithful irreducible binary constituent kills a two-primary center. -/
theorem center_eq_bot_of_twoPrimary (T : TensorData ρ L L₂)
    (hz : IsPGroup 2 (center L)) : center L = ⊥ := by
  let σ : Representation (ZMod 2) L T.I := Representation.restrictScalars T.left
  let : Representation.IsIrreducible σ := T.left_irreducible
  have hk := Representation.normal_p_subgroup_le_ker σ (center L) hz
  apply eq_bot_iff.mpr
  intro z hz
  apply T.left_faithful
  ext x
  have he := congrArg (fun f : Module.End (ZMod 2) T.I => f x) (hk hz)
  simpa [σ, Representation.restrictScalars] using he

/-- The source section-rank theorem and proved I.1.2 transfer kill the
center, with no multiplier-table or model-classification input. -/
theorem component_center_eq_bot (hA : SemisimpleSectionRankTheorem K)
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hne : L ≠ L₂) (e : L ≃* L₂)
    (T : TensorData ρ L L₂) : center L = ⊥ := by
  let : IsQuasisimple L := h.component.2
  obtain ⟨c⟩ := h.quotient
  apply center_eq_bot_of_twoPrimary T
  apply center_isTwoGroup_of_quotient_odd_rank
  intro p hp ho
  exact quotient_odd_rank_le_one hA c h.component hL₂ hne (quotientCenterEquiv e) hp ho

/-- The direct product of the two isomorphic factors forces odd-prime
rank at most one in each factor. This is what excludes p². -/
theorem odd_rank_le_one (hL : IsComponent G L) (hL₂ : IsComponent G L₂)
    (hH : H = L ⊔ L₂) (hne : L ≠ L₂) (e : L ≃* L₂)
    (hz : center L = ⊥) (hqt : IsStronglyQuasithin H)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) : primeRank p L ≤ 1 := by
  let : Fact p.Prime := ⟨hp⟩
  have hc := commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hL₂ hne)
  have he := Subgroup.primeRank_sup_eq_add_of_disjoint_commuting L L₂
    (component_pair_disjoint_of_center_eq_bot hL hL₂ hne hz) hc p
  have ht := hqt p hp ho
  rw [hH, he, ← primeRank_equiv p e] at ht
  omega

/-- The root subgroup of PSL₂(pᵃ) forces a=1, rather than silently
strengthening A.1.34's a≤2 conclusion. -/
theorem odd_exponent_eq_one {p a : ℕ} [Fact p.Prime] (_hp : 3 < p) (ha : 1 ≤ a)
    (e : L ≃* PSL(2, GaloisField p a)) (hr : primeRank p L ≤ 1) : a = 1 := by
  let : NeZero a := ⟨by omega⟩
  have hb := Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_projective_injective
    (GaloisField.card p a (by omega)) e.symm.toMonoidHom e.symm.injective
  omega

private theorem janko_two_rank_bounds : 0 < primeRank 2 Janko1.Model ∧
    primeRank 2 Janko1.Model ≤ 3 := by
  constructor
  · let : IsElementaryAbelian 2 (zpowers Janko1.a) :=
      IsElementaryAbelian.zpowers_of_pow_eq_one Janko1.a_pow_two
    have hl : 1 ≤ primeRank 2 Janko1.Model :=
      IsElementaryAbelian.primeRank_ge_of_card (zpowers Janko1.a) (by
        simpa only [Nat.card_zpowers, pow_one] using Janko1.orderOf_a)
    omega
  · obtain ⟨E, _, hE⟩ := exists_elementaryAbelian_card_primeRank (G := Janko1.Model) (p := 2)
    have hd := E.card_subgroup_dvd_card
    rw [hE, Janko1.card_model] at hd
    by_contra h
    have hh : 2 ^ 4 ∣ 175560 := (pow_dvd_pow 2 (by omega : 4 ≤ primeRank 2 Janko1.Model)).trans hd
    norm_num at hh

private theorem janko_automorphism_rank :
    primeRank 2 (MulAut Janko1.Model) ≤ primeRank 2 Janko1.Model := by
  have hz : center Janko1.Model = ⊥ := by
    rcases (inferInstance : (center Janko1.Model).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exact (Group.IsPerfect.not_isMulCommutative Janko1.Model (center_eq_top_iff.mp ht)).elim
  let e := MulEquiv.ofBijective (MulAut.conj : Janko1.Model →* MulAut Janko1.Model)
    ⟨MulAut.conj_injective_of_center_eq_bot hz, Janko1.OuterCertificate.aut_inner⟩
  exact (primeRank_equiv 2 e).symm.le

/-- Rank restrictions for the genuine models, using the odd rank proved
from the pair and the independent binary automorphism estimate. -/
theorem model_ranks (hb : BinaryAutomorphismRankTheorem)
    (hmodels : QuotientModel L)
    (hodd : ∀ p : ℕ, p.Prime → Odd p → primeRank p L ≤ 1) :
    0 < primeRank 2 L ∧ primeRank 2 (MulAut L) ≤ primeRank 2 L ∧
      (4 ≤ primeRank 2 L → LargeRankModel L) := by
  classical
  rcases hmodels with ⟨n, hn, ⟨e⟩⟩ | ⟨s, hs, ⟨e⟩⟩ | hj | ⟨p, hp, a, hpa, ha, ha', ⟨e⟩⟩
  · let : NeZero n := ⟨by omega⟩
    have hcard := GaloisField.card 2 n (by omega)
    have hl := Matrix.SpecialLinearGroup.fieldExponent_le_primeRank_of_injective hcard
      e.symm.toMonoidHom e.symm.injective
    have hu : primeRank 2 (MulAut L) ≤ n := by
      rw [primeRank_equiv 2 (MulAut.congr e)]
      exact hb _ n hn hcard
    have hi : primeRank 2 L ≤ primeRank 2 (MulAut L) := by
      rw [primeRank_equiv 2 e, primeRank_equiv 2 (MulAut.congr e)]
      exact primeRank_le_of_injective 2 MulAut.conj
        (MulAut.conj_injective_of_center_eq_bot (Theory.PSL2.sl2_center_eq_bot _))
    have hr : primeRank 2 L = n := by omega
    refine ⟨by omega, by omega, fun _ => .inl ?_⟩
    exact ⟨GaloisField 2 n, inferInstance, inferInstance, inferInstance, hr ▸ hcard, ⟨e⟩⟩
  · have hr := (primeRank_equiv 2 e).trans
      (BenderSuzuki.MatrixGroups.suzuki_two_rank s hs)
    have hu : primeRank 2 (MulAut L) ≤ 2 * s + 1 := by
      rw [primeRank_equiv 2 (MulAut.congr e)]
      exact BenderSuzuki.MatrixGroups.suzuki_automorphism_two_rank s hs
    exact ⟨by omega, by omega, fun _ => .inr ⟨s, hs, ⟨e⟩⟩⟩
  · obtain ⟨e⟩ := hj
    have hr := primeRank_equiv 2 e
    have hu : primeRank 2 (MulAut L) ≤ primeRank 2 L := by
      rw [primeRank_equiv 2 (MulAut.congr e), hr]
      exact janko_automorphism_rank
    exact ⟨by have := janko_two_rank_bounds.1; omega, hu,
      fun hlarge => by have := janko_two_rank_bounds.2; omega⟩
  · have hao : a = 1 := odd_exponent_eq_one hpa ha e
      (hodd p hp.out (hp.out.odd_of_ne_two (by omega)))
    subst a
    let : Fintype (GaloisField p 1) := Fintype.ofFinite _
    let eF : GaloisField p 1 ≃+* ZMod p := FiniteField.ringEquivOfCardEq (by
      rw [← Nat.card_eq_fintype_card, GaloisField.card p 1 (by decide)]
      simp)
    let ep := e.trans (GorensteinWalter.psl2RingEquiv eF)
    have hr : primeRank 2 L = 2 :=
      (primeRank_equiv 2 ep).trans (Theory.PSL2.primeField_two_rank hpa)
    have hu : primeRank 2 (MulAut L) ≤ 2 := by
      rw [primeRank_equiv 2 (MulAut.congr ep)]
      exact Theory.PSL2.primeField_automorphism_two_rank hpa
    exact ⟨by omega, by omega, fun hlarge => by omega⟩

/-- Conditional assembly. The A.2.1 section-rank input remains a source
obligation, in addition to A.1.34 and the binary automorphism estimate.
No center, model, actor-rank or tensor-dimension conclusion is assumed. -/
theorem component_model_restrictions
    (hA : SemisimpleSectionRankTheorem K) (hs : SourceA134Three K)
    (hb : BinaryAutomorphismRankTheorem)
    (h : ComponentHypothesis K ρ A L H m)
    (hL₂ : IsComponent G L₂) (hH : H = L ⊔ L₂) (hne : L ≠ L₂)
    (hq : Quasiequivalent (ρ.comp L.subtype) (ρ.comp L₂.subtype) ∨
      Quasiequivalent (ρ.comp L.subtype) (Representation.dual (ρ.comp L₂.subtype)))
    (T : TensorData ρ L L₂) :
    center L = ⊥ ∧ 0 < primeRank 2 L ∧
      primeRank 2 (MulAut L) ≤ primeRank 2 L ∧
      (4 ≤ primeRank 2 L → LargeRankModel L) := by
  obtain ⟨e⟩ : Nonempty (L ≃* L₂) := by
    rcases hq with ⟨e, _, _⟩ | ⟨e, _, _⟩ <;> exact ⟨e⟩
  let : IsQuasisimple L := h.component.2
  have hm := source_quotient_models hA hs h hL₂ hH hne e
  have hz := component_center_eq_bot hA h hL₂ hne e T
  let ez : L ≃* (L ⧸ center L) :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hz.symm)
  exact ⟨hz, model_ranks hb (hm.of_equiv ez) (fun p hp ho =>
    odd_rank_le_one h.component hL₂ hH hne e hz
      (pair_join_stronglyQuasithin hA h hL₂ hH) hp ho)⟩

end CFSG.Quasithin.ChapterG.Section09.TwoComponents.FactorReduction.ModelRestrictions
