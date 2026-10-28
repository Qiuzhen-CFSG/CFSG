module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesActionSelection
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSevenActor
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.ExceptionalRestrictions.A7
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingSevenFixed
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.SL2.PerfectCoreQuotientDegree

/-!
# The ordinary A₇ star row in the original rank-one configuration

The full source module W is nontrivial, is moved by the original perfect L,
and lies properly in U(K). Its binary dimension is at least 2n by the actual
L/O₂(L) marking. This excludes the exceptional four-dimensional A₇ section.
The B.5 table then supplies the ordinary natural action with its intertwiner.
Its fixed layer vanishes, so |U(K)| = 64 and W < U(K) forces n = 2.

Thus both the module recognition and original parameter are proved for the
literal A₇ star component. The chosen V is never identified with the full W.
The remaining symplectic and large G₂ rows stay with this task's assembly owner.
Source: Aschbacher–Smith C.4.1(1), C.4.6, pp.151–153; original 4.3.7, pp.615–616.
-/

public section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The nontrivial perfect action on the full W has binary dimension at least 2n. -/
theorem SourceConfiguration.fullModule_card_lower_bound
    (c : SourceConfiguration T L) {n : ℕ} (hn : n ≠ 0)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) :
    2 ^ (2*n) ≤ Nat.card (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)) := by
  let W := Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)
  have hs : conjugateSpanBy L (c.H ⊓ normalizer (L : Set G)) = L :=
    le_antisymm (conjugateSpanBy_le le_rfl inf_le_right) (le_conjugateSpanBy _ _)
  let : Group.IsPerfect L := hs ▸ c.c28.span_perfect
  let : IsElementaryAbelian 2 W := c.c28.module_elementary
  have hw : W = ⁅W,L⁆ := by simpa only [hs] using c.c28.module_commutator
  have hnW : L ≤ normalizer (W : Set G) := le_normalizer_iff_commutator_le_left.mpr hw.ge
  let φ := W.normalizerMonoidHom.comp (inclusion hnW)
  let ρ := elementaryRepresentation (p := 2) φ
  have hnt : ∃ l, ρ l ≠ 1 := by
    by_contra! hh
    have hc : W ≤ centralizer (L : Set G) := by
      intro w hw l hl
      have he := congrArg (fun f : Module.End (ZMod 2) (Additive W) =>
        (f (Additive.ofMul ⟨w,hw⟩)).toMul.val) (hh ⟨l,hl⟩)
      change l * w * l⁻¹ = w at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact c.c28.module_nontrivial (hw.trans (commutator_eq_bot_iff_le_centralizer.mpr hc))
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  have hd := Representation.SL2.perfect_core_quotient_finrank_bound
    (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm) ρ hnt hn hF
  have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    simpa only [Nat.card_congr (Additive.toMul : Additive W ≃ W),Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  rw [hc]
  exact Nat.pow_le_pow_right (by decide) hd

/-- The proper full module excludes the exceptional four-dimensional A₇ block. -/
theorem SourceConfiguration.not_exceptionalA7_block
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (he : ChapterC.IsExceptionalA7Block c.K) : False := by
  have hb := c.fullModule_card_lower_bound (by omega : n ≠ 0) hpsl
  have hu : Nat.card c.blockLayer = 16 := by
    rw [SourceConfiguration.blockLayer,card_map_of_injective c.H.subtype_injective,
      card_map_of_injective c.K.subtype_injective,he.u_card]
  have hl := Set.Finite.card_lt_card (Set.toFinite (c.blockLayer : Set G)) (c.fullModule_lt_blockLayer hf)
  change Nat.card (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)) < Nat.card c.blockLayer at hl
  rw [hu] at hl
  have hp : 2^4 ≤ 2^(2*n) := Nat.pow_le_pow_right (by decide) (by omega)
  omega
open ChapterC ChapterB.QuasisimpleSource Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
/-- The ordinary A₇ module forces the original rank-one field degree to be two. -/
theorem SourceConfiguration.original_degree_of_alternatingSeven
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K)
    (ha : IsAlternatingBlock c.K 7) : n = 2 := by
  have hb := c.fullModule_card_lower_bound (by omega : n ≠ 0) hpsl
  let e : BlockModule c.K ≃* blockU c.K :=
    (QuotientGroup.quotientMulEquivOfEq ha.seven_fixed_eq_bot).trans QuotientGroup.quotientBot
  have hu : Nat.card c.blockLayer = 2^6 := by
    rw [SourceConfiguration.blockLayer,card_map_of_injective c.H.subtype_injective,
      card_map_of_injective c.K.subtype_injective,← Nat.card_congr e.toEquiv]
    exact ha.module_card_odd (by decide)
  have hl := Set.Finite.card_lt_card (Set.toFinite (c.blockLayer : Set G)) (c.fullModule_lt_blockLayer hf)
  change Nat.card (Section02.Unitary.fullModule L ((L ⊔ (T : Subgroup G)).pCoreIn 2)) < Nat.card c.blockLayer at hl
  rw [hu] at hl
  have hd : 2*n < 6 := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp (hb.trans_lt hl)
  omega

/-- The full B.5 table on the actual A₇ star component selects the ordinary
six-dimensional action. The exceptional four-dimensional section contradicts
W < U(K) and the original rank-one degree bound. -/
theorem SourceConfiguration.alternatingSeven_block_of_star_group
    (c : SourceConfiguration T L) {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hf : generalizedFitting c.K = pCore 2 c.K) (hb : IsBlock c.K)
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype) ≃*
      alternatingGroup (Fin 7)) : n = 2 ∧ IsAlternatingBlock c.K 7 := by
  obtain ⟨hCJ,s,_,hs⟩ := c.block_star_irreducible_source hf hb
  rcases ChapterB.QuasisimpleSource.SourceCompletion.AlternatingSevenActor.natural_or_four
    s.action hs ((subgroupOfEquivOfLe hCJ).trans e) with ha | hd
  · obtain ⟨a⟩ := ha
    have ha : IsAlternatingBlock c.K 7 := ⟨by decide,hb.short,
      c.block_model_of_restricted_star_moving hb _ hCJ s (alternatingNatural 7) a⟩
    exact ⟨c.original_degree_of_alternatingSeven hn hpsl hf ha,ha⟩
  · have hm := c.block_model_of_restricted_star_moving hb _ hCJ s
      (s.action.comp ((starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)).subgroupOf _).subtype)
      ⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩
    have he : IsExceptionalA7Block c.K := by
      refine ⟨hb.short,⟨(c.block_star_quotientEquiv hb).trans e⟩,?_⟩
      rw [hm.module_card,Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hd]
    exact (c.not_exceptionalA7_block hn hpsl hf he).elim

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
