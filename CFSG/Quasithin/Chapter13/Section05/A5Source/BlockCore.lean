module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.LocalUniqueness
public import CFSG.Quasithin.Chapter13.Section02.A5Local.FixedPoints
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFiveCentralizer
public import CFSG.Quasithin.ChapterC.Section01.LocalCoreDisplacement
public import CFSG.Quasithin.ChapterC.Section01.BlockCohomology.AlternatingFivePairSplit

/-!
# The original A₅ block with a prime-order Sylow omega-center

The original flag line has order two and lies in Ω₁Z(T). If this full
omega-center has order two, it equals that line. The marked natural module
has no component-fixed vector, so the normalized two-group C_T(L) misses
Ω₁Z(T) and is trivial. The genuine C.1.13(c) splitting then removes the
whole centralizer factor from O₂(LT) and from O₂(L). Thus the local core
has order sixteen and the component core equals U(L). Only after proving
that equality do we apply the natural-extension complement theorem.

SourceAssembly/NonsolvableBlocks uses the local core equality to construct
the required elementary subgroup of the original outside residual. No
core equality or complement is inferred from the block predicate alone.
Source: Aschbacher--Smith C.1.13(c), pp.124--125; 13.2.8(1), p.880;
the same centralizer/core argument appears in 13.2.11(1),(5), p.881.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section05.A5Source.Context
open ChapterC
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
include d

/-- The original component has trivial Sylow centralizer when the full omega-center is a line. -/
theorem sylow_centralizer_eq_bot_of_omega_card_two
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have h1Z : V₁ ≤ omegaOneCenterAmbient (T : Subgroup G) := by
    intro v hv
    have hf := d.flag.module_fixed_eq_line.ge hv
    let := d.elementary
    exact (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨d.chosen.le_sylow hf.1,elemPow_eq_one_of_isElementaryAbelian v hf.1,hf.2⟩
  have he : V₁ = omegaOneCenterAmbient (T : Subgroup G) :=
    eq_of_le_of_card_ge h1Z (by rw [d.flag.one_card,hz])
  apply Section06.CentralizerReduction.centralizer_T_eq_bot_of_omega
    (T : Subgroup G) L T.isPGroup' d.normalizes_L
  apply bot_unique
  intro x hx
  exact d.flag.module.fixed_eq_bot.le
    ⟨(d.flag.one_le_two.trans d.flag.two_le_V) (he.ge hx.1),hx.2⟩

/-- The block split identifies the local two-core and gives its order. -/
theorem block_local_core_card_of_omega_card_two
    (hb : IsAlternatingBlock L 5)
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    Nat.card (pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G)) = 16 := by
  have hsplit := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
    (sup_le L.le_normalizer d.normalizes_L)
  have hQT : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) :=
    map_le_iff_le_comap.mpr
      (pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right))
  have hzero : (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hQT).trans
      (d.sylow_centralizer_eq_bot_of_omega_card_two hz).le)
  rw [hzero,sup_bot_eq] at hsplit
  have hc := congrArg (fun A : Subgroup G => Nat.card A) hsplit
  simpa only [pCoreIn,card_map_of_injective (L ⊔ (T : Subgroup G)).subtype_injective,
    card_map_of_injective L.subtype_injective,hb.blockU_card] using hc

/-- The same centralizer calculation gives the literal component-core equality. -/
theorem block_core_eq_module_of_omega_card_two
    (hb : IsAlternatingBlock L 5)
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    pCore 2 L = blockU L := by
  have hsplit := hb.normalizer_twoCore_eq_module_sup_centralizer
    (show L ≤ L from le_rfl) L.le_normalizer
  have hQT : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer d.normalizes_L)).trans
      (map_le_iff_le_comap.mpr
        (pCore_isPGroup.le_sylow_of_normal (T.subtype le_sup_right)))
  have hzero : L.pCoreIn 2 ⊓ centralizer (L : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ hQT).trans
      (d.sylow_centralizer_eq_bot_of_omega_card_two hz).le)
  rw [hzero,sup_bot_eq] at hsplit
  exact (map_injective L.subtype_injective) hsplit

/-- The established core equality permits the genuine group complement. -/
theorem block_core_complement_of_omega_card_two
    (hb : IsAlternatingBlock L 5)
    (hz : Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2) :
    ∃ A : Subgroup L, (pCore 2 L).IsComplement' A :=
  hb.exists_core_complement (d.block_core_eq_module_of_omega_card_two hb hz)
end CFSG.Quasithin.Chapter13.Section05.A5Source.Context
