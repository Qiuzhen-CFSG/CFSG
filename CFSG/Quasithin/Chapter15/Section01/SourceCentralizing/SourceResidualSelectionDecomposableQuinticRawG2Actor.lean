module

public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.G2FullActor
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.FixedLayerCentralizer
public import Theory.GroupTheory.PResidual.PrimeToPerfect
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction

/-!
# Quotient-centralizing actors on the full binary G₂ block

A block automorphism trivial on its two-core quotient has trivial full G₂
actor, hence fixes the actual natural module quotient. The three-subgroups
lemma lifts this across the central attachment of U(X), since the two-core
centralizes U(X) and [U(X),X]=U(X). A two-perfect actor then centralizes the
whole short group. In particular the actor need not be a two-group or lie
in a component-Sylow product.

The native full automorphism group of G₂(2)′ has order 12096, prime to
five, so every normalizing five-group fixes the full block.

This is the intrinsic lifting needed for the original quintic source row;
no ambient source or residual-normalization premise is used. The internal
AutomorphismAction import identifies its hidden actor with the literal
two-core projection only inside the private proof; its public API is unchanged.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC

private theorem g2_module_fixed_of_quotient_fixed
    {L : Type*} [Group L] (m : BlockModuleModel L g2TwoNaturalAction)
    (a : MulAut L) (ha : quotientAut (pCore 2 L) a = 1) :
    blockModuleAut a = 1 := by
  have hq : m.quotientAction a = 1 := by
    apply MulEquiv.ext
    intro g
    obtain ⟨l,rfl⟩ := m.actor_surjective g
    rw [m.quotientAction_actor]
    have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 L) l)
    rw [quotientAut_apply_mk] at hh
    exact congrArg m.quotientIso hh
  have hg : m.g2FullActor a = 1 := by
    apply Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.injective
    rw [m.g2FullActor_conjugation,hq,map_one]
  have hb : m.moduleAction a = 1 := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    change (m.moduleAction a (Multiplicative.ofAdd v.toAdd)).toAdd = v.toAdd
    rw [m.g2_moduleAction_eq_natural,hg,map_one]
    rfl
  apply MulEquiv.ext
  intro v
  apply m.moduleIso.injective
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) v
  have hh := DFunLike.congr_fun hb (m.moduleIso (QuotientGroup.mk' (blockFixed L) u))
  change m.moduleAction a (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)) = _ at hh
  rw [m.moduleAction_mk] at hh
  rw [blockModuleAut_apply_mk]
  exact hh

variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect actor fixing the literal two-core quotient of a binary
G₂ block centralizes the whole block, including its central attachment. -/
theorem IsG2TwoBlock.centralizes_of_coreQuotient
    {X Y : Subgroup G} (hX : IsG2TwoBlock X) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (X : Set G)) (hcore : ⁅Y,X⁆ ≤ X.pCoreIn 2) :
    Y ≤ centralizer (X : Set G) := by
  let U := (blockU X).map X.subtype
  have hAU : ⁅Y,U⁆ ≤ centralizer (X : Set G) := by
    apply commutator_le.mpr
    intro y hy u hu
    let a : MulAut X := X.normalizerMonoidHom ⟨y,hn hy⟩
    have hq : quotientAut (pCore 2 X) a = 1 := by
      apply MulEquiv.ext
      intro z
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
      rw [quotientAut_apply_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      obtain ⟨w,hw,he⟩ := hcore (commutator_mem_commutator hy x.property)
      simp only [div_eq_mul_inv]
      exact (Subtype.ext he : w = a x * x⁻¹) ▸ hw
    obtain ⟨m⟩ := hX.natural_model
    have hm := g2_module_fixed_of_quotient_fixed m a hq
    obtain ⟨w,hw,rfl⟩ := hu
    have hh := DFunLike.congr_fun hm (QuotientGroup.mk' (blockFixed X) ⟨w,hw⟩)
    rw [blockModuleAut_apply_mk] at hh
    have hc0 : MulAut.characteristic (blockU X) a ⟨w,hw⟩ / (⟨w,hw⟩ : blockU X) ∈
        blockFixed X := QuotientGroup.eq_iff_div_mem.mp hh
    change (a w / w : X) ∈ center X at hc0
    have hc : (a w * w⁻¹ : X) ∈ center X := by
      simpa only [div_eq_mul_inv] using hc0
    intro x hx
    exact congrArg X.subtype (mem_center_iff.mp hc ⟨x,hx⟩)
  have hOU : X.pCoreIn 2 ≤ centralizer (U : Set G) :=
    (map_mono hX.short.core_centralizes_blockU).trans
      (map_centralizer_le_centralizer_image _ X.subtype)
  have hrot : ⁅⁅U,X⁆,Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (commutator_eq_bot_iff_le_centralizer.mpr (by rw [commutator_comm]; exact hcore.trans hOU))
    (commutator_eq_bot_iff_le_centralizer.mpr hAU)
  have hUX : ⁅U,X⁆ = U := by
    have hi := commutator_isPPerfect_idempotent X (X.pCoreIn 2)
      hX.short.twoPerfect (isPGroup_pCoreIn 2 X)
      (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    simpa only [pCoreIn,U,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hi
  rw [hUX] at hrot
  exact hX.short.centralizes_of_normalizing_coreQuotient_and_blockU X Y hY hn hcore
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hrot))

/-- A five-group normalizing a binary G₂ block fixes its full cover. -/
theorem IsG2TwoBlock.quintic_centralizes
    {L Y : Subgroup G} (hL : IsG2TwoBlock L)
    (hY : IsPGroup 5 Y) (hn : Y ≤ normalizer (L : Set G)) :
    Y ≤ centralizer (L : Set G) := by
  let a : Y →* MulAut L := L.normalizerMonoidHom.comp (inclusion hn)
  let q := (quotientAut (pCore 2 L)).comp a
  have hc : Nat.card (MulAut (L ⧸ pCore 2 L)) = 12096 := by
    obtain ⟨e⟩ := hL.quotient_iso
    rw [Nat.card_congr (MulAut.congr e).toEquiv,
      ←Nat.card_congr Atlas.G2.LieAutomorphismExtensions.binaryAutomorphismEquiv.toEquiv]
    exact Atlas.G2.LieAutomorphismExtensions.card_binaryFull
  have hq (y : Y) : q y = 1 := by
    obtain ⟨n,hn⟩ := hY y
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes ((by decide : Nat.Coprime 5 12096).pow_left n)
    · exact orderOf_dvd_of_pow_eq_one (by rw [←map_pow,hn,map_one])
    · simpa only [hc] using orderOf_dvd_natCard (q y)
  have hperf : IsPPerfect 2 Y := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have he : primeToResidual 5 Y = ⊤ := by
      apply top_unique
      intro y _
      obtain ⟨n,hn⟩ := hY y
      exact mem_primeToResidual_of_pow hn
    exact (isPPerfect_primeToResidual (G := Y) 5 2 (by decide)).of_surjective
      (primeToResidual 5 Y).subtype (by
        intro y
        exact ⟨⟨y,he ▸ mem_top y⟩,rfl⟩)
  apply hL.centralizes_of_coreQuotient hperf hn
  apply commutator_le.mpr
  intro y hy l hl
  have he := DFunLike.congr_fun (hq ⟨y,hy⟩)
    (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩)
  change quotientAut (pCore 2 L) (a ⟨y,hy⟩)
    (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩) = _ at he
  rw [quotientAut_apply_mk] at he
  have hh : a ⟨y,hy⟩ ⟨l,hl⟩ * (⟨l,hl⟩ : L)⁻¹ ∈ pCore 2 L := by
    simpa only [div_eq_mul_inv] using QuotientGroup.eq_iff_div_mem.mp he
  exact mem_map.mpr ⟨_,hh,rfl⟩

end CFSG.Quasithin.ChapterC
