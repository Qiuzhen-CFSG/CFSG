module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternativesDegrees
public import Theory.Representation.SL2.PerfectCoreQuotientDegree
public import Theory.Representation.GeneralLinearNatural
public import Theory.GroupTheory.NormalSylowQuotientAction

/-!
# The original rank-one section in binary linear star models

The literal L-image is perfect and retains L/O₂(L) after taking its own
two-core quotient. Its nontrivial natural binary representation therefore has
dimension at least 2n. The source Sylow intersection supplies a full Sylow in
the star local, and that local normalizes the same L-image in every marking.
These facts feed the A₈ and SL₅(2) exclusions without changing the full W.
Source: Aschbacher–Smith C.4.1(4), C.4.5 and 4.3.7, pp.151–153,615–616;
the binary degree bound is the defining-characteristic SL₂ bound.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open ChapterC Chapter1.RadicalExclusions.ModelReduction FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
/-- A binary linear marking bounds the original rank-one field degree. -/
theorem SourceConfiguration.binary_linear_degree_bound (c : SourceConfiguration T L) {n d : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2^n))
    (e : (c.K ⧸ pCore 2 c.K) ≃* SL(d,ZMod 2)) : 2*n ≤ d := by
  obtain ⟨F, _, _, hF, ⟨a⟩⟩ := hpsl
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) (by
    simpa only [Nat.card_eq_fintype_card] using hF)
  let a' := c.originalLocalCoreEquiv.symm.trans (a.trans (Theory.PSL2.sl2QuotientEquiv F).symm)
  let : Group.IsPerfect c.componentQuotientL := c.componentQuotientL_perfect
  let : Nontrivial c.componentQuotientL :=
    c.componentQuotientL.nontrivial_iff_ne_bot.mpr c.componentQuotientL_ne_bot
  let ρ := (Representation.specialLinearNatural (k := ZMod 2) d).comp
    (e.toMonoidHom.comp c.componentQuotientL.subtype)
  have hi : Function.Injective ρ := (Representation.specialLinearNatural_injective d).comp
    (e.injective.comp c.componentQuotientL.subtype_injective)
  obtain ⟨x,hx⟩ := exists_ne (1 : c.componentQuotientL)
  have hnt : ∃ x, ρ x ≠ 1 := ⟨x,fun he => hx (hi (he.trans ρ.map_one.symm))⟩
  simpa only [Module.finrank_fin_fun] using
    Representation.SL2.perfect_core_quotient_finrank_bound a' ρ hnt (by omega) hF

/-- The literal star local contains a full Sylow subgroup of the component. -/
theorem SourceConfiguration.block_star_local_sylow
    (c : SourceConfiguration T L) :
    ∃ U : Sylow 2 (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.K.map c.H.subtype)),
      (U : Subgroup _) ≤ (starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
        (c.H ⊓ normalizer (L : Set G))).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)) := by
  obtain ⟨P,hP⟩ := c.sylow
  let : c.K.Normal := c.component_normal
  obtain ⟨Q,hQ⟩ := Subgroup.NormalSylowQuotientAction.intersection_sylow P c.K
    (by rw [normalizer_eq_top]; exact le_top)
  let a := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  let f := (toStarImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)).comp a.toMonoidHom
  have hf : Function.Surjective f :=
    (toStarImage_surjective _ _).comp a.surjective
  refine ⟨Q.mapSurjective hf,?_⟩
  rintro x ⟨k,hk,rfl⟩
  have hkP : (k : c.H) ∈ (P : Subgroup c.H) := by
    change k ∈ (Q : Subgroup c.K) at hk
    rw [hQ] at hk
    exact hk
  have hkS : ((k : c.H) : G) ∈ (T : Subgroup G) ⊓ c.H := by
    rw [←hP]
    exact mem_map_of_mem c.H.subtype hkP
  have hkM : ((k : c.H) : G) ∈ c.H ⊓ normalizer (L : Set G) :=
    ⟨(k : c.H).property,c.normalizer_sylow (le_normalizer hkS)⟩
  exact mem_map_of_mem (QuotientGroup.mk' (starKernel _ _))
    (show ((k : c.H) : G) ∈ (c.H ⊓ normalizer (L : Set G)) ⊓ c.K.map c.H.subtype
      from ⟨hkM,mem_map_of_mem c.H.subtype k.property⟩)

/-- The original local image remains a normal subgroup of the literal star local. -/
theorem SourceConfiguration.block_star_local_image
    (c : SourceConfiguration T L) (hb : IsBlock c.K)
    {A : Type*} [Group A]
    (e : starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.K.map c.H.subtype) ≃* A) :
    let P := ((starM (c.K.map c.H.subtype) (c.I.pCoreIn 2)
      (c.H ⊓ normalizer (L : Set G))).subgroupOf
        (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2)
          (c.K.map c.H.subtype))).map e.toMonoidHom
    let B := c.componentQuotientL.map ((c.block_star_quotientEquiv hb).trans e).toMonoidHom
    B ≤ P ∧ P ≤ normalizer (B : Set A) := by
  let C := starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) (c.K.map c.H.subtype)
  let B₀ := (starImage (c.K.map c.H.subtype) (c.I.pCoreIn 2) L).subgroupOf C
  have hB := c.componentQuotientL_star hb
  have hm : c.componentQuotientL.map ((c.block_star_quotientEquiv hb).trans e).toMonoidHom =
      B₀.map e.toMonoidHom := by
    rw [show ((c.block_star_quotientEquiv hb).trans e).toMonoidHom =
      e.toMonoidHom.comp (c.block_star_quotientEquiv hb).toMonoidHom from rfl,
      ←map_map,hB]
  dsimp only
  rw [hm]
  constructor
  · apply map_mono
    apply comap_mono
    apply map_mono
    apply comap_mono
    exact le_inf (le_inf (c.le_I.trans c.I_le_H) L.le_normalizer) c.le_component
  · rw [←map_equiv_normalizer_eq B₀ e]
    exact map_mono c.block_star_local_normalizes_L
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
