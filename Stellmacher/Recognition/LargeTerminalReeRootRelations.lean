module

public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalSylowArithmetic
public import Stellmacher.Recognition.LargeTerminalReeActionCoordinates
public import Stellmacher.Recognition.LargeTerminalReeStandardAction
public import Theory.SpecificGroups.ReeTwo.RootRelationsTransport
public import Theory.SpecificGroups.ReeTwo.FixingActionStandardization

/-!
# Actual terminal roots and their complement action

At the order-4096 endpoint the first residual R has index two in the
actual second core Q. The cyclic five-fixed subgroup supplies t outside R
with t² = z. Thus Q = R ⊔ ⟨t⟩, and R ∩ ⟨t⟩ = ⟨z⟩ because fixed elements
of R are central and Z(R) = ⟨z⟩. This same t lies in the actual two-core
of C_G(z), retaining all ambient subgroup equalities.

The checked core construction and compatible squaring lift now supply
actual coordinates and one of twenty fixing census actions. For every
standard census entry we correct the actual actor and construct all ten
roots, root 1 and the Weyl element with their full relations and markings.
The neighboring parabolic excludes the nonstandard entries by the checked
standard-action selection theorem. Combining these results completes actual
root extraction with cyclicity of the five-fixed subgroup as an explicit input.

Source: Thompson, Nonsolvable finite groups VI, pp.629–630; Shinoda,
A characterization of odd order extensions of the Ree groups (1975),
(2.3), pp.81–83. Cyclicity is an explicit input throughout.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- Any element of the second core outside the first residual supplements
that residual at the upper endpoint. -/
public theorem LargeTerminalContext.second_core_eq_residual_sup_seed
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second) (htR : t ∉ ctx.firstResidual) :
    twoCoreIn ctx.second = ctx.firstResidual ⊔ zpowers t := by
  let Q := twoCoreIn ctx.second
  let R := ctx.firstResidual
  obtain ⟨_, _, _, hlo, hhi, _⟩ := ctx.involution_centralizer_core
  have hRQ : R ≤ Q := hlo.trans hhi
  have hindex : (R.subgroupOf Q).index = 2 :=
    ctx.sylow_card_eq_4096_iff.mp hS
  apply le_antisymm _ (sup_le hRQ (zpowers_le.mpr htQ))
  intro q hqQ
  by_cases hqR : q ∈ R
  · exact (show R ≤ R ⊔ zpowers t from le_sup_left) hqR
  · have hprod : q * t⁻¹ ∈ R := by
      have h := (R.subgroupOf Q).mul_mem_iff_of_index_two hindex
        (a := ⟨q, hqQ⟩) (b := ⟨t⁻¹, Q.inv_mem htQ⟩)
      exact h.mpr (by simpa only [mem_subgroupOf, inv_mem_iff] using
        (iff_of_false hqR htR))
    have hm : (q * t⁻¹) * t ∈ R ⊔ zpowers t :=
      mul_mem ((show R ≤ R ⊔ zpowers t from le_sup_left) hprod)
        ((show zpowers t ≤ R ⊔ zpowers t from le_sup_right) (mem_zpowers t))
    simpa only [inv_mul_cancel_right] using hm

/-- The fixed root meets the residual in exactly the designated central line. -/
public theorem LargeTerminalContext.residual_inf_seed_eq_central_line
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (A : Subgroup G)
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (t : G) (htA : t ∈ centralizer (A : Set G)) (htsq : t ^ 2 = z) :
    ctx.firstResidual ⊓ zpowers t = zpowers z := by
  have hcenter : CenterAmbient ctx.firstResidual = zpowers z :=
    ctx.first_residual_center_eq_omegaOneCenter.trans hgen.symm
  have hzR : z ∈ ctx.firstResidual :=
    (show zpowers z ≤ ctx.firstResidual from hcenter ▸ map_subtype_le _) (mem_zpowers z)
  apply le_antisymm
  · rintro g ⟨hgR, hgt⟩
    have hgA : g ∈ centralizer (A : Set G) := (zpowers_le.mpr htA) hgt
    have hgZ : (⟨g, hgR⟩ : ctx.firstResidual) ∈ center ctx.firstResidual :=
      hfixed hgA
    rw [← hcenter]
    exact mem_map.mpr ⟨⟨g, hgR⟩, hgZ, rfl⟩
  · apply zpowers_le.mpr
    exact ⟨hzR, htsq ▸ (zpowers t).pow_mem (mem_zpowers t) 2⟩

/-- The cyclic fixed root lies in the actual full-centralizer two-core and
supplies its index-two extension of the first residual. -/
public theorem LargeTerminalContext.exists_ree_core_seed_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ t : centralizer ({z} : Set G),
      t ∈ pCore 2 (centralizer ({z} : Set G)) ∧
      (t : G) ∈ centralizer (A : Set G) ∧
      (t : G) ∉ ctx.firstResidual ∧ orderOf t = 4 ∧ (t : G) ^ 2 = z ∧
      zpowers (t : G) = twoCoreIn ctx.second ⊓ centralizer (A : Set G) ∧
      twoCoreIn ctx.second = ctx.firstResidual ⊔ zpowers (t : G) ∧
      ctx.firstResidual ⊓ zpowers (t : G) = zpowers z := by
  obtain ⟨t, htQ, htA, htR, ht4, htsq, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  let C := centralizer ({z} : Set G)
  have htcore : t ∈ twoCoreIn C := by
    rw [(ctx.involution_centralizer_core_eq_at_generator hS z hgen).1]
    exact htQ
  have htC : t ∈ C := twoCoreIn_le C htcore
  let tc : C := ⟨t, htC⟩
  have htc : tc ∈ pCore 2 C :=
    (mem_map_iff_mem C.subtype_injective).mp htcore
  refine ⟨tc, htc, htA, htR, ?_, htsq, htgen,
    ctx.second_core_eq_residual_sup_seed hS t htQ htR,
    ctx.residual_inf_seed_eq_central_line A hfixed z hgen t htA htsq⟩
  rw [← Subgroup.orderOf_coe]
  exact ht4


/-- Actual normalized core actions supply every required root relation,
including membership in the literal full-centralizer two-core. -/
public theorem LargeTerminalContext.exists_ree_root_relations_of_normalized_action
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (e : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (hez : (e.symm (ReeTwo.Core.root 9) : G) = z)
    (c a : ctx.second) (hc5 : c ^ 5 = 1) (ha4 : a ^ 4 = 1)
    (hac : a * c * a⁻¹ = c ^ 2)
    (hc : ctx.reeCoreAction e c = ReeTwo.Core.c)
    (ha : ctx.reeCoreAction e a = ReeTwo.Core.a) :
    ∃ (x : ReeTwo.CoreRoot → centralizer ({z} : Set G))
      (s w : centralizer ({z} : Set G)),
      ReeTwo.CoreRelations x ∧ ReeTwo.RootOneRelations s x ∧
      (∀ i, w * x i * w⁻¹ = x (ReeTwo.weylRoot i)) ∧
      ((s⁻¹) ^ 2 * w) ^ 5 = 1 ∧ (s⁻¹) ^ 4 = 1 ∧
      s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2 ∧
      (∀ i, x i ∈ pCore 2 (centralizer ({z} : Set G))) ∧
      (x 9 : G) = z := by
  let C := centralizer ({z} : Set G)
  have hCP : C = ctx.second := ctx.involution_centralizer_eq_second hS z hz hgen
  let j : ctx.second →* C :=
    { toFun := fun b => ⟨b, hCP.symm ▸ b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f : ReeTwo.Core →* C := j.comp
    ((inclusion (twoCoreIn_le ctx.second)).comp e.symm.toMonoidHom)
  have hf (q : ReeTwo.Core) : (f q : G) = (e.symm q : G) := rfl
  have haction (b : ctx.second) (q : ReeTwo.Core) :
      j b * f q * (j b)⁻¹ = f (ctx.reeCoreAction e b q) := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hf,
      show (j b : G) = (b : G) from rfl]
    have hh := ctx.reeCoreAction_apply e b (e.symm q)
    simpa only [e.apply_symm_apply] using hh.symm
  have hrels := ReeTwo.root_relations_of_normalized_action f (j a) (j c)
    (by rw [← map_pow, ha4, map_one]) (by rw [← map_pow, hc5, map_one])
    (by rw [← map_inv, ← map_mul, ← map_mul, hac, map_pow])
    (by intro q; rw [haction, ha]) (by intro q; rw [haction, hc])
  refine ⟨fun i => f (ReeTwo.Core.root i), (j a)⁻¹, (j a) ^ 2 * j c,
    hrels.1, hrels.2.1, hrels.2.2.1, hrels.2.2.2.1, hrels.2.2.2.2.1,
    hrels.2.2.2.2.2, ?_, hez⟩
  intro i
  apply (mem_map_iff_mem C.subtype_injective).mp
  change (f (ReeTwo.Core.root i) : G) ∈ twoCoreIn C
  rw [(ctx.involution_centralizer_core_eq_at_generator hS z hgen).1, hf]
  exact (e.symm (ReeTwo.Core.root i)).property


/-- The standard half of the fixing census suffices for complete extraction.
The correction changes only actual elements, retaining the marked core. -/
public theorem LargeTerminalContext.exists_ree_root_relations_of_standard_census
    {G : Type*} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (e : twoCoreIn ctx.second ≃* ReeTwo.Core)
    (hez : (e.symm (ReeTwo.Core.root 9) : G) = z)
    (c a : ctx.second) (hc5 : c ^ 5 = 1) (ha4 : a ^ 4 = 1)
    (hac : a * c * a⁻¹ = c ^ 2)
    (hc : ctx.reeCoreAction e c = ReeTwo.Core.c)
    (i : Fin 20) (hi : ReeTwo.Core.FixingActionCensus.IsStandard i)
    (ha : ctx.reeCoreAction e a = ReeTwo.Core.FixingActionCensus.representative i) :
    ∃ (x : ReeTwo.CoreRoot → centralizer ({z} : Set G))
      (s w : centralizer ({z} : Set G)),
      ReeTwo.CoreRelations x ∧ ReeTwo.RootOneRelations s x ∧
      (∀ i, w * x i * w⁻¹ = x (ReeTwo.weylRoot i)) ∧
      ((s⁻¹) ^ 2 * w) ^ 5 = 1 ∧ (s⁻¹) ^ 4 = 1 ∧
      s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2 ∧
      (∀ i, x i ∈ pCore 2 (centralizer ({z} : Set G))) ∧
      (x 9 : G) = z := by
  let f := ctx.reeCoreAction e
  let tQ := e.symm (ReeTwo.Core.root 2)
  let j := inclusion (twoCoreIn_le ctx.second)
  let t := j tQ
  have ht4 : t ^ 4 = 1 := by
    change j (e.symm (ReeTwo.Core.root 2)) ^ 4 = 1
    rw [← map_pow, ← map_pow,
      show ReeTwo.Core.root 2 ^ 4 = 1 from by decide +kernel, map_one, map_one]
  have hfix (b : ctx.second) (hb : f b (ReeTwo.Core.root 2) = ReeTwo.Core.root 2) :
      Commute b t := by
    change b * t = t * b
    apply Subtype.ext
    have hh := ctx.reeCoreAction_apply e b tQ
    change (e.symm (f b (e tQ)) : G) = (b : G) * (tQ : G) * (b : G)⁻¹ at hh
    rw [show e tQ = ReeTwo.Core.root 2 from e.apply_symm_apply _, hb] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh.symm
  have hct : Commute c t := hfix c (by
    rw [show f c = ReeTwo.Core.c from hc]
    exact (by decide +kernel : ReeTwo.Core.c (ReeTwo.Core.root 2) = ReeTwo.Core.root 2))
  have hat : Commute a t := hfix a (by
    rw [show f a = ReeTwo.Core.FixingActionCensus.representative i from ha]
    exact ReeTwo.Core.FixingActionCensus.representative_root_two i)
  have ht : f t = MulAut.conj (ReeTwo.Core.root 2) := by
    apply ReeTwo.Core.aut_ext
    intro k
    apply e.symm.injective
    apply Subtype.ext
    have hh := ctx.reeCoreAction_apply e t (e.symm (ReeTwo.Core.root k))
    rw [e.apply_symm_apply] at hh
    rw [hh]
    change (tQ : G) * (e.symm (ReeTwo.Core.root k) : G) * (tQ : G)⁻¹ =
      (e.symm (ReeTwo.Core.root 2 * ReeTwo.Core.root k * (ReeTwo.Core.root 2)⁻¹) : G)
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  obtain ⟨b, hb4, hbc, hb⟩ := ReeTwo.Core.FixingActionCensus.exists_standard_actor
    f c a t ha4 ht4 hac hct hat hc ht i hi ha
  exact ctx.exists_ree_root_relations_of_normalized_action hS z hz hgen e hez
    c b hc5 hb4 hbc hc hb

/-- The actual terminal centralizer has all Ree root relations when its
order-four five-fixed subgroup is cyclic. The roots lie in its actual two-core,
and the last root is the prescribed omega-central involution. -/
public theorem LargeTerminalContext.exists_ree_root_relations_of_cyclic
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (hAN : A ≤ normalizer (ctx.firstResidual : Set G))
    (hcard : Nat.card ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)) = 4)
    (hcyc : IsCyclic ((centralizer (A : Set G)).subgroupOf
      (twoCoreIn ctx.second)))
    (hfixed : (centralizer (A : Set G)).subgroupOf ctx.firstResidual ≤
      center ctx.firstResidual)
    (z : G) (hz : orderOf z = 2)
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G)) :
    ∃ (x : ReeTwo.CoreRoot → centralizer ({z} : Set G))
      (s w : centralizer ({z} : Set G)),
      ReeTwo.CoreRelations x ∧ ReeTwo.RootOneRelations s x ∧
      (∀ i, w * x i * w⁻¹ = x (ReeTwo.weylRoot i)) ∧
      ((s⁻¹) ^ 2 * w) ^ 5 = 1 ∧ (s⁻¹) ^ 4 = 1 ∧
      s⁻¹ * ((s⁻¹) ^ 2 * w) * (s⁻¹)⁻¹ = ((s⁻¹) ^ 2 * w) ^ 2 ∧
      (∀ i, x i ∈ pCore 2 (centralizer ({z} : Set G))) ∧
      (x 9 : G) = z := by
  obtain ⟨e, c, a, i, hez, _, _, hc5, ha4, hac, hc, ha, hi⟩ :=
    ctx.exists_ree_standard_census_action_of_cyclic
      hS A hA hAP hAN hcard hcyc hfixed z hz hgen
  exact ctx.exists_ree_root_relations_of_standard_census hS z hz hgen e hez
    c a hc5 ha4 hac hc i hi ha

end Stellmacher.Recognition
