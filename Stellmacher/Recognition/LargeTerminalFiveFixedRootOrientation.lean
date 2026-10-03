module

public import Stellmacher.Recognition.LargeTerminalReeRootSeed
public import Stellmacher.Recognition.LargeTerminalFiveNormalizerData
public import Stellmacher.Recognition.LargeTerminalFiveFixedConjugateGeometry
public import Stellmacher.Recognition.LargeTerminalDerivedCentralizerFourFusion
public import Theory.GroupTheory.CoprimeSubgroupAutomorphisms

/-!
# Orienting the cyclic five-fixed root by conjugacy in the core

Write `P` for the second local group, `Q` for its two-core and `D` for the
derived first residual. A root fixed by the five-subgroup lies in `C_Q(D)`.
If its `P`-conjugates are already `Q`-conjugates, its centralizer in `P`
maps onto `P/Q`. Coprime normalizer lifting inside this centralizer then
realizes the squaring automorphism of the five-subgroup while fixing the
root, and hence the whole cyclic fixed subgroup.

The final theorem discharges the conjugacy input using the terminal geometry
proved in `LargeTerminalDerivedCentralizerFourFusion`. Its marked Ree core
and neighboring parabolic exclude inversion of the fixed root. The earlier
conditional interfaces remain available independently of this final assembly.
There is no order restriction on the squaring witness.

Source: the local identification following the cyclicity argument in
Thompson VI, printed pp.629–630; the intended root action is specified in
Shinoda (1975), pp.81–83.
-/

namespace Stellmacher.Recognition
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup
universe u

/-- Core conjugacy control for one cyclic fixed root gives a squaring
witness fixing its entire cyclic subgroup, with no order restriction. -/
public theorem LargeTerminalContext.exists_five_squaring_fixed_root_of_core_conjugacy
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096)
    (A : Subgroup G) (hA : Nat.card A = 5) (hAP : A ≤ ctx.second)
    (t : G) (htQ : t ∈ twoCoreIn ctx.second)
    (htA : t ∈ centralizer (A : Set G))
    (htgen : zpowers t = twoCoreIn ctx.second ⊓ centralizer (A : Set G))
    (horbit : ∀ b ∈ ctx.second, ∃ q ∈ twoCoreIn ctx.second,
      b * t * b⁻¹ = q * t * q⁻¹) :
    ∃ a : G, a ∈ ctx.second ∧ (∀ c ∈ A, a * c * a⁻¹ = c ^ 2) ∧
      a ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  let P := ctx.second
  let Q := pCore 2 P
  let A₀ := A.subgroupOf P
  let tP : P := ⟨t, twoCoreIn_le P htQ⟩
  let M := centralizer ({tP} : Set P)
  let f := QuotientGroup.mk' Q
  let e : A₀ ≃* A := subgroupOfEquivOfLe hAP
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hA₀ : Nat.card A₀ = 5 := (Nat.card_congr e.toEquiv).trans hA
  have hAp : IsPGroup 5 A₀ := IsPGroup.of_card (n := 1) (by simpa using hA₀)
  let _ : Fact (IsPGroup 5 A₀) := ⟨hAp⟩
  have hAM : A₀ ≤ M := by
    intro c hc
    apply mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact mem_centralizer_iff.mp htA c hc
  have hM : Function.Surjective (f.comp M.subtype) := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Q y
    obtain ⟨q, hq, heq⟩ := horbit b b.property
    let qP : P := ⟨q, twoCoreIn_le P hq⟩
    have hqQ : qP ∈ Q := (mem_map_iff_mem P.subtype_injective).mp hq
    have hqf : f qP = 1 := (QuotientGroup.eq_one_iff qP).mpr hqQ
    have hm : qP⁻¹ * b ∈ M := by
      apply mem_centralizer_singleton_iff.mpr
      apply mul_inv_eq_iff_eq_mul.mp
      apply Subtype.ext
      change (q⁻¹ * (b : G)) * t * (q⁻¹ * (b : G))⁻¹ = t
      calc
        _ = q⁻¹ * ((b : G) * t * (b : G)⁻¹) * q := by group
        _ = t := by rw [heq]; group
    refine ⟨⟨qP⁻¹ * b, hm⟩, ?_⟩
    change f (qP⁻¹ * b) = f b
    rw [map_mul, map_inv, hqf, inv_one, one_mul]
  have hcop : Nat.Coprime 5 (Nat.card f.ker) := by
    rw [QuotientGroup.ker_mk']
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := P)).exists_card_eq
    rw [hn]
    exact (show Nat.Coprime 5 2 by decide).pow_right n
  have hi : Function.Injective (f.subgroupMap A₀) := by
    have hd : Disjoint A₀ Q := hAp.disjoint_of_coprime pCore_isPGroup (by decide)
    rw [← MonoidHom.ker_eq_bot_iff]
    apply bot_unique
    intro c hc
    have hfc : f (c : P) = 1 := congrArg Subtype.val (show f.subgroupMap A₀ c = 1 from hc)
    have hcQ : (c : P) ∈ Q := (QuotientGroup.eq_one_iff (c : P)).mp hfc
    exact Subtype.ext (hd.le_bot ⟨c.property, hcQ⟩)
  have hfull : Function.Surjective A₀.normalizerMonoidHom := by
    intro α
    obtain ⟨b, hb⟩ := ctx.five_local_automorphisms_surjective hS A hA hAP
      (e.symm.trans (α.trans e))
    let bP : P := ⟨b, b.property⟩
    have hbN : bP ∈ normalizer (A₀ : Set P) := by
      rw [← subgroupOf_normalizer_eq hAP]
      exact b.val.property
    refine ⟨⟨bP, hbN⟩, ?_⟩
    apply MulEquiv.ext
    intro c
    apply e.injective
    apply Subtype.ext
    exact congrArg (fun β : MulAut A => (β (e c) : G)) hb
  have hrestricted := normalizer_action_surjective_in_subgroup
    5 A₀ M hAM f hM hcop hi hfull
  let _ : IsCyclic A₀ := isCyclic_of_prime_card hA₀
  let _ : CommGroup A₀ := IsCyclic.commGroup
  have htwo : (Nat.card A₀).Coprime 2 := by rw [hA₀]; decide
  let square : MulAut A₀ := { powCoprime htwo with
    map_mul' := fun x y => mul_pow x y 2 }
  obtain ⟨a, ha⟩ := hrestricted square
  refine ⟨(a.val.val : G), a.val.val.property, ?_, ?_⟩
  · intro c hc
    exact congrArg (fun β : MulAut A₀ => (((β (e.symm ⟨c, hc⟩)) : P) : G)) ha
  · rw [← htgen, zpowers_eq_closure, centralizer_closure]
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg (fun x : P => (x : G))
      (mem_centralizer_singleton_iff.mp a.property)

/-- Preservation of the core conjugacy classes of order-four elements in
its derived centralizer suffices for the geometric squaring witness. The
class-preservation hypothesis is the remaining geometric obligation. -/
public theorem LargeTerminalContext.exists_five_squaring_fixed_root_of_derived_centralizer_fusion
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
    (hgen : zpowers z = omegaOneCenter (S : Subgroup G))
    (hclasses : ∀ t : G, t ∈ twoCoreIn ctx.second →
      t ∈ centralizer (DerivedAmbient ctx.firstResidual : Set G) →
      orderOf t = 4 → ∀ b ∈ ctx.second, ∃ q ∈ twoCoreIn ctx.second,
        b * t * b⁻¹ = q * t * q⁻¹) :
    ∃ a : G, a ∈ ctx.second ∧ (∀ c ∈ A, a * c * a⁻¹ = c ^ 2) ∧
      a ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  obtain ⟨t, htQ, htA, _, ht4, _, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  exact ctx.exists_five_squaring_fixed_root_of_core_conjugacy hS A hA hAP
    t htQ htA htgen
    (hclasses t htQ (ctx.five_fixed_centralizes_derived A hA hAN hfixed t htQ htA) ht4)

/-- The actual terminal geometry supplies a squaring element fixing the
entire cyclic five-fixed subgroup. No order condition is imposed on it. -/
public theorem LargeTerminalContext.exists_five_squaring_fixed_root
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
    ∃ a : G, a ∈ ctx.second ∧ (∀ c ∈ A, a * c * a⁻¹ = c ^ 2) ∧
      a ∈ centralizer
        ((twoCoreIn ctx.second ⊓ centralizer (A : Set G) : Subgroup G) : Set G) := by
  obtain ⟨t, htQ, htA, _, _, _, htgen⟩ :=
    ctx.exists_five_fixed_root_of_cyclic A hAN hcard hcyc hfixed z hz hgen
  exact ctx.exists_five_squaring_fixed_root_of_core_conjugacy hS A hA hAP
    t htQ htA htgen
    (ctx.five_fixed_core_conjugacy hS A hA hAP hAN hcard hcyc hfixed t htQ htA)

end Stellmacher.Recognition
