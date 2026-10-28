module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.Basic
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal.SevenRatio
/-!
# Actors from the involution-centralizer geometry

An actual A₅ subgroup of C_G(z) supplies a double transposition inverting
its standard three-cycle. Sylow conjugacy inside C_G(z) transports this
involution to the literal normalizer of the chosen seed X. The A₅ subgroup
is also proved to complement the intrinsic extraspecial core.

For the order-eight actor, the remaining finite model calculation asks for
q fixed by the cubic action whose norm q·r(q) has order four. The square of
q·r is precisely that norm. `eight_of_core_norm` proves all transport and
membership statements, while keeping this finite calculation explicit.
`Actors.Source` constructs the A₅ embedding from the earlier 47.1–47.2
conclusions. No semidihedral or 47.3 identification is assumed here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.2(2), printed p.261,
and the initial local-normalizer calculation in the proof of 47.3, p.262.
The explicit A₅ permutations also appear in
`Theory.SpecificGroups.Alternating.FiveLocalGeometry`.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
private def cubicCycle : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩
private def cubicFlip : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 3 4, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide +kernel⟩
private theorem cubicCycle_order : orderOf cubicCycle = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem cubicFlip_order : orderOf cubicFlip = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private theorem cubicFlip_inverts :
    cubicFlip * cubicCycle * cubicFlip⁻¹ = cubicCycle⁻¹ := by decide +kernel
variable {G : Type*} [Group G] [Finite G] (D : Seed G)

/-- Construct an inverting involution from an actual A₅ inside the seed centralizer. -/
theorem inverter_of_alternating_embedding (f : alternatingGroup (Fin 5) →* G)
    (hf : Function.Injective f) (hfH : f.range ≤ involutionCentralizer D.z) :
    ∃ m : M D, orderOf m = 2 ∧
      ∀ x : D.X, (m : G) * x * (m : G)⁻¹ = (x : G)⁻¹ := by
  let Y := zpowers (f cubicCycle)
  have hY : Nat.card Y = 3 := by
    rw [Nat.card_zpowers, orderOf_injective f hf, cubicCycle_order]
  have hYH : Y ≤ involutionCentralizer D.z :=
    zpowers_le.mpr (hfH ⟨cubicCycle, rfl⟩)
  obtain ⟨g, hg⟩ := D.conjugate_of_le_centralizer Y hY hYH
  let a : G ≃* G := MulAut.conj (g : G)
  have hXY : D.X.map a.toMonoidHom = Y := hg
  let r : G := a.symm (f cubicFlip)
  have hr : orderOf r = 2 := by
    rw [show r = a.symm (f cubicFlip) from rfl, a.symm.orderOf_eq,
      orderOf_injective f hf, cubicFlip_order]
  have hinv (x : G) (hx : x ∈ D.X) : r * x * r⁻¹ = x⁻¹ := by
    apply a.injective
    have hxY : a x ∈ Y := hXY ▸ mem_map_of_mem a.toMonoidHom hx
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hxY
    have hflip : f cubicFlip * f cubicCycle * (f cubicFlip)⁻¹ = (f cubicCycle)⁻¹ := by
      simpa only [map_mul, map_inv] using congrArg f cubicFlip_inverts
    have hnflip := congrArg (fun y : G => y ^ n) hflip
    have ha : a r = f cubicFlip := a.apply_symm_apply _
    rw [map_mul, map_mul, map_inv, map_inv, ha, ← hn]
    simpa only [conj_zpow, inv_zpow] using hnflip
  have hrM : r ∈ M D := by
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      rw [hinv x hx]
      exact inv_mem hx
    · intro hx
      have hi := hinv (r * x * r⁻¹) hx
      have hrr : r * r = 1 := by
        have hp := pow_orderOf_eq_one r
        rw [hr, pow_two] at hp
        exact hp
      have hir : r⁻¹ = r := inv_eq_of_mul_eq_one_left hrr
      have he : r * (r * x * r⁻¹) * r⁻¹ = x := by
        calc
          _ = (r * r) * x * (r * r) := by rw [hir]; group
          _ = x := by rw [hrr, one_mul, mul_one]
      rw [he] at hi
      rw [hi]
      exact inv_mem hx
  exact ⟨⟨r, hrM⟩, (orderOf_coe _).symm.trans hr, fun x => hinv x x.property⟩

open Theory.GroupTheory

private theorem preimage_core_eq_bot
    (f : alternatingGroup (Fin 5) →* involutionCentralizer D.z)
    (hf : Function.Injective f) : (localCore D.z).comap f = ⊥ := by
  let : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases (inferInstance : ((localCore D.z).comap f).Normal).eq_bot_or_eq_top with h | h
  · exact h
  · have hle : f.range ≤ localCore D.z := by
      rintro _ ⟨x, rfl⟩
      exact show x ∈ (localCore D.z).comap f from h ▸ mem_top x
    have hd := card_dvd_of_le hle
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      nat_card_alternatingGroup, D.localType.core_card] at hd
    norm_num [Nat.factorial] at hd

/-- An embedded A₅ is an actual complement to the intrinsic extraspecial core. -/
theorem alternating_complement
    (f : alternatingGroup (Fin 5) →* involutionCentralizer D.z)
    (hf : Function.Injective f) : f.range.IsComplement' (localCore D.z) := by
  apply isComplement'_of_card_mul_and_disjoint
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
      nat_card_alternatingGroup, D.localType.core_card, D.localType.centralizer_card]
    norm_num [Nat.factorial]
  · apply disjoint_iff.mpr
    apply bot_unique
    rintro y ⟨⟨x, rfl⟩, hx⟩
    have hx1 : x = 1 := by
      have hx' : x ∈ (localCore D.z).comap f := hx
      rwa [preimage_core_eq_bot D f hf, mem_bot] at hx'
    simp only [hx1, map_one, mem_bot]

private theorem coreAction_injective
    (f : alternatingGroup (Fin 5) →* involutionCentralizer D.z)
    (hf : Function.Injective f)
    (hcentral : centralizer (localCore D.z : Set (involutionCentralizer D.z)) ≤
      localCore D.z) :
    Function.Injective ((MulAut.conjNormal : involutionCentralizer D.z →*
      MulAut (localCore D.z)).comp f) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  have hfix : ∀ q : localCore D.z, MulAut.conjNormal (f a) q = q := by
    intro q
    exact DFunLike.congr_fun ha q
  have hc : f a ∈ centralizer (localCore D.z : Set (involutionCentralizer D.z)) := by
    intro q hq
    have he := congrArg Subtype.val (hfix ⟨q, hq⟩)
    change f a * q * (f a)⁻¹ = q at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hm : a ∈ (localCore D.z).comap f := hcentral hc
  rwa [preimage_core_eq_bot D f hf] at hm

private theorem order_eight_of_square {H : Type*} [Group H] [Finite H]
    (s : H) (hs : orderOf (s ^ 2) = 4) : orderOf s = 8 := by
  have hg := (Nat.dvd_prime Nat.prime_two).mp (Nat.gcd_dvd_right (orderOf s) 2)
  rw [orderOf_pow] at hs
  rcases hg with hg | hg
  · rw [hg, Nat.div_one] at hs
    norm_num [hs] at hg
  · rw [hg] at hs
    have hd := Nat.gcd_dvd_left (orderOf s) 2
    rw [hg] at hd
    omega

/-- Transfer a local normalizing actor to the literal seed normalizer. -/
theorem normalizer_actor_of_local_cubic (Y : Subgroup G) (hY : Nat.card Y = 3)
    (hYH : Y ≤ involutionCentralizer D.z) (s : normalizer (Y : Set G)) :
    ∃ m : M D, orderOf m = orderOf s := by
  obtain ⟨g, hg⟩ := D.conjugate_of_le_centralizer Y hY hYH
  let a : G ≃* G := MulAut.conj (g : G)
  have hXY : D.X.map a.toMonoidHom = Y := hg
  have hs : a.symm (s : G) ∈ M D := by
    have hm : (s : G) ∈ (normalizer (D.X : Set G)).map a.toMonoidHom := by
      rw [map_equiv_normalizer_eq, hXY]
      exact s.property
    rwa [mem_map_equiv] at hm
  refine ⟨⟨a.symm s, hs⟩, ?_⟩
  rw [← orderOf_coe, a.symm.orderOf_eq, orderOf_coe]

/-- The remaining finite core-action fact gives an actual order-eight actor.
The source application supplies the embedding and self-centralization; the
finite norm-four premise remains a separate mathematical obligation. -/
theorem eight_of_core_norm
    (f : alternatingGroup (Fin 5) →* involutionCentralizer D.z)
    (hf : Function.Injective f)
    (hcentral : centralizer (localCore D.z : Set (involutionCentralizer D.z)) ≤
      localCore D.z)
    (hnorm : ∀ φ : alternatingGroup (Fin 5) →* MulAut MinusExtraspecial.Model,
      Function.Injective φ → ∀ x r : alternatingGroup (Fin 5),
      orderOf x = 3 → orderOf r = 2 → r * x * r⁻¹ = x⁻¹ →
      ∃ q : MinusExtraspecial.Model,
        φ x q = q ∧ orderOf (q * φ r q) = 4) :
    ∃ s : M D, orderOf s = 8 := by
  let e := D.localType.core_equiv.some
  let ψ : alternatingGroup (Fin 5) →* MulAut (localCore D.z) :=
    (MulAut.conjNormal : involutionCentralizer D.z →* MulAut (localCore D.z)).comp f
  let φ : alternatingGroup (Fin 5) →* MulAut MinusExtraspecial.Model :=
    (MulAut.congr e).toMonoidHom.comp ψ
  have hφ : Function.Injective φ :=
    (MulAut.congr e).injective.comp (coreAction_injective D f hf hcentral)
  obtain ⟨q, hq, hn⟩ := hnorm φ hφ cubicCycle cubicFlip
    cubicCycle_order cubicFlip_order cubicFlip_inverts
  let v : localCore D.z := e.symm q
  have hfix : ψ cubicCycle v = v := by
    apply e.injective
    exact hq.trans (e.apply_symm_apply q).symm
  have hnormQ : orderOf (v * ψ cubicFlip v) = 4 := by
    rw [← e.orderOf_eq, map_mul]
    change orderOf (e (e.symm q) * φ cubicFlip q) = 4
    simpa only [e.apply_symm_apply] using hn
  let s : involutionCentralizer D.z := v.val * f cubicFlip
  have hr : f cubicFlip * f cubicFlip = 1 := by
    have hp := pow_orderOf_eq_one (f cubicFlip)
    rw [orderOf_injective f hf, cubicFlip_order, pow_two] at hp
    exact hp
  have hsquare : s ^ 2 = (v * ψ cubicFlip v).val := by
    change (v.val * f cubicFlip) ^ 2 =
      v.val * (f cubicFlip * v.val * (f cubicFlip)⁻¹)
    have hi := inv_eq_of_mul_eq_one_left hr
    rw [hi, pow_two]
    simp only [mul_assoc]
  have hs8 : orderOf s = 8 := by
    apply order_eight_of_square
    rw [hsquare, orderOf_coe]
    exact hnormQ
  let k := (involutionCentralizer D.z).subtype
  let Y := zpowers (k (f cubicCycle))
  have hY : Nat.card Y = 3 := by
    rw [Nat.card_zpowers, orderOf_injective k (involutionCentralizer D.z).subtype_injective,
      orderOf_injective f hf, cubicCycle_order]
  have hYH : Y ≤ involutionCentralizer D.z :=
    zpowers_le.mpr (f cubicCycle).property
  have hv : k v.val ∈ normalizer (Y : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (zpowers (k (f cubicCycle))).map _ = _
    rw [MonoidHom.map_zpowers]
    have hcomm : v.val * f cubicCycle = f cubicCycle * v.val := by
      have he := congrArg Subtype.val hfix
      change f cubicCycle * v.val * (f cubicCycle)⁻¹ = v.val at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he : k v.val * k (f cubicCycle) * (k v.val)⁻¹ = k (f cubicCycle) := by
      rw [← map_inv, ← map_mul, ← map_mul, hcomm, mul_inv_cancel_right]
    change zpowers (k v.val * k (f cubicCycle) * (k v.val)⁻¹) = Y
    rw [he]
  have hrN : k (f cubicFlip) ∈ normalizer (Y : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (zpowers (k (f cubicCycle))).map _ = _
    rw [MonoidHom.map_zpowers]
    have he := congrArg (k.comp f) cubicFlip_inverts
    simp only [map_mul, map_inv, MonoidHom.comp_apply] at he
    change zpowers (k (f cubicFlip) * k (f cubicCycle) * (k (f cubicFlip))⁻¹) = Y
    rw [he, zpowers_inv]
  have hsN : k s ∈ normalizer (Y : Set G) := by
    change k (v.val * f cubicFlip) ∈ _
    rw [map_mul]
    exact mul_mem hv hrN
  obtain ⟨m, hm⟩ := normalizer_actor_of_local_cubic D Y hY hYH ⟨k s, hsN⟩
  refine ⟨m, hm.trans ?_⟩
  rw [← orderOf_coe, orderOf_injective k (involutionCentralizer D.z).subtype_injective, hs8]

end CFSG.Quasithin.Janko23.J2Recognition.SourceLocal.PrimeNormalizers.ThreeLocal
