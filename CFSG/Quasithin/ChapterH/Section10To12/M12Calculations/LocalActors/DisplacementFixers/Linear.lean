module

public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.Reductions
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Faithful A₅ action on an involution displacement space

In a faithful binary module of dimension ten, let an involution move at least
four dimensions. If a commuting element of order five fixed its displacement,
the five-element's moved space would lie in the involution's fixed space and
be disjoint from the involution's displacement. Their dimensions are each at
least four, whereas that fixed space has dimension at most six. This is
impossible. Simplicity therefore makes every commuting A₅ faithful on the
displacement. If the involution centralizer normalizes this A₅, its displacement
kernel centralizes A₅.

This is the action step in Aschbacher–Smith H.11.1(5), printed pp.392–393,
combined manuscript of 1 March 2004. The argument uses the elementary
order-five displacement bound instead of the source's Thompson A × B argument.
-/

public section

open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem centralizer_stabilizes_displacement (ρ : Representation (ZMod 2) G V) (t : G) :
    centralizer ({t} : Set G) ≤ subspaceStabilizer ρ (LinearMap.range (ρ t - LinearMap.id)) := by
  apply le_subspaceStabilizer
  rintro g hg w ⟨v, rfl⟩
  refine ⟨ρ g v, ?_⟩
  change ρ t (ρ g v) - ρ g v = ρ g (ρ t v - v)
  rw [map_sub, ← Module.End.mul_apply, ← map_mul,
    (mem_centralizer_singleton_iff.mp hg).symm, map_mul, Module.End.mul_apply]

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem five_displacement_disjoint_fixed (ρ : Representation (ZMod 2) G V)
    {x : G} (hx : x ^ 5 = 1) :
    Disjoint (LinearMap.range (ρ x - LinearMap.id)) (fixedSpace ρ (zpowers x)) := by
  apply disjoint_iff.mpr
  apply le_antisymm _ bot_le
  rintro w ⟨⟨v, hv⟩, hw⟩
  have hw := (mem_fixedSpace_zpowers_iff ρ x w).mp hw
  change ρ x v - v = w at hv
  have hpow (n : ℕ) : ρ (x ^ n) v = v + n • w := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', map_mul, Module.End.mul_apply, ih, map_add, map_nsmul, hw,
        succ_nsmul]
      rw [sub_eq_iff_eq_add.mp hv]
      abel
  have he := hpow 5
  rw [hx, map_one, Module.End.one_apply] at he
  have hfive : 5 • w = w := by
    calc
      5 • w = (5 : ZMod 2) • w := (Nat.cast_smul_eq_nsmul (ZMod 2) 5 w).symm
      _ = w := by rw [show (5 : ZMod 2) = 1 by decide, one_smul]
  rw [hfive] at he
  simpa only [Submodule.mem_bot] using (add_left_cancel (he.symm.trans (add_zero v).symm))

private theorem five_not_fixes_displacement (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hV : Module.finrank (ZMod 2) V = 10)
    {t x : G} (ht : orderOf t = 2) (hx : orderOf x = 5)
    (hcomm : x * t = t * x) (hr : 4 ≤ fixedCodim ρ (zpowers t)) :
    ¬ (∀ w ∈ LinearMap.range (ρ t - LinearMap.id), ρ x w = w) := by
  intro hfix
  let U := LinearMap.range (ρ x - LinearMap.id)
  let W := LinearMap.range (ρ t - LinearMap.id)
  let F := fixedSpace ρ (zpowers t)
  have hWF : W ≤ F := by
    rintro w ⟨v, rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    change ρ t (ρ t v - v) = ρ t v - v
    have ht2 : t * t = 1 := by simpa only [← pow_two, ht] using pow_orderOf_eq_one t
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ht2, map_one, Module.End.one_apply]
    have hn (u : V) : -u = u := by
      have hu : u + u = 0 := by
        simpa only [add_smul, one_smul, zero_smul] using
          congrArg (fun c : ZMod 2 => c • u) (by decide : (1 : ZMod 2) + 1 = 0)
      exact neg_eq_of_add_eq_zero_left hu
    simp only [sub_eq_add_neg, hn, add_comm]
  have hUF : U ≤ F := by
    rintro w ⟨v, rfl⟩
    rw [mem_fixedSpace_zpowers_iff]
    have hh := hfix (ρ t v - v) (LinearMap.mem_range_self (ρ t - LinearMap.id) v)
    change ρ x (ρ t v - v) = ρ t v - v at hh
    rw [map_sub] at hh
    change ρ t (ρ x v - v) = ρ x v - v
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, ← hcomm, map_mul, Module.End.mul_apply]
    exact sub_eq_sub_iff_sub_eq_sub.mp hh
  have hd : Disjoint U W :=
    (five_displacement_disjoint_fixed ρ (hx ▸ pow_orderOf_eq_one x)).mono_right
      (fun w hw => (mem_fixedSpace_zpowers_iff ρ x w).mpr (hfix w hw))
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq U W
  rw [hd.eq_bot, finrank_bot, add_zero] at hsum
  have hle := Submodule.finrank_mono (sup_le hUF hWF)
  have hU : 4 ≤ Module.finrank (ZMod 2) U := by
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five, fixedCodim_zpowers_eq_displacement_rank]
      using prime_order_le_fixedCodim ρ hρ (by decide : Nat.Prime 5) (by decide) x hx
  have hW : 4 ≤ Module.finrank (ZMod 2) W := by
    simpa only [fixedCodim_zpowers_eq_displacement_rank] using hr
  have hF := fixedCodim_add_finrank ρ (zpowers t)
  rw [hV] at hF
  change fixedCodim ρ (zpowers t) + Module.finrank (ZMod 2) F = 10 at hF
  omega


theorem a5_faithful_on_displacement (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hV : Module.finrank (ZMod 2) V = 10)
    {t : G} (ht : orderOf t = 2) (hr : 4 ≤ fixedCodim ρ (zpowers t))
    (E : Subgroup G) (e : E ≃* alternatingGroup (Fin 5))
    (hEC : E ≤ centralizer ({t} : Set G))
    {x : G} (hxE : x ∈ E)
    (hx : ∀ w ∈ LinearMap.range (ρ t - LinearMap.id), ρ x w = w) : x = 1 := by
  let W := LinearMap.range (ρ t - LinearMap.id)
  let K := (subspaceKernel ρ W E).subgroupOf E
  let : IsSimpleGroup E := e.isSimpleGroup
  have hN : K.Normal := subspaceKernel_normal ρ W E
    (hEC.trans (centralizer_stabilizes_displacement ρ t))
  rcases hN.eq_bot_or_eq_top with hb | ha
  · have hmem : (⟨x, hxE⟩ : E) ∈ K := ⟨hxE, hx⟩
    rw [hb] at hmem
    exact congrArg Subtype.val (mem_bot.mp hmem)
  · have hcard : Nat.card E = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hdiv : 5 ∣ Nat.card E := by rw [hcard]; decide
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨a, ha5⟩ := exists_prime_orderOf_dvd_card' (G := E) 5 hdiv
    have haK : a ∈ K := ha ▸ mem_top a
    exact (five_not_fixes_displacement ρ hρ hV ht
      ((orderOf_injective E.subtype E.subtype_injective a).trans ha5)
      (mem_centralizer_singleton_iff.mp (hEC a.property)) hr haK.2).elim

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
theorem fixer_centralizes_of_faithful (ρ : Representation (ZMod 2) G V)
    (t : G) (E : Subgroup G)
    (hEC : E ≤ centralizer ({t} : Set G))
    (hEN : centralizer ({t} : Set G) ≤ normalizer (E : Set G))
    (hfaith : ∀ x ∈ E,
      (∀ w ∈ LinearMap.range (ρ t - LinearMap.id), ρ x w = w) → x = 1) :
    involutionDisplacementFixer ρ t ≤ centralizer (E : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro x hx
  have hconj : g * x * g⁻¹ * x⁻¹ ∈ E := E.mul_mem
    ((mem_normalizer_iff.mp (hEN hg.1) x).mp hx) (E.inv_mem hx)
  have heq : g * x * g⁻¹ * x⁻¹ = 1 := by
    apply hfaith _ hconj
    intro w hw
    have hxw := (centralizer_stabilizes_displacement ρ t (hEC (E.inv_mem hx)) w).mpr hw
    have hgi : g⁻¹ ∈ involutionDisplacementFixer ρ t :=
      (involutionDisplacementFixer ρ t).inv_mem hg
    simp only [map_mul, Module.End.mul_apply]
    rw [hgi.2 _ hxw]
    have hxx : ρ x (ρ x⁻¹ w) = w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [hxx, hg.2 w hw]
  exact (commutatorElement_eq_one_iff_mul_comm.mp heq).symm

end CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.LocalActors.DisplacementFixers
