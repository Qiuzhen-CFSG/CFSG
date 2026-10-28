module
public import Theory.SpecificGroups.GL2.PrimeThreeFiveResidual.Coordinates
public import Theory.SpecificGroups.GL2.ThreeConjugacy
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# A commuting inverter lifted inside the original cubic residual

For a two-perfect group with cubic two-core quotient, a nontrivial core
image on the ternary plane gives the full special linear image. Its scalar
involution lifts to the centralizer of an actual cubic element, since the
action kernel is a two-group. No order is required of the lifted inverter.

Source: Aschbacher--Smith 15.4.10, third paragraph, printed p.1159.
-/

public section
open Subgroup Matrix
namespace Matrix.GeneralLinearGroup.PrimeThreeFiveResidual

private theorem central_lift {X D : Type*} [Group X] [Finite X] [Group D]
    (f : X →* D) (hk : IsPGroup 2 f.ker) (x : X) (hx : orderOf x = 3)
    (d : D) (hd : d ∈ f.range) (hc : ∀ y, y * d = d * y) :
    ∃ t : X, t * x = x * t ∧ f t = d := by
  let K := f.ker
  let q := QuotientGroup.mk' K
  let e := QuotientGroup.quotientKerEquivRange f
  let v := e.symm ⟨d, hd⟩
  have hv : v ∈ centralizer (Set.univ : Set (X ⧸ K)) := by
    intro w _
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul, v, MulEquiv.apply_symm_apply, Subgroup.coe_mul] using hc (e w : D)
  let : Fact (IsPGroup 3 (zpowers x)) := ⟨IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers, hx, pow_one])⟩
  obtain ⟨n, hn⟩ := hk.exists_card_eq
  have hcop : Nat.Coprime 3 (Nat.card K) := by
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hv' : v ∈ (centralizer (zpowers x : Set X)).map q := by
    rw [← centralizer_map_quotient_eq_map_centralizer 3 (zpowers x) K inferInstance hcop]
    exact fun w _ => hv w (Set.mem_univ w)
  obtain ⟨t, ht, htv⟩ := hv'
  refine ⟨t, (ht x (mem_zpowers x)).symm, ?_⟩
  have he := congrArg (fun w => (e w : D)) htv
  have hem : (e (q t) : D) = f t := rfl
  rw [hem] at he
  simpa only [v, MulEquiv.apply_symm_apply] using he

private theorem scalar_commutes (y : GL (Fin 2) (ZMod 3)) :
    y * threeCentral = threeCentral * y := by
  apply Units.ext
  change y.val * threeCentral.val = threeCentral.val * y.val
  have ht : threeCentral.val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by decide
  rw [ht, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_one, Matrix.one_mul]

private theorem scalar_inverts (v : Multiplicative (Fin 2 → ZMod 3)) :
    planeAction 3 threeCentral v = v⁻¹ := by
  change Multiplicative.ofAdd (threeCentral.val *ᵥ v.toAdd) = _
  have ht : threeCentral.val = -(1 : Matrix (Fin 2) (Fin 2) (ZMod 3)) := by decide
  rw [ht, Matrix.neg_mulVec, Matrix.one_mulVec]
  rfl

/-- The actual cubic actor and a commuting inverter in the original group. -/
theorem exists_commuting_inverter
    {X V : Type*} [Group X] [Finite X] [Group V] [Finite V]
    [IsElementaryAbelian 3 V] (hV : Nat.card V = 9)
    (hX : IsPPerfect 2 X) (hX3 : Nat.card (X ⧸ pCore 2 X) = 3)
    (a : X →* MulAut V) (hne : (pCore 2 X).map a ≠ ⊥) :
    ∃ x t : X, orderOf x = 3 ∧ a x ≠ 1 ∧ t * x = x * t ∧
      ∀ v : V, a t v = v⁻¹ := by
  obtain ⟨c, e, he⟩ := exists_plane_coordinates (p := 3) hV
  let f := e.toMonoidHom.comp a
  have hf : (pCore 2 X).map f ≠ ⊥ := by
    intro hb
    apply hne
    apply eq_bot_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    apply e.injective
    simpa only [map_one] using mem_bot.mp (hb ▸ mem_map_of_mem f hx)
  have hkne : f.ker ≠ ⊤ := fun h => hf ((Subgroup.map_eq_bot_iff _).mpr (h ▸ le_top))
  have hk : f.ker ≤ pCore 2 X := normal_le_pCore_of_pPerfect_prime_quotient hX
    (by rw [hX3]; exact Nat.prime_three) f.ker hkne
  have hk2 : IsPGroup 2 f.ker := pCore_isPGroup.of_injective
    (inclusion hk) (inclusion_injective hk)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3
    (hX3 ▸ card_quotient_dvd_card (pCore 2 X))
  have hfx : orderOf (f x) = 3 :=
    (f.orderOf_map_eq_of_coprime_of_isPGroup_ker hk2 x (by rw [hx]; decide)).trans hx
  have hd : threeCentral ∈ f.range := by
    rw [ternary_range_eq hX f hf, three_mem_specialLinear]
    decide
  obtain ⟨t, htx, ht⟩ := central_lift f hk2 x hx threeCentral hd scalar_commutes
  refine ⟨x, t, hx, ?_, htx, ?_⟩
  · intro h
    have hh : f x = 1 := by change e (a x) = 1; rw [h, map_one]
    rw [hh, orderOf_one] at hfx
    omega
  · intro v
    apply c.injective
    rw [← he]
    change planeAction 3 (f t) (c v) = _
    rw [ht, scalar_inverts, map_inv]

end Matrix.GeneralLinearGroup.PrimeThreeFiveResidual
