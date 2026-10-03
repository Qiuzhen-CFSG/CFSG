module
public import Theory.GroupAction.FiveFourSquareFixed
public import Theory.GroupAction.FiveOnSixteenIrreducible
public import Theory.GroupAction.FivePointOrderFour

/-!
# Five-point orbits in an invariant binary hyperplane

For a faithful five-four action on elementary sixteen, an invariant hyperplane
contains only one point from the five-point orbit, provided it contains the
nonidentity fixed point of the order-four actor. The actor cycles the other
four points. A second point would therefore put the entire orbit in the
hyperplane, although its closure is the whole group by the irreducible
five-action. Fixed-point counting also identifies every orbit of size five
with this orbit.

Source: the quotient action in D. Parrott, *A characterization of the Tits'
simple group* (1972), pp.674 and 677.
-/

open Subgroup MulAction
namespace Theory.GroupAction

private theorem orbit_generates
    {M V : Type*} [Group M] [Group V] [Finite V] [MulDistribMulAction M V]
    (hV : Nat.card V = 16)
    (i : Multiplicative (ZMod 5) →* M)
    (hfree : letI := MulDistribMulAction.compHom V i
      FixedPoints.subgroup (Multiplicative (ZMod 5)) V = ⊥)
    (x : V) (hx : x ≠ 1) : closure (orbit M x) = ⊤ := by
  let A := Multiplicative (ZMod 5)
  let : MulDistribMulAction A V := MulDistribMulAction.compHom V i
  let S := closure (orbit M x)
  have hstable (a : A) (v : V) (hv : v ∈ S) : a • v ∈ S := by
    refine closure_induction (p := fun v _ => a • v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨g, rfl⟩
      exact subset_closure ⟨i a * g, mul_smul (i a) g x⟩
    · simpa only [smul_one] using S.one_mem
    · intro u v _ _ hu hv
      simpa only [smul_mul'] using S.mul_mem hu hv
    · intro u _ hu
      simpa only [smul_inv'] using S.inv_mem hu
  let : IsInvariant A V S := ⟨fun a v => ⟨hstable a v, fun hv => by
    simpa only [inv_smul_smul] using hstable a⁻¹ (a • v) hv⟩⟩
  rcases invariant_eq_bot_or_top_of_five_actor (by simp) hV hfree S with hb | ht
  · exact (hx (hb.le (subset_closure (mem_orbit_self x)))).elim
  · exact ht

/-- In a faithful five-four action on elementary sixteen, an invariant
hyperplane meets the orbit of a supplied nonidentity fixed point only there. -/
public theorem five_four_invariant_hyperplane_orbit_intersection
    {V : Type*} [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 16)
    (φ : Multiplicative (ZMod 4) →* MulAut (Multiplicative (ZMod 5)))
    (hφ : Function.Injective φ)
    (f : (Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) →* MulAut V)
    (hf : Function.Injective f)
    (g : Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)) (hg : orderOf g = 4)
    (U : Subgroup V) (hU : Nat.card U = 8)
    (hstable : ∀ v ∈ U, f g v ∈ U)
    (r : V) (hr : r ≠ 1) (hrU : r ∈ U) (hrfix : f g r = r)
    (hO : (Set.range (fun k => f k r)).ncard = 5)
    (w : V) (hwU : w ∈ U) (hw : w ≠ 1)
    (hw5 : (Set.range (fun k => f k w)).ncard = 5) : w = r := by
  classical
  let M := Multiplicative (ZMod 5) ⋊[φ] Multiplicative (ZMod 4)
  let : Finite M := Finite.of_equiv
    (Multiplicative (ZMod 5) × Multiplicative (ZMod 4)) SemidirectProduct.equivProd.symm
  let : MulDistribMulAction M V := MulDistribMulAction.compHom V f
  let P := zpowers g
  let : MulAction P (orbit M w) := MulAction.compHom (orbit M w) P.subtype
  have hp : IsPGroup 2 P := IsPGroup.of_card (n := 2) (by
    rw [Nat.card_zpowers, hg]; decide)
  have hmod := hp.card_modEq_card_fixedPoints (orbit M w)
  have hnonempty : (fixedPoints P (orbit M w)).Nonempty := by
    by_contra hn
    have he : fixedPoints P (orbit M w) = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    have hz : Nat.card (fixedPoints P (orbit M w)) = 0 := by
      rw [he]; exact Nat.card_of_isEmpty
    change Nat.ModEq 2 ((orbit M w).ncard) _ at hmod
    have hw5' : (orbit M w).ncard = 5 := hw5
    norm_num [hw5', hz, Nat.ModEq] at hmod
  obtain ⟨v, hv⟩ := hnonempty
  let F := FixedPoints.subgroup (zpowers (f g)) V
  have hvF : (v : V) ∈ F := (MulAut.mem_fixed_zpowers_iff _ _).mpr
    (congrArg Subtype.val (hv ⟨g, mem_zpowers g⟩))
  have hrF : r ∈ F := (MulAut.mem_fixed_zpowers_iff _ _).mpr hrfix
  have hvne : (v : V) ≠ 1 := by
    obtain ⟨k, hk⟩ := v.property
    intro heq
    exact hw ((f k).injective (hk.trans (heq.trans (map_one (f k)).symm)))
  have hF := (five_four_sixteen_order_four_fixed_cards hV φ hφ f hf g hg).1
  obtain ⟨s, _, hs⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have hvr : (v : V) = r := congrArg Subtype.val
    ((hs ⟨v, hvF⟩ (fun hh => hvne (congrArg Subtype.val hh))).trans
      (hs ⟨r, hrF⟩ (fun hh => hr (congrArg Subtype.val hh))).symm)
  have hrO : r ∈ orbit M w := hvr ▸ v.property
  have hwO : w ∈ Set.range (fun k => f k r) := by
    change w ∈ orbit M r
    rw [orbit_eq_iff.mpr hrO]
    exact mem_orbit_self w
  let O := orbit M r
  have hOc : Nat.card O = 5 := hO
  let p : Equiv.Perm O := MulAction.toPerm g
  have hp4 : p ^ 4 = 1 := by
    change (MulAction.toPermHom M O g) ^ 4 = 1
    have hg4 : g ^ 4 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
    rw [← map_pow, hg4, map_one]
  have hp2 : p ^ 2 ≠ 1 := by
    intro heq
    let F := FixedPoints.subgroup (zpowers ((f g) ^ 2)) V
    have hOF : O ⊆ F := by
      intro v hv
      apply (MulAut.mem_fixed_zpowers_iff _ _).mpr
      have hh := congrArg (fun q : Equiv.Perm O => (q ⟨v, hv⟩ : V)) heq
      exact hh
    have hh := Set.ncard_le_ncard hOF
    have hF := (five_four_sixteen_order_four_fixed_cards hV φ hφ f hf g hg).2
    change Nat.card O ≤ Nat.card F at hh
    rw [hOc, hF] at hh
    omega
  let root : O := ⟨r, mem_orbit_self r⟩
  let left : O := ⟨w, hwO⟩
  have hroot : p root = root := Subtype.ext hrfix
  by_contra hwr
  have hOU : O ⊆ U := by
    intro v hv
    by_cases hvr : v = r
    · exact hvr ▸ hrU
    obtain ⟨n, hn⟩ := Equiv.Perm.exists_pow_apply_eq_of_order_four_card_five
      hOc p hp4 hp2 (left := left) hroot (fun heq => hwr (congrArg Subtype.val heq))
      (show (⟨v, hv⟩ : O) ≠ root from fun heq => hvr (congrArg Subtype.val heq))
    have hpow : ∀ n : ℕ, (f g ^ n) w ∈ U := by
      intro n
      induction n with
      | zero => exact hwU
      | succ n ih =>
        rw [pow_succ']
        exact hstable _ ih
    have hperm : p ^ n.val = MulAction.toPermHom M O (g ^ n.val) :=
      (map_pow (MulAction.toPermHom M O) g n.val).symm
    rw [hperm] at hn
    have heq : f (g ^ n.val) w = v := congrArg Subtype.val hn
    rw [map_pow] at heq
    exact heq ▸ hpow n.val
  let i : Multiplicative (ZMod 5) →* M := SemidirectProduct.inl
  have hfree : letI := MulDistribMulAction.compHom V i
      FixedPoints.subgroup (Multiplicative (ZMod 5)) V = ⊥ := by
    let : MulDistribMulAction (Multiplicative (ZMod 5)) V := MulDistribMulAction.compHom V i
    apply fixed_eq_bot_of_five_action_card_sixteen (by simp) hV
    intro ht
    have hall (c : Multiplicative (ZMod 5)) : f (i c) = 1 := by
      ext v
      have hv : v ∈ FixedPoints.subgroup (Multiplicative (ZMod 5)) V := by rw [ht]; trivial
      exact hv c
    have hbad : (Multiplicative.ofAdd (1 : ZMod 5)) = (1 : Multiplicative (ZMod 5)) := by
      apply SemidirectProduct.inl_injective (φ := φ)
      apply hf
      exact (hall _).trans (map_one f).symm
    exact (by decide : Multiplicative.ofAdd (1 : ZMod 5) ≠ (1 : Multiplicative (ZMod 5))) hbad
  have hgen := orbit_generates hV i hfree r hr
  have htop : U = ⊤ := top_unique (hgen ▸ (closure_le _).mpr hOU)
  have hh : Nat.card U = Nat.card V := by rw [htop, card_top]
  omega
end Theory.GroupAction
