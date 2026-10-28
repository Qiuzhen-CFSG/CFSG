module

public import Theory.LinearAlgebra.RegularLinearAction
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Index
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Pointwise stabilizers in a binary four-space

Extending isomorphisms between spans shows that GL(V) is transitive on
independent frames. Orbit–stabilizer then counts each pointwise stabilizer.
For a four-space, subspaces of dimensions zero, one and two have pointwise
stabilizers of orders 20160, 1344 and 96. A subgroup of order 2520 has index
eight; the intersection index bound and Lagrange's theorem force three to
divide its intersection with each of these stabilizers.

Separately, an automorphism fixing a subspace of codimension at most one
has trivial quotient action over F₂. Its displacement lies in its fixed
space, so its square is the identity.

These intrinsic linear-algebra facts supply the four-dimensional A₇ case
of the module comparison in Aschbacher–Smith, B.4.2(7), B.5.1 and 15.4.18,
printed pp.86,99,1163. No identification of representations is used.
-/

@[expose] public section
namespace BinaryFourFixedSpace

open Module Subgroup
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem frame_transitive {k : ℕ} (b c : Fin k → V) (hb : LinearIndependent (ZMod 2) b)
    (hc : LinearIndependent (ZMod 2) c) : ∃ g : V ≃ₗ[ZMod 2] V, ∀ i, g (b i) = c i := by
  let f := hb.linearCombinationEquiv.symm ≪≫ₗ hc.linearCombinationEquiv
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq f
  refine ⟨g, fun i => ?_⟩
  have h := hg (hb.linearCombinationEquiv (Finsupp.single i 1))
  simpa [f] using h.symm

/-- The automorphism group of any four-dimensional binary space has order 20160. -/
theorem card_GL_four (hdim : finrank (ZMod 2) V = 4) : Nat.card (V ≃ₗ[ZMod 2] V) = 20160 := by
  let b : Basis (Fin 4) (ZMod 2) V := (finBasis (ZMod 2) V).reindex (finCongr hdim)
  let e := (Matrix.GeneralLinearGroup.toLin' b).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  rw [← Nat.card_congr e.toEquiv, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ]


/-- Linear automorphisms fixing every vector of the marked subspace. -/
def pointwiseFixer (W : Submodule (ZMod 2) V) : Subgroup (V ≃ₗ[ZMod 2] V) where
  carrier := {g | ∀ w ∈ W, g w = w}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh w hw
    change g (h w) = w
    rw [hh w hw, hg w hw]
  inv_mem' := by
    intro g hg w hw
    apply g.injective
    simpa using (hg w hw).symm

/-- Count independent frames to compute the pointwise stabilizer index. -/
theorem index_pointwiseFixer (W : Submodule (ZMod 2) V) :
    (pointwiseFixer W).index =
      ∏ i : Fin (finrank (ZMod 2) W), (2 ^ finrank (ZMod 2) V - 2 ^ i.val) := by
  classical
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let b := finBasis (ZMod 2) W
  let v : Fin (finrank (ZMod 2) W) → V := fun i => b i
  have hv : LinearIndependent (ZMod 2) v :=
    b.linearIndependent.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hstab : pointwiseFixer W = MulAction.stabilizer (V ≃ₗ[ZMod 2] V) v := by
    ext g
    change (∀ w ∈ W, g w = w) ↔ g • v = v
    constructor
    · intro h
      funext i
      exact h (v i) (b i).property
    · intro h w hw
      have he : g.toLinearMap.comp W.subtype = W.subtype := by
        apply b.ext
        intro i
        exact congrFun h i
      exact LinearMap.congr_fun he ⟨w, hw⟩
  have horbit : MulAction.orbit (V ≃ₗ[ZMod 2] V) v =
      {c | LinearIndependent (ZMod 2) c} := by
    ext c
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact hv.map' g.toLinearMap g.ker
    · intro hc
      obtain ⟨g, hg⟩ := frame_transitive v c hv hc
      exact ⟨g, funext hg⟩
  rw [hstab, MulAction.index_stabilizer, horbit, ← Nat.card_coe_set_eq]
  change Nat.card {c : Fin (finrank (ZMod 2) W) → V // LinearIndependent (ZMod 2) c} = _
  convert card_linearIndependent (K := ZMod 2) (V := V) (Submodule.finrank_le W) using 1
  simp

/-- Fixing a subspace of codimension at most one forces square one over F₂. -/
theorem pointwiseFixer_sq (W : Submodule (ZMod 2) V)
    (hcodim : finrank (ZMod 2) (V ⧸ W) ≤ 1) (g : pointwiseFixer W) : g ^ 2 = 1 := by
  have hmap : W.map g.val.toLinearMap = W := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      change g.val w ∈ W
      rw [g.property w hw]
      exact hw
    · intro w hw
      exact ⟨w, hw, g.property w hw⟩
  have hquot := LinearGroup.eq_one_of_binary_finrank_le_one hcodim
    (Submodule.Quotient.equiv W W g.val hmap)
  have hdisp (v : V) : g.val v - v ∈ W := by
    apply (Submodule.Quotient.eq W).mp
    exact LinearEquiv.congr_fun hquot (W.mkQ v)
  apply Subtype.ext
  ext v
  have h := g.property (g.val v - v) (hdisp v)
  change g.val (g.val v - v) = g.val v - v at h
  change g.val (g.val v) = v
  have hn (w : V) : -w = w := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul]
      using (add_smul (1 : ZMod 2) 1 w).symm
  rw [map_sub] at h
  simp only [sub_eq_add_neg, hn] at h
  exact add_right_cancel (h.trans (add_comm _ _))


/-- A subgroup of order 2520 meets every pointwise stabilizer of a subspace
of dimension at most two in a subgroup of order divisible by three. -/
theorem three_dvd_intersection (hdim : finrank (ZMod 2) V = 4)
    (H : Subgroup (V ≃ₗ[ZMod 2] V)) (hH : Nat.card H = 2520)
    (W : Submodule (ZMod 2) V) (hW : finrank (ZMod 2) W ≤ 2) :
    3 ∣ Nat.card (H ⊓ pointwiseFixer W : Subgroup (V ≃ₗ[ZMod 2] V)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  have hG := card_GL_four hdim
  have hHidx : H.index = 8 := by
    have := H.card_mul_index
    rw [hH, hG] at this
    omega
  let K := pointwiseFixer W
  let I := H ⊓ K
  have hidx : I.index ≤ 8 * K.index := by
    simpa only [hHidx] using (Subgroup.index_inf_le (H := H) (K := K))
  have hKprod : K.index * Nat.card K = 20160 := K.index_mul_card.trans hG
  have hIprod : I.index * Nat.card I = 20160 := I.index_mul_card.trans hG
  have hdvd : Nat.card I ∣ Nat.gcd 2520 (Nat.card K) := by
    rw [← hH]
    exact Nat.dvd_gcd (card_dvd_of_le inf_le_left) (card_dvd_of_le inf_le_right)
  have hKidx := index_pointwiseFixer W
  change K.index = _ at hKidx
  rw [hdim] at hKidx
  by_contra hthree
  have hcop : Nat.Coprime (Nat.card I) 3 :=
    ((by decide : Nat.Prime 3).coprime_iff_not_dvd.mpr hthree).symm
  generalize hn : finrank (ZMod 2) W = n at hW hKidx
  interval_cases n
  · have hKidx' : K.index = 1 := by simpa [Fin.prod_univ_succ] using hKidx
    rw [hKidx'] at hKprod hidx
    have hKcard : Nat.card K = 20160 := by omega
    rw [hKcard] at hdvd
    norm_num at hdvd
    have hsmall : Nat.card I ∣ 280 := (hcop.pow_right 2).dvd_of_dvd_mul_left hdvd
    have hle := Nat.le_of_dvd (by decide : 0 < 280) hsmall
    nlinarith
  · have hKidx' : K.index = 15 := by simpa [Fin.prod_univ_succ] using hKidx
    rw [hKidx'] at hKprod hidx
    have hKcard : Nat.card K = 1344 := by omega
    rw [hKcard] at hdvd
    norm_num at hdvd
    have hsmall : Nat.card I ∣ 56 := hcop.dvd_of_dvd_mul_left hdvd
    have hle := Nat.le_of_dvd (by decide : 0 < 56) hsmall
    nlinarith
  · have hKidx' : K.index = 210 := by simpa [Fin.prod_univ_succ] using hKidx
    rw [hKidx'] at hKprod hidx
    have hKcard : Nat.card K = 96 := by omega
    rw [hKcard] at hdvd
    norm_num at hdvd
    have hsmall : Nat.card I ∣ 8 := hcop.dvd_of_dvd_mul_left hdvd
    have hle := Nat.le_of_dvd (by decide : 0 < 8) hsmall
    nlinarith


end BinaryFourFixedSpace
