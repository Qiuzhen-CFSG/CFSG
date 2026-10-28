module

public import Theory.Representation.AbelianWeightAutomizer
public import Theory.Representation.GeneralLinearNatural
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The order-five normalizer obstruction in degree three

An element of order five cannot be conjugate to its square in a faithful
representation of dimension at most three in characteristic different from
five. Indeed its cyclic subgroup has at most three character weights over
the algebraic closure, and its automizer acts faithfully on those weights.
Every permutation of three letters has sixth power one, whereas six
iterations of squaring on a group of order five are nontrivial.

The matrix version extends scalars entrywise, preserving faithfulness.
Together with coprime lifting through scalar kernels, this excludes A₇ and
its central three-cover from the degree-three binary projective groups.

Source application: Aschbacher–Smith, combined manuscript (1 March 2004),
the Theorem C inspection in E.6.18, printed p.252. The weight argument is
the elementary abelian-automizer argument of A.3.21(c), pp.55–56.
-/

public section

open Subgroup
namespace Representation.FiveCycleDegreeThree

private theorem normalizes {G : Type*} [Group G] (x y : G) (hx : orderOf x = 5)
    (hxy : y * x * y⁻¹ = x ^ 2) :
    y ∈ normalizer (zpowers x : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [MonoidHom.map_zpowers]
  change zpowers (y * x * y⁻¹) = zpowers x
  rw [hxy]
  apply le_antisymm (zpowers_le.mpr (pow_mem (mem_zpowers x) 2))
  apply zpowers_le.mpr
  have he : (x ^ 2) ^ 3 = x := by
    rw [← pow_mul, ← pow_mod_orderOf, hx]
    norm_num
  have hm := pow_mem (mem_zpowers (x ^ 2)) 3
  rwa [he] at hm

/-- The cyclic five-subgroup's automizer cannot act faithfully on at most
three occurring weights if it contains the squaring automorphism. -/
theorem not_conjugate_square
    {E G V : Type*} [Field E] [IsAlgClosed E] [Group G]
    [AddCommGroup V] [Module E V] [FiniteDimensional E V]
    (rho : Representation E G V) (hrho : Function.Injective rho)
    (hfive : (5 : E) ≠ 0) (hdim : Module.finrank E V ≤ 3)
    (x y : G) (hx : orderOf x = 5) : y * x * y⁻¹ ≠ x ^ 2 := by
  intro hxy
  let Q := zpowers x
  obtain ⟨j, hj⟩ := automizer_embeds_perm_of_abelian rho Q hrho
    (by simpa [Q, Nat.card_zpowers, hx] using hfive) 3 hdim
  have hy := normalizes x y hx hxy
  let a : Q.normalizerMonoidHom.range :=
    ⟨Q.normalizerMonoidHom ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩⟩
  have ha6 : a ^ 6 = 1 := by
    apply hj
    rw [map_pow, map_one]
    simpa only [Fintype.card_perm, Fintype.card_fin, Nat.factorial] using
      (pow_card_eq_one (x := j a))
  let u : Q := ⟨x, mem_zpowers x⟩
  have hau : a.val u = u ^ 2 := Subtype.ext hxy
  have hn (n : ℕ) : (a.val ^ n) u = u ^ (2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_pow, hau, ← pow_mul, pow_succ']
  have ha : a.val ^ 6 = 1 := congrArg Subtype.val ha6
  have h64 : x ^ 64 = x := by
    have he := hn 6
    rw [ha] at he
    exact (congrArg Subtype.val he).symm
  have h63 : x ^ 63 = 1 := by
    apply mul_right_cancel (b := x)
    simpa only [← pow_succ, one_mul] using h64
  have := orderOf_dvd_of_pow_eq_one h63
  rw [hx] at this
  norm_num at this

/-- The obstruction for a faithful matrix representation over the original
field; no splitting-field or finiteness hypothesis is necessary. -/
theorem not_conjugate_square_of_matrix
    {F G : Type*} [Field F] [Group G]
    (rho : G →* GL (Fin 3) F) (hrho : Function.Injective rho)
    (hfive : (5 : F) ≠ 0) (x y : G) (hx : orderOf x = 5) :
    y * x * y⁻¹ ≠ x ^ 2 := by
  let E := AlgebraicClosure F
  let f : GL (Fin 3) F →* GL (Fin 3) E :=
    Matrix.GeneralLinearGroup.map (algebraMap F E)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    ext i j
    apply (algebraMap F E).injective
    exact congrArg (fun c : GL (Fin 3) E => c i j) h
  let sigma : Representation E G (Fin 3 → E) :=
    (generalLinearNatural 3).comp (f.comp rho)
  have hfaith : Function.Injective sigma :=
    (generalLinearNatural_injective 3).comp (hf.comp hrho)
  have hfive' : (5 : E) ≠ 0 := by
    intro h
    apply hfive
    apply (algebraMap F E).injective
    simpa only [map_ofNat, map_zero] using h
  exact not_conjugate_square sigma hfaith hfive'
    (by simp) x y hx

end Representation.FiveCycleDegreeThree
