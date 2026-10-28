module

public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility

/-!
# An order-five test for an involution's moved module

An involution in an eight-dimensional binary space moves at most four
dimensions. A commuting order-five actor has displacement divisible by four
on every invariant subspace. If it fixed the involution's entire moved
space, averaging over its five powers would produce every moved vector
from its fixed space. Square-zero displacement then bounds twice the moved
dimension by that fixed dimension. When the actor moves at least four
dimensions, this contradicts moved rank greater than two.

Thus the actor is fixed-point-free on the moved four-space. The same
divisibility argument excludes every proper nonzero invariant subspace.
This proof uses the original operators and needs no module recognition.

The matrix application is in the parent `Swapping` module. It supplies the
rank and irreducibility step of Aschbacher–Smith 14.4.9, printed p.1010,
combined manuscript of 1 March 2004.
-/

public section
open Module
namespace ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual.Swapping
variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U]

omit [FiniteDimensional (ZMod 2) U] in
private theorem binary_add_self (v : U) : v + v = 0 := by
  have h := congrArg (fun c : ZMod 2 => c • v) (show (1 : ZMod 2) + 1 = 0 by decide)
  simpa only [add_smul, one_smul, zero_smul] using h

private theorem twice_rank_le (f : U →ₗ[ZMod 2] U) (hf : ∀ v, f (f v) = 0) :
    2 * finrank (ZMod 2) f.range ≤ finrank (ZMod 2) U := by
  have hle : f.range ≤ f.ker := by
    rintro _ ⟨v, rfl⟩
    exact hf v
  have hdim := f.finrank_range_add_finrank_ker
  have hmono := Submodule.finrank_mono hle
  omega

omit [FiniteDimensional (ZMod 2) U] in
private theorem displacement_square_zero (t : U ≃ₗ[ZMod 2] U) (ht : t ^ 2 = 1) :
    ∀ v, (t.toLinearMap - LinearMap.id : U →ₗ[ZMod 2] U)
      ((t.toLinearMap - LinearMap.id : U →ₗ[ZMod 2] U) v) = 0 := by
  intro v
  have htv : t (t v) = v := by
    simpa [pow_two] using
      LinearEquiv.congr_fun ht v
  change t (t v - v) - (t v - v) = 0
  rw [map_sub, htv]
  calc
    (v - t v) - (t v - v) = (v + v) - (t v + t v) := by abel
    _ = 0 := by rw [binary_add_self, binary_add_self, sub_self]

omit [FiniteDimensional (ZMod 2) U] in
/-- Every commuting actor preserves the literal moved subspace. -/
theorem moved_invariant (t s : U ≃ₗ[ZMod 2] U) (h : Commute t s)
    (v : U) (hv : v ∈ LinearMap.range (t.toLinearMap - LinearMap.id)) :
    s v ∈ LinearMap.range (t.toLinearMap - LinearMap.id) := by
  obtain ⟨w, rfl⟩ := hv
  refine ⟨s w, ?_⟩
  have he := LinearEquiv.congr_fun h.eq w
  change t (s w) - s w = s (t w - w)
  rw [map_sub]
  exact congrArg (fun x => x - s w) he

/-- An involution moves at most half the binary space. -/
theorem twice_moved_finrank_le (t : U ≃ₗ[ZMod 2] U) (ht : t ^ 2 = 1) :
    2 * finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤
      finrank (ZMod 2) U :=
  twice_rank_le _ (displacement_square_zero t ht)

private theorem twice_rank_le_fixed (f u : U →ₗ[ZMod 2] U)
    (hf : ∀ v, f (f v) = 0) (hu : u ^ 5 = 1)
    (huf : ∀ v, u (f v) = f v) (hfu : ∀ v, f (u v) = f v) :
    2 * finrank (ZMod 2) f.range ≤
      finrank (ZMod 2) (LinearMap.ker (u - LinearMap.id)) := by
  let K := LinearMap.ker (u - LinearMap.id)
  let q := 1 + u + u ^ 2 + u ^ 3 + u ^ 4
  have huq : u * q = q := by
    dsimp [q]
    calc
      u * (1 + u + u ^ 2 + u ^ 3 + u ^ 4) =
          u + u ^ 2 + u ^ 3 + u ^ 4 + u ^ 5 := by noncomm_ring
      _ = 1 + u + u ^ 2 + u ^ 3 + u ^ 4 := by rw [hu]; abel
  have hq (v : U) : q v ∈ K := by
    change u (q v) - q v = 0
    exact sub_eq_zero.mpr (LinearMap.congr_fun huq v)
  have hfq (v : U) : f (q v) = f v := by
    simp only [q, LinearMap.add_apply, Module.End.one_apply, map_add,
      pow_succ, pow_zero, Module.End.mul_apply, hfu]
    simp only [binary_add_self, zero_add]
  let d : K →ₗ[ZMod 2] f.range := f.rangeRestrict.domRestrict K
  have hsurj : Function.Surjective d := by
    rintro ⟨_, v, rfl⟩
    exact ⟨⟨q v, hq v⟩, Subtype.ext (hfq v)⟩
  let i : f.range →ₗ[ZMod 2] LinearMap.ker d :=
    { toFun := fun w => ⟨⟨w, by
        obtain ⟨v, hv⟩ := w.property
        change u w - w = 0
        rw [← hv, huf, sub_self]⟩, by
          apply Subtype.ext
          obtain ⟨v, hv⟩ := w.property
          change f w = 0
          rw [← hv, hf]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hinj : Function.Injective i := by
    intro x y he
    exact Subtype.ext (congrArg (fun z : LinearMap.ker d => (z.val : U)) he)
  have hdim := d.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hdim
  have hmono := LinearMap.finrank_le_finrank_of_injective hinj
  change 2 * finrank (ZMod 2) f.range ≤ finrank (ZMod 2) K
  omega

variable {H : Type*} [Group H]

/-- A commuting order-five actor with fixed dimension at most four forces
an involution of moved rank greater than two to move an irreducible four-space. -/
theorem moved_four_irreducible_of_order_five
    (ρ : Representation (ZMod 2) H U) (t : U ≃ₗ[ZMod 2] U)
    (ht : t ^ 2 = 1) (hd : finrank (ZMod 2) U = 8)
    (hcomm : ∀ (g : H) (v : U), t (ρ g v) = ρ g (t v))
    (hr : 2 < finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)))
    (x : H) (hx : orderOf x = 5)
    (hgap : 4 ≤ finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id))) :
    finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 4 ∧
      ∀ X : Submodule (ZMod 2) U,
        X ≤ LinearMap.range (t.toLinearMap - LinearMap.id) →
        (∀ (g : H) (v : U), v ∈ X → ρ g v ∈ X) →
        X = ⊥ ∨ X = LinearMap.range (t.toLinearMap - LinearMap.id) := by
  let f := t.toLinearMap - LinearMap.id
  let W := LinearMap.range f
  have hW : ∀ g : H, W ≤ W.comap (ρ g) := by
    intro g _ hv
    obtain ⟨v, rfl⟩ := hv
    refine ⟨ρ g v, ?_⟩
    change t (ρ g v) - ρ g v = ρ g (t v - v)
    rw [map_sub, hcomm]
  let σ := ρ.subrepresentation W hW
  have hbound : finrank (ZMod 2) W ≤ 4 := by
    have h := twice_moved_finrank_le t ht
    rw [hd] at h
    change 2 * finrank (ZMod 2) W ≤ 8 at h
    omega
  have hnonzero : finrank (ZMod 2) (LinearMap.range (σ x - LinearMap.id)) ≠ 0 := by
    intro hz
    have he : σ x = LinearMap.id := sub_eq_zero.mp
      (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz))
    have huf (v : U) : ρ x (f v) = f v :=
      congrArg Subtype.val (LinearMap.congr_fun he ⟨f v, LinearMap.mem_range_self f v⟩)
    have hfu (v : U) : f (ρ x v) = f v := by
      calc
        f (ρ x v) = ρ x (f v) := by
          change t (ρ x v) - ρ x v = ρ x (t v - v)
          rw [hcomm, map_sub]
        _ = f v := huf v
    have hpow : ρ x ^ 5 = 1 := by
      rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
    have hf := twice_rank_le_fixed f (ρ x) (displacement_square_zero t ht) hpow huf hfu
    have hdims := (ρ x - LinearMap.id).finrank_range_add_finrank_ker
    rw [hd] at hdims
    change 2 < finrank (ZMod 2) f.range at hr
    omega
  have hdiv := Representation.BinaryOffender.four_dvd_fixedCodim_of_order_five σ x hx
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank] at hdiv
  have hlo := Nat.le_of_dvd (Nat.pos_of_ne_zero hnonzero) hdiv
  have hle := (LinearMap.range (σ x - LinearMap.id)).finrank_le
  have hrank : finrank (ZMod 2) W = 4 := by omega
  have hker : LinearMap.ker (σ x - LinearMap.id) = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have hdim := (σ x - LinearMap.id).finrank_range_add_finrank_ker
    omega
  have hfixed (v : U) (hv : v ∈ W) (he : ρ x v = v) : v = 0 := by
    have hh : (⟨v, hv⟩ : W) ∈ LinearMap.ker (σ x - LinearMap.id) := by
      apply sub_eq_zero.mpr
      exact Subtype.ext he
    rw [hker] at hh
    exact congrArg Subtype.val hh
  refine ⟨hrank, fun X hX hXinv => ?_⟩
  by_cases hb : X = ⊥
  · exact Or.inl hb
  right
  let τ := ρ.subrepresentation X hXinv
  have hk : LinearMap.ker (τ x - LinearMap.id) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    apply hfixed v (hX v.property)
    exact congrArg Subtype.val (sub_eq_zero.mp hv)
  have hdim := (τ x - LinearMap.id).finrank_range_add_finrank_ker
  rw [hk, finrank_bot, add_zero] at hdim
  have hdivX := Representation.BinaryOffender.four_dvd_fixedCodim_of_order_five τ x hx
  rw [Representation.BinaryOffender.fixedCodim_zpowers_eq_displacement_rank, hdim] at hdivX
  have hpos : 0 < finrank (ZMod 2) X :=
    Nat.pos_of_ne_zero (fun h => hb (Submodule.finrank_eq_zero.mp h))
  have hloX := Nat.le_of_dvd hpos hdivX
  have hleX := Submodule.finrank_mono hX
  change finrank (ZMod 2) X ≤ finrank (ZMod 2) W at hleX
  apply Submodule.eq_of_le_of_finrank_eq hX
  change finrank (ZMod 2) X = finrank (ZMod 2) W
  omega

end ClassicalOrthogonal.FourPlusMatrix.Binary.InvolutionResidual.Swapping
