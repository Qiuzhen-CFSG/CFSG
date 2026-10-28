module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight.Regular.Displacement
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Order-four subgroups of regular elementary eight groups

For a subgroup `B` of order four in a regular elementary eight group, the
points form two regular `B`-orbits. Constant-displacement functions are
parametrized by two orbit constants and one common additive character of `B`.
Since `B` is a binary plane, this gives dimension `2 + 2 = 4`.

Each orbit constant occurs four times in the sum of coordinates, and the
character has the same sum on both orbits. Thus every such function belongs
to the even core. Quotienting by the constant line gives natural fixed
space dimension three, the order-four calculation used in proving bestness
of the regular group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(3),(6), printed pp.83–84.
-/

public section

open BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB.Offenders

/-- The eight points are two disjoint regular four-point orbits. -/
private theorem planes_orbit_coordinates {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 4) :
    ∃ r : Bool → Fin 8, Function.Bijective (fun p : Bool × B => p.2.val (r p.1)) := by
  classical
  have heval (x : Fin 8) : Function.Injective (fun b : B => b.val x) := by
    intro b c h
    change b.val x = c.val x at h
    have hbc : (c⁻¹ * b).val x = x := by
      change c.val.symm (b.val x) = x
      rw [h, Equiv.symm_apply_apply]
    have h1 := regularEight_subgroup_free hA hBA (c⁻¹ * b) x hbc
    exact (inv_mul_eq_one.mp h1).symm
  have hn : ¬ Function.Surjective (fun b : B => b.val 0) := by
    intro hs
    have hc := Nat.card_le_card_of_surjective _ hs
    rw [hB, Nat.card_fin] at hc
    omega
  obtain ⟨y, hy⟩ : ∃ y : Fin 8, ∀ b : B, b.val 0 ≠ y := by
    simpa only [Function.Surjective, not_forall, not_exists] using hn
  let r : Bool → Fin 8 := fun t => if t then y else 0
  refine ⟨r, (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩⟩
  · have hcross (b c : B) : b.val 0 ≠ c.val y := by
      intro h
      apply hy (c⁻¹ * b)
      change c.val.symm (b.val 0) = y
      rw [h, Equiv.symm_apply_apply]
    rintro ⟨t, b⟩ ⟨u, c⟩ h
    cases t <;> cases u
    · exact Prod.ext rfl (heval 0 h)
    · exact (hcross b c h).elim
    · exact (hcross c b h.symm).elim
    · exact Prod.ext rfl (heval y h)
  · rw [Nat.card_prod, hB]
    simp

/-- The two orbit functions have independent constants and a common character. -/
private theorem planes_affine_iff (B : Subgroup (Equiv.Perm (Fin 8)))
    (r : Bool → Fin 8)
    (hr : Function.Bijective (fun p : Bool × B => p.2.val (r p.1)))
    (v : Full (Fin 8)) :
    v ∈ eightDisplacementSpace B ↔
      ∃ χ : Additive B →+ ZMod 2, ∀ t (b : B),
        v (b.val (r t)) = v (r t) + χ (Additive.ofMul b) := by
  rw [mem_eightDisplacementSpace_iff_forward]
  constructor
  · intro hv
    have hd (a : B) (i : Fin 8) :
        v (a.val i) - v i = v (a.val (r false)) - v (r false) := by
      obtain ⟨c, hc⟩ := hv a
      exact (hc i).trans (hc (r false)).symm
    let χ : Additive B →+ ZMod 2 :=
      { toFun := fun a => v (a.toMul.val (r false)) - v (r false)
        map_zero' := by simp
        map_add' := by
          intro a b
          change v (a.toMul.val (b.toMul.val (r false))) - v (r false) =
            (v (a.toMul.val (r false)) - v (r false)) +
              (v (b.toMul.val (r false)) - v (r false))
          have := hd a.toMul (b.toMul.val (r false))
          linear_combination this }
    refine ⟨χ, ?_⟩
    intro t b
    have := hd b (r t)
    change _ = _ + (v (b.val (r false)) - v (r false))
    linear_combination this
  · rintro ⟨χ, hχ⟩ a
    refine ⟨χ (Additive.ofMul a), ?_⟩
    intro i
    obtain ⟨⟨t, b⟩, rfl⟩ := hr.2 i
    have hm := hχ t (a * b)
    change v (a.val (b.val (r t))) = _ at hm
    rw [hm, hχ t b]
    change v (r t) + χ (Additive.ofMul a + Additive.ofMul b) -
      (v (r t) + χ (Additive.ofMul b)) = _
    rw [map_add]
    ring

private theorem planes_finrank (E : Type*) [Group E] [Finite E]
    [IsElementaryAbelian 2 E] (hcard : Nat.card E = 4) :
    Module.finrank (ZMod 2) (Additive E) = 2 := by
  have hpow : 2 ^ Module.finrank (ZMod 2) (Additive E) = 2 ^ 2 := by
    have hsize := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive E)
    change Nat.card E = _ at hsize
    simpa only [Nat.card_zmod, hcard, show (2 : ℕ) ^ 2 = 4 by decide] using hsize.symm
  exact Nat.pow_right_injective (by decide : 1 < 2) hpow

/-- Two orbit constants and a binary-plane character give four parameters. -/
theorem regularEight_four_displacement_finrank {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 4) :
    Module.finrank (ZMod 2) (eightDisplacementSpace B) = 4 := by
  classical
  let : IsElementaryAbelian 2 A := hA.1.2
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.of_le hBA
  obtain ⟨r, hr⟩ := planes_orbit_coordinates hA hBA hB
  let e : Bool × B ≃ Fin 8 := Equiv.ofBijective _ hr
  have he (t : Bool) (b : B) : e.symm (b.val (r t)) = (t, b) :=
    e.symm_apply_apply (t, b)
  have her (t : Bool) : e.symm (r t) = (t, 1) := he t 1
  let f₀ : ((Bool → ZMod 2) × Module.Dual (ZMod 2) (Additive B)) →ₗ[ZMod 2]
      Full (Fin 8) :=
    { toFun := fun p i => p.1 (e.symm i).1 + p.2 (Additive.ofMul (e.symm i).2)
      map_add' := by intro p q; ext i; simp; ring
      map_smul' := by intro c p; ext i; simp [mul_add] }
  have hf₀ (p : (Bool → ZMod 2) × Module.Dual (ZMod 2) (Additive B)) :
      f₀ p ∈ eightDisplacementSpace B := by
    apply (planes_affine_iff B r hr (f₀ p)).mpr
    refine ⟨p.2.toAddMonoidHom, ?_⟩
    intro t b
    change p.1 (e.symm (b.val (r t))).1 + p.2 (Additive.ofMul (e.symm (b.val (r t))).2) =
      p.1 (e.symm (r t)).1 + p.2 (Additive.ofMul (e.symm (r t)).2) + p.2 (Additive.ofMul b)
    rw [he, her]
    simp
  let f := f₀.codRestrict (eightDisplacementSpace B) hf₀
  have hinj : Function.Injective f := by
    intro p q hpq
    have hfun : f₀ p = f₀ q := congrArg Subtype.val hpq
    have hconst : p.1 = q.1 := by
      funext t
      have := congrFun hfun (r t)
      simpa [f₀, her] using this
    apply Prod.ext hconst
    ext a
    have := congrFun hfun (a.toMul.val (r false))
    simpa [f₀, he, hconst] using this
  have hsurj : Function.Surjective f := by
    intro v
    obtain ⟨χ, hχ⟩ := (planes_affine_iff B r hr v.val).mp v.property
    let φ : Module.Dual (ZMod 2) (Additive B) :=
      { χ with map_smul' := ZMod.map_smul χ }
    refine ⟨(fun t => v.val (r t), φ), ?_⟩
    apply Subtype.ext
    ext i
    change v.val (r (e.symm i).1) + χ (Additive.ofMul (e.symm i).2) = v.val i
    have hi := hχ (e.symm i).1 (e.symm i).2
    have heval : (e.symm i).2.val (r (e.symm i).1) = i := e.apply_symm_apply i
    simpa only [heval] using hi.symm
  let ef := LinearEquiv.ofBijective f ⟨hinj, hsurj⟩
  rw [← ef.finrank_eq, Module.finrank_prod, Module.finrank_fintype_fun_eq_card,
    Subspace.dual_finrank_eq, planes_finrank B hB]
  rfl

/-- Constant-displacement representatives for an order-four subgroup have even weight. -/
theorem regularEight_four_displacement_le_core {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 4) :
    eightDisplacementSpace B ≤ core (Fin 8) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  obtain ⟨r, hr⟩ := planes_orbit_coordinates hA hBA hB
  let e : Bool × B ≃ Fin 8 := Equiv.ofBijective _ hr
  have hc : Fintype.card B = 4 := by simpa [Nat.card_eq_fintype_card] using hB
  intro v hv
  obtain ⟨χ, hχ⟩ := (planes_affine_iff B r hr v).mp hv
  rw [mem_core, ← Equiv.sum_comp e v, Fintype.sum_prod_type]
  have hv' (t : Bool) (b : B) : v (e (t, b)) = v (r t) + χ (Additive.ofMul b) := hχ t b
  simp [hv', Finset.sum_add_distrib, hc, nsmul_eq_mul,
    show (4 : ZMod 2) = 0 by decide, show (2 : ZMod 2) = 0 by decide]

/-- The natural fixed space of an order-four subgroup has dimension three. -/
theorem fixedSpace_natural_regularEight_four_finrank {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (hB : Nat.card B = 4) :
    Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) B) = 3 := by
  have h := eightDisplacementSpace_finrank_eq_natural_add_one B
    (regularEight_four_displacement_le_core hA hBA hB)
  rw [regularEight_four_displacement_finrank hA hBA hB] at h
  omega

end CFSG.Quasithin.ChapterB.Offenders
