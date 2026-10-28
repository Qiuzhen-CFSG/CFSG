module
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.RootScalars.Model
public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Center

/-!
# The actual Borel scalar action on any Sylow center of PSL₃

For a finite field of order `2^n`, `n ≥ 1`, an actual projective model
isomorphism and Sylow conjugacy transport the highest-root coordinates to
the center of the specified Sylow subgroup. The whole Sylow normalizer acts
through a surjective character to the field units. Its kernel is precisely
the ambient centralizer of that center, restricted to the normalizer.

The conjugation formula gives transitivity on the nonidentity center
elements, including when `n = 1`. For `n > 1` it also shows that the common
fixed subgroup in the center is trivial. The field units are identified
with the cyclic group of order `2^n - 1` by an actual group equivalence.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the PSL₃ case
of E.6.8, printed pp.247–248 (PDF pp.258–259). This intrinsic calculation
uses the matrix centralizer–torus factorization, independently of the
Chapter E Borel alternative and its later complement results.
-/

public section
open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3 Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3.LinearThree.RootScalars
variable (F : Type*) [Field F]

/-- The kernel is the relative centralizer of the actual root image. -/
theorem scalarCharacter_ker {J : Type*} [Group J] (B : Subgroup J)
    (r : Multiplicative F →* J) (χ : B →* Fˣ)
    (hr : Function.Injective r)
    (hconj : ∀ (b : B) (x : F), (b : J) * r (Multiplicative.ofAdd x) * (b : J)⁻¹ =
      r (Multiplicative.ofAdd ((χ b : F) * x))) :
    χ.ker = (centralizer (r.range : Set J)).subgroupOf B := by
  ext b
  change χ b = 1 ↔ (b : J) ∈ centralizer (r.range : Set J)
  rw [mem_centralizer_iff]
  constructor
  · intro hb y hy
    obtain ⟨x,rfl⟩ := hy
    have h := hconj b x.toAdd
    simp only [hb, Units.val_one, one_mul] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hb
    apply Units.ext
    have hc := hb (r (Multiplicative.ofAdd (1 : F))) ⟨_,rfl⟩
    have he : (b : J) * r (Multiplicative.ofAdd (1 : F)) * (b : J)⁻¹ =
        r (Multiplicative.ofAdd (1 : F)) := by rw [← hc, mul_inv_cancel_right]
    have hh := hr ((hconj b 1).symm.trans he)
    simpa using congrArg Multiplicative.toAdd hh

variable [Finite F]

/-- Coordinates and scalar character on the specified Sylow center and normalizer. -/
theorem exists_sylow_center_scalar_action {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) :
    ∃ (r : Multiplicative F →* J) (χ : normalizer (S : Set J) →* Fˣ),
      Function.Injective r ∧ r.range = (center S).map (S : Subgroup J).subtype ∧
      Function.Surjective χ ∧
      (∀ (b : normalizer (S : Set J)) (x : F),
        (b : J) * r (Multiplicative.ofAdd x) * (b : J)⁻¹ =
          r (Multiplicative.ofAdd ((χ b : F) * x))) ∧
      χ.ker = (centralizer ((center S).map (S : Subgroup J).subtype : Set J)).subgroupOf
        (normalizer (S : Set J)) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, Nat.ne_of_gt hn])
  let : CharP F 2 := ringChar.of_eq hc
  let P := (unipotentSylow F hn hF).mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq J P S
  let f : PSL(3,F) ≃* J := e.symm.trans (MulAut.conj g)
  have hS : (unipotent F).map f.toMonoidHom = (S : Subgroup J) := by
    have hh := congrArg Sylow.toSubgroup hg
    change ((unipotent F).map e.symm.toMonoidHom).map (MulAut.conj g).toMonoidHom = _ at hh
    change (unipotent F).map ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
    rw [← Subgroup.map_map]
    exact hh
  have hN : (borel F).map f.toMonoidHom = normalizer (S : Set J) := by
    rw [← normalizer_unipotent F hn hF, map_equiv_normalizer_eq, hS]
    rfl
  have hZ : (projectiveCenter F).map f.toMonoidHom =
      (center S).map (S : Subgroup J).subtype := by
    rw [projectiveCenter_eq_mapped_center, map_subgroup_center_eq _ f.injective, hS]
  let eB : borel F ≃* normalizer (S : Set J) :=
    ((borel F).equivMapOfInjective f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hN)
  let r : Multiplicative F →* J := f.toMonoidHom.comp (root F)
  let χ : normalizer (S : Set J) →* Fˣ := (borelCharacter F).comp eB.symm.toMonoidHom
  have hr : Function.Injective r := f.injective.comp (root_injective F)
  have hrange : r.range = (center S).map (S : Subgroup J).subtype := by
    rw [MonoidHom.range_comp, root_range, hZ]
  have hχ : Function.Surjective χ := (borelCharacter_surjective F).comp eB.symm.surjective
  have hconj (b : normalizer (S : Set J)) (x : F) :
      (b : J) * r (Multiplicative.ofAdd x) * (b : J)⁻¹ =
        r (Multiplicative.ofAdd ((χ b : F) * x)) := by
    obtain ⟨b,rfl⟩ := eB.surjective b
    change f (b : PSL(3,F)) * f (root F (Multiplicative.ofAdd x)) *
      (f (b : PSL(3,F)))⁻¹ =
        f (root F (Multiplicative.ofAdd ((borelCharacter F (eB.symm (eB b)) : F) * x)))
    simp only [MulEquiv.symm_apply_apply, ← map_inv, ← map_mul, borel_conjugation]
  refine ⟨r,χ,hr,hrange,hχ,hconj,?_⟩
  rw [scalarCharacter_ker F _ r χ hr hconj, hrange]

/-- The field units identify the full scalar action image with the stated cyclic group. -/
noncomputable def unitsCyclicEquiv {n : ℕ} (hF : Nat.card F = 2 ^ n) :
    Fˣ ≃* Multiplicative (ZMod (2 ^ n - 1)) :=
  mulEquivOfCyclicCardEq (by
    simp only [Nat.card_units, hF, Nat.card_congr (Multiplicative.toAdd :
      Multiplicative (ZMod (2 ^ n - 1)) ≃ ZMod (2 ^ n - 1)), Nat.card_zmod])

/-- The actual normalizer is transitive on nonidentity elements of the Sylow center,
including over the field of order two. -/
theorem sylow_center_nonidentity_transitive {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J) :
    ∀ z ∈ (center S).map (S : Subgroup J).subtype, z ≠ 1 →
      ∀ w ∈ (center S).map (S : Subgroup J).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (S : Set J), b * z * b⁻¹ = w := by
  obtain ⟨r,χ,_,hrange,hχ,hconj,_⟩ := exists_sylow_center_scalar_action F hn hF e S
  intro z hz hzne w hw hwne
  rw [← hrange] at hz hw
  obtain ⟨x,rfl⟩ := hz
  obtain ⟨y,rfl⟩ := hw
  have hx : x.toAdd ≠ 0 := by
    intro hx
    have hx1 : x = 1 := hx
    exact hzne (hx1 ▸ r.map_one)
  have hy : y.toAdd ≠ 0 := by
    intro hy
    have hy1 : y = 1 := hy
    exact hwne (hy1 ▸ r.map_one)
  let a : Fˣ := Units.mk0 (y.toAdd / x.toAdd) (div_ne_zero hy hx)
  obtain ⟨b,hb⟩ := hχ a
  refine ⟨b,b.property,?_⟩
  have hc := hconj b x.toAdd
  rw [hb] at hc
  simpa only [a, Units.val_mk0, div_mul_cancel₀ _ hx, ofAdd_toAdd] using hc

/-- For fields larger than two, the normalizer fixes only the identity in its
Sylow center. The restriction `1 < n` is necessary. -/
theorem sylow_center_fixed_eq_one {J : Type*} [Group J] [Finite J]
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (e : J ≃* PSL(3,F)) (S : Sylow 2 J)
    (z : J) (hz : z ∈ (center S).map (S : Subgroup J).subtype)
    (hfixed : ∀ b ∈ normalizer (S : Set J), b * z * b⁻¹ = z) : z = 1 := by
  obtain ⟨r,χ,hr,hrange,hχ,hconj,_⟩ :=
    exists_sylow_center_scalar_action F (by omega) hF e S
  rw [← hrange] at hz
  obtain ⟨x,rfl⟩ := hz
  by_cases hx : x.toAdd = 0
  · have hx1 : x = 1 := hx
    exact hx1 ▸ r.map_one
  have hall : ∀ a : Fˣ, a = 1 := by
    intro a
    obtain ⟨b,hb⟩ := hχ a
    have hh := (hconj b x.toAdd).symm.trans (hfixed b b.property)
    rw [hb] at hh
    have he := congrArg Multiplicative.toAdd (hr hh)
    apply Units.ext
    apply mul_right_cancel₀ hx
    simpa only [one_mul, Units.val_one, toAdd_ofAdd] using he
  have hcard : Nat.card Fˣ = 1 := Nat.card_eq_one_iff_exists.mpr ⟨1,hall⟩
  rw [Nat.card_units, hF] at hcard
  have hp : 2 ^ 1 < 2 ^ n := Nat.pow_lt_pow_right (by decide) hn
  simp only [pow_one] at hp
  omega

end Matrix.PSL3.LinearThree.RootScalars
