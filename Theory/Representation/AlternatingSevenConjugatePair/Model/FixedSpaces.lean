module
public import Theory.Representation.AlternatingSevenConjugatePair
public import Theory.Representation.BinaryAlternatingSevenCohomology
public import Theory.Representation.BinaryNaturalDual
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Mathlib.LinearAlgebra.Transvection.Basic

/-!
# Single-element reductions for a conjugate pair of binary A₇ modules

Both four-dimensional irreducible summands are faithful by simplicity of A₇.
Fixed spaces split over these summands for inner actors. An odd involution
interchanges them and consequently has fixed codimension four. Every element
of odd prime order moves at least two dimensions in each faithful summand:
a binary automorphism moving at most one dimension has square one.

These statements hold for every finite-dimensional `Pair`, without a choice
of model or a module-classification premise. The even-involution calculation
and the double-three-cycle fixed-plane witness remain separate obligations.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
H.8, printed p.389/PDF p.400, with standing hypotheses on printed p.377.
-/

@[expose] public section

namespace Representation.AlternatingSevenConjugatePair
open BinaryOffender
noncomputable section
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

theorem Pair.finrank_eq_eight (D : Pair V) : Module.finrank (ZMod 2) V = 8 := by
  have h := Submodule.finrank_add_eq_of_isCompl D.complementary
  rw [D.first_dim, D.second_dim] at h
  exact h.symm

theorem Pair.first_faithful (D : Pair V) : Function.Injective D.first.toRepresentation := by
  let _ := D.first_irreducible
  exact binaryAlternatingSeven_faithful_of_irreducible_four _ D.first_dim

theorem Pair.second_faithful (D : Pair V) : Function.Injective D.second.toRepresentation := by
  let _ := D.second_irreducible
  exact binaryAlternatingSeven_faithful_of_irreducible_four _ D.second_dim

/-- All odd involutions have the displacement claimed in H.8. -/
theorem Pair.odd_involution_fixedCodim (D : Pair V) (t : Equiv.Perm (Fin 7))
    (ht : orderOf t = 2) (hodd : t ∉ alternatingGroup (Fin 7)) :
    fixedCodim D.representation (Subgroup.zpowers t) = 4 := by
  let e : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (D.representation t)
    (D.representation.apply_bijective t)
  have ht2 : t ^ 2 = 1 := by simpa only [ht] using pow_orderOf_eq_one t
  have he : ∀ v, e (e v) = v := by
    intro v
    change (D.representation t * D.representation t) v = v
    rw [← map_mul, ← pow_two, ht2, map_one]
    rfl
  have hf : BinaryNaturalDual.fixedSpace e = fixedSpace D.representation (Subgroup.zpowers t) := by
    ext v
    rw [BinaryNaturalDual.mem_fixedSpace, mem_fixedSpace_zpowers_iff]
    rfl
  have hfixed := BinaryNaturalDual.finrank_fixedSpace D.complementary e he
    (D.swap_first t hodd) (D.swap_second t hodd)
  rw [hf, D.first_dim] at hfixed
  have hdim := fixedCodim_add_finrank D.representation (Subgroup.zpowers t)
  rw [hfixed, D.finrank_eq_eight] at hdim
  omega

/-- Inclusion identifies summand fixed vectors with their ambient intersection. -/
def cyclicSummandFixedEquiv (ρ : Representation (ZMod 2) (Equiv.Perm (Fin 7)) V)
    (U : Subrepresentation (ρ.comp (alternatingGroup (Fin 7)).subtype))
    (a : alternatingGroup (Fin 7)) :
    fixedSpace U.toRepresentation (Subgroup.zpowers a) ≃ₗ[ZMod 2]
      (U.toSubmodule ⊓ fixedSpace ρ (Subgroup.zpowers a.val) : Submodule (ZMod 2) V) where
  toFun v := ⟨v.val, v.val.property, by
    apply (mem_fixedSpace_zpowers_iff ρ a.val (v.val : V)).mpr
    exact congrArg Subtype.val ((mem_fixedSpace_zpowers_iff _ a v.val).mp v.property)⟩
  invFun v := ⟨⟨v, v.property.1⟩, by
    rw [mem_fixedSpace_zpowers_iff]
    exact Subtype.ext ((mem_fixedSpace_zpowers_iff _ a.val v.val).mp v.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [FiniteDimensional (ZMod 2) V] in
theorem Pair.fixedSpace_eq_sup (D : Pair V) (A : Subgroup (Equiv.Perm (Fin 7)))
    (hA : A ≤ alternatingGroup (Fin 7)) :
    fixedSpace D.representation A = D.firstFixedSpace A ⊔ D.secondFixedSpace A := by
  apply le_antisymm
  · intro v hv
    obtain ⟨u, w, hu, hw, rfl⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp D.complementary.codisjoint v
    have hcomponents (a : A) : D.representation a u = u ∧ D.representation a w = w := by
      have he : (Submodule.prodEquivOfIsCompl _ _ D.complementary)
          (⟨D.representation a u, D.first.apply_mem_toSubmodule ⟨a, hA a.property⟩ hu⟩,
            ⟨D.representation a w, D.second.apply_mem_toSubmodule ⟨a, hA a.property⟩ hw⟩) =
          (Submodule.prodEquivOfIsCompl _ _ D.complementary) (⟨u, hu⟩, ⟨w, hw⟩) := by
        change D.representation a u + D.representation a w = u + w
        rw [← map_add]
        exact hv a
      have h := (Submodule.prodEquivOfIsCompl _ _ D.complementary).injective he
      exact ⟨congrArg (fun z => (z.1 : V)) h, congrArg (fun z => (z.2 : V)) h⟩
    exact Submodule.mem_sup.mpr ⟨u, ⟨hu, fun a => (hcomponents a).1⟩,
      w, ⟨hw, fun a => (hcomponents a).2⟩, rfl⟩
  · exact sup_le inf_le_right inf_le_right

theorem Pair.finrank_fixedSpace (D : Pair V) (A : Subgroup (Equiv.Perm (Fin 7)))
    (hA : A ≤ alternatingGroup (Fin 7)) :
    Module.finrank (ZMod 2) (fixedSpace D.representation A) =
      Module.finrank (ZMod 2) (D.firstFixedSpace A) +
      Module.finrank (ZMod 2) (D.secondFixedSpace A) := by
  have hd : Disjoint (D.firstFixedSpace A) (D.secondFixedSpace A) :=
    D.complementary.disjoint.mono inf_le_left inf_le_left
  have h := (D.firstFixedSpace A).finrank_sup_add_finrank_inf_eq (D.secondFixedSpace A)
  rw [hd.eq_bot, finrank_bot, add_zero, ← D.fixedSpace_eq_sup A hA] at h
  exact h

/-- Displacement is additive on the two actual invariant summands. -/
theorem Pair.inner_fixedCodim (D : Pair V) (a : alternatingGroup (Fin 7)) :
    fixedCodim D.representation (Subgroup.zpowers a.val) =
      fixedCodim D.first.toRepresentation (Subgroup.zpowers a) +
      fixedCodim D.second.toRepresentation (Subgroup.zpowers a) := by
  have h := D.finrank_fixedSpace (Subgroup.zpowers a.val) (Subgroup.zpowers_le.mpr a.property)
  have hfirst := (cyclicSummandFixedEquiv D.representation D.first a).finrank_eq
  have hsecond := (cyclicSummandFixedEquiv D.representation D.second a).finrank_eq
  change _ = Module.finrank (ZMod 2) (D.firstFixedSpace _) at hfirst
  change _ = Module.finrank (ZMod 2) (D.secondFixedSpace _) at hsecond
  have htotal := fixedCodim_add_finrank D.representation (Subgroup.zpowers a.val)
  have hU := fixedCodim_add_finrank D.first.toRepresentation (Subgroup.zpowers a)
  have hW := fixedCodim_add_finrank D.second.toRepresentation (Subgroup.zpowers a)
  rw [D.first_dim] at hU
  rw [D.second_dim] at hW
  rw [D.finrank_eq_eight] at htotal
  omega

private theorem binary_square_of_displacement_le_one
    (e : V ≃ₗ[ZMod 2] V)
    (h : Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1) :
    e ^ 2 = 1 := by
  obtain ⟨f, v, he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr h
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by
      change e.toLinearMap v = 0
      rw [he, LinearMap.transvection.apply, ho, one_smul, ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv, map_zero] at ho
    exact (zero_ne_one ho).elim
  apply LinearEquiv.ext
  intro x
  change e (e x) = x
  have hex (x : V) : e x = x + f x • v := congrArg (fun l : V →ₗ[ZMod 2] V => l x) he
  simp only [hex, map_add, map_smul, hfv, smul_zero, add_zero]
  simp [add_assoc, ZModModule.add_self]

/-- A faithful binary action of an odd-prime-order element moves at least a plane. -/
theorem two_le_fixedCodim_of_odd_prime {G : Type*} [Group G]
    (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ)
    (x : G) (hp : (orderOf x).Prime) (hodd : orderOf x ≠ 2) :
    2 ≤ fixedCodim ρ (Subgroup.zpowers x) := by
  by_contra hn
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id)) ≤ 1 := by
    rw [← fixedCodim_zpowers_eq_displacement_rank]
    omega
  let e := LinearEquiv.ofBijective (ρ x) (ρ.apply_bijective x)
  have he := binary_square_of_displacement_le_one e hr
  have hx : x ^ 2 = 1 := by
    apply hρ
    rw [map_pow, map_one]
    exact congrArg LinearEquiv.toLinearMap he
  have hd := orderOf_dvd_of_pow_eq_one hx
  exact hodd ((Nat.dvd_prime Nat.prime_two).mp hd |>.resolve_left hp.ne_one)

/-- The universal odd-prime displacement bound for H.8. -/
theorem Pair.odd_prime_fixedCodim (D : Pair V) (x : Equiv.Perm (Fin 7))
    (hp : (orderOf x).Prime) (hodd : orderOf x ≠ 2) :
    4 ≤ fixedCodim D.representation (Subgroup.zpowers x) := by
  have hx : x ∈ alternatingGroup (Fin 7) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have hd : orderOf (Equiv.Perm.sign x) ∣ orderOf x := orderOf_map_dvd _ _
    rcases Int.units_eq_one_or (Equiv.Perm.sign x) with h | h
    · exact h
    · rw [h, show orderOf (-1 : ℤˣ) = 2 from orderOf_eq_prime (by decide) (by decide)] at hd
      exact (hodd ((((Nat.dvd_prime hp).mp hd).resolve_left (by decide)).symm)).elim
  let a : alternatingGroup (Fin 7) := ⟨x, hx⟩
  have ha : orderOf a = orderOf x := (orderOf_injective (alternatingGroup (Fin 7)).subtype Subtype.val_injective a).symm
  have hU := two_le_fixedCodim_of_odd_prime D.first.toRepresentation D.first_faithful a
    (by simpa only [ha] using hp) (by simpa only [ha] using hodd)
  have hW := two_le_fixedCodim_of_odd_prime D.second.toRepresentation D.second_faithful a
    (by simpa only [ha] using hp) (by simpa only [ha] using hodd)
  have he := D.inner_fixedCodim a
  change fixedCodim D.representation (Subgroup.zpowers x) = _ at he
  omega

end
end Representation.AlternatingSevenConjugatePair
