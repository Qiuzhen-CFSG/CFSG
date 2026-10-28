module

public import Theory.GroupTheory.CentralCoprimeAbelianLift
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Calculation

/-!
# Reducing a central cubic extension of S₄ to S₃

The normal Klein four of S₄ has a normal lift through a central kernel of
order three. The coprime lifting theorem gives this lift and its invariance
under the whole group. The map on the lift is injective, so it has order
four and exponent two. Quotienting by it gives a central cubic extension
of S₃: the new kernel is exactly the image of the original central kernel.
The condition that ninth powers detect cubic torsion descends by squaring.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 13.2.1 and Lemma 13.2.2(3), printed pp.876–877. This is the finite
group reduction used for the order of L₁,₊/O₂(L₁,₊).
-/

public section

noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.Hexacode.CubicLocalModel.Orders.CentralCubicSymmetricFour
open Theory.SpecificGroups.SymmetricSix

variable {X : Type*} [Group X] [Finite X]

/-- The normal Klein four in S₄ lifts to a normal four-group through a central
kernel of order three. -/
theorem exists_normal_klein_lift (f : X →* Equiv.Perm (Fin 4))
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 3)
    (hc : f.ker ≤ center X) :
    ∃ Q : Subgroup X, Q.Normal ∧ IsPGroup 2 Q ∧ Nat.card Q = 4 ∧
      Q.map f = DuadCalculation.core ∧ ∀ x ∈ Q, x ^ 2 = 1 := by
  have hcop : Nat.Coprime 2 (Nat.card f.ker) := by rw [hk]; decide
  obtain ⟨Q, hQp, _, hQf, hQn⟩ :=
    exists_abelian_prime_lift_of_central_coprime_kernel f hf hc hcop DuadCalculation.core
      (IsElementaryAbelian.isPGroup 2 DuadCalculation.core)
  have hQnormal : Q.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    simpa only [normalizer_eq_top, comap_top] using hQn
  have hinj := injective_comp_subtype_of_coprime_ker f hcop Q hQp
  let e : Q ≃* DuadCalculation.core := (MulEquiv.ofBijective (f.subgroupMap Q)
    ⟨fun x y h => hinj (congrArg Subtype.val h), f.subgroupMap_surjective Q⟩).trans
      (MulEquiv.subgroupCongr hQf)
  refine ⟨Q, hQnormal, hQp, (Nat.card_congr e.toEquiv).trans DuadCalculation.core_card, hQf, ?_⟩
  intro x hx
  have he : (⟨x, hx⟩ : Q) ^ 2 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 DuadCalculation.core) _
  exact congrArg Subtype.val he

/-- Quotienting by the lifted four-group leaves a central cubic extension of S₃,
and the absence of elements of order nine descends to this quotient. -/
theorem exists_central_cubic_s3_quotient (f : X →* Equiv.Perm (Fin 4))
    (hf : Function.Surjective f) (hk : Nat.card f.ker = 3)
    (hc : f.ker ≤ center X) (h9 : ∀ x : X, x ^ 9 = 1 → x ^ 3 = 1) :
    ∃ (Q : Subgroup X) (_hQn : Q.Normal),
      IsPGroup 2 Q ∧ Nat.card Q = 4 ∧
        ∃ g : (X ⧸ Q) →* Equiv.Perm (Fin 3), Function.Surjective g ∧
          Nat.card g.ker = 3 ∧ g.ker ≤ center (X ⧸ Q) ∧
            ∀ y : X ⧸ Q, y ^ 9 = 1 → y ^ 3 = 1 := by
  obtain ⟨Q, hQn, hQp, hQcard, hQf, hQ2⟩ := exists_normal_klein_lift f hf hk hc
  let := hQn
  let q := QuotientGroup.mk' Q
  let k := DuadCalculation.quotientHom.comp f
  have hQk : Q ≤ k.ker := by
    intro x hx
    change f x ∈ DuadCalculation.core
    rw [← hQf]
    exact mem_map_of_mem f hx
  let g : (X ⧸ Q) →* Equiv.Perm (Fin 3) := QuotientGroup.lift Q k hQk
  have hg : Function.Surjective g :=
    QuotientGroup.lift_surjective_of_surjective Q k (DuadCalculation.quotientHom_surjective.comp hf) hQk
  have hgq (x : X) : g (q x) = k x := rfl
  have hgker : g.ker = f.ker.map q := by
    ext y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    constructor
    · intro hx
      have hfx : f x ∈ DuadCalculation.core := hx
      rw [← hQf] at hfx
      obtain ⟨a, ha, hfa⟩ := hfx
      have hax : a⁻¹ * x ∈ f.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfa, inv_mul_cancel]
      refine mem_map.mpr ⟨a⁻¹ * x, hax, ?_⟩
      have hqa : q a = 1 := (QuotientGroup.eq_one_iff a).mpr ha
      rw [map_mul, map_inv, hqa, inv_one, one_mul]
    · rintro ⟨a, ha, he⟩
      rw [MonoidHom.mem_ker, ← he, hgq]
      change DuadCalculation.quotientHom (f a) = 1
      rw [MonoidHom.mem_ker.mp ha, map_one]
  have hker3 : IsPGroup 3 f.ker := IsPGroup.of_card (n := 1) (by simpa using hk)
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    rw [QuotientGroup.ker_mk', hQcard]; decide
  have hi := injective_comp_subtype_of_coprime_ker q hcop f.ker hker3
  let e : f.ker ≃* f.ker.map q := MulEquiv.ofBijective (q.subgroupMap f.ker)
    ⟨fun x y h => hi (congrArg Subtype.val h), q.subgroupMap_surjective f.ker⟩
  refine ⟨Q, hQn, hQp, hQcard, g, hg, ?_, ?_, ?_⟩
  · rw [hgker, ← Nat.card_congr e.toEquiv, hk]
  · rw [hgker]
    rintro y ⟨a, ha, rfl⟩
    apply mem_center_iff.mpr
    intro z
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective Q z
    exact (congrArg q (mem_center_iff.mp (hc ha) b))
  · intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Q y
    have hxQ : x ^ 9 ∈ Q := by
      apply (QuotientGroup.eq_one_iff (x ^ 9)).mp
      change q (x ^ 9) = 1
      rwa [map_pow]
    have hx18 : x ^ 18 = 1 := by
      simpa only [← pow_mul] using hQ2 (x ^ 9) hxQ
    have hx6 : x ^ 6 = 1 := by
      exact (pow_mul x 2 3).trans (h9 (x ^ 2) ((pow_mul x 2 9).symm.trans hx18))
    have hy6 : q x ^ 6 = 1 := by rw [← map_pow, hx6, map_one]
    have hh := hy
    rw [show 9 = 6 + 3 from rfl, pow_add, hy6, one_mul] at hh
    exact hh

end Representation.Hexacode.CubicLocalModel.Orders.CentralCubicSymmetricFour
