module

public import Theory.Representation.SubrepresentationLattice
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Theory.Representation.NormalInvariants
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum

/-!
# Binary simple modules above a normal cubic subgroup

Let K and X be normal subgroups of a finite group H. If K acts trivially,
H/(KX) is a two-group, and the normal subgroup X of order three acts
nontrivially on a simple binary module, its dimension is exactly two.

A Sylow two-subgroup maps onto H/(KX) and fixes a nonzero vector. Its
X-orbit spans the whole module, giving dimension at most |X|. Normality
and irreducibility make the X-fixed space zero; the fixed-point counting
congruence modulo three then gives dimension two. No splitting or S₃
factor is assumed.

This is the multiplicity-space dimension argument needed for the Clifford
pairings in Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.21(1), printed p.956. Construction of the multiplicity module and of
an index-two inertia block is separate from this dimension result.
-/

public section

namespace Representation.CubicClifford

variable {H V : Type*} [Group H] [Finite H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private abbrev action (ρ : Representation (ZMod 2) H V) : MulAction H V where
  smul h v := ρ h v
  one_smul v := by change ρ 1 v = v; simp
  mul_smul h k v := by
    change ρ (h * k) v = ρ h (ρ k v)
    simp [Module.End.mul_apply]

omit [Finite H] in
private theorem fixed_vector (ρ : Representation (ZMod 2) H V)
    (hH : IsPGroup 2 H) [Nontrivial V] :
    ∃ v : V, v ≠ 0 ∧ ∀ h, ρ h v = v := by
  let := action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hd : 2 ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
    exact dvd_pow_self 2 (Module.finrank_pos.ne')
  obtain ⟨v, hv, hne⟩ := hH.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    V hd (a := (0 : V)) (by intro h; exact map_zero (ρ h))
  exact ⟨v, Ne.symm hne, hv⟩

private theorem sylow_surjective (X : Subgroup H) [X.Normal]
    (hQ : IsPGroup 2 (H ⧸ X)) (P : Sylow 2 H) :
    Function.Surjective ((QuotientGroup.mk' X).comp (P : Subgroup H).subtype) := by
  let T := P.mapSurjective (QuotientGroup.mk'_surjective X)
  have htop : (T : Subgroup (H ⧸ X)) = ⊤ :=
    (T.is_maximal' (hQ.to_subgroup ⊤) le_top).symm
  intro a
  have ha : a ∈ (P : Subgroup H).map (QuotientGroup.mk' X) := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective X) P, htop]
    trivial
  obtain ⟨p, hp, he⟩ := ha
  exact ⟨⟨p, hp⟩, he⟩

/-- If K acts trivially and H/(KX) is a two-group, a binary simple module
has dimension at most |X|. -/
theorem finrank_le_card_of_kernel (ρ : Representation (ZMod 2) H V)
    [IsIrreducible ρ] (K X : Subgroup H) [K.Normal] [X.Normal]
    (hK : K ≤ ρ.ker) (hQ : IsPGroup 2 (H ⧸ (K ⊔ X))) :
    Module.finrank (ZMod 2) V ≤ Nat.card X := by
  classical
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  let : Fintype X := Fintype.ofFinite X
  let P : Sylow 2 H := Sylow.nonempty.some
  obtain ⟨v, hv, hfix⟩ := fixed_vector (ρ.comp (P : Subgroup H).subtype) P.isPGroup'
  let U := Submodule.span (ZMod 2) (Set.range (fun x : X => ρ x v))
  have hvU : v ∈ U := by
    have := Submodule.subset_span (R := ZMod 2)
      (Set.mem_range_self (f := fun x : X => ρ x v) 1)
    simpa using this
  have hstable (h : H) (u : V) (hu : u ∈ U) : ρ h u ∈ U := by
    induction hu using Submodule.span_induction with
    | mem u hu =>
      obtain ⟨x, rfl⟩ := hu
      let Y := K ⊔ X
      obtain ⟨p, hp⟩ := sylow_surjective Y hQ P (QuotientGroup.mk' Y h)
      have hxp : h * (x : H) * (p : H)⁻¹ ∈ Y := by
        apply (QuotientGroup.eq_one_iff _).mp
        change (QuotientGroup.mk' Y) (h * (x : H) * (p : H)⁻¹) = 1
        have hxq : (QuotientGroup.mk' Y) (x : H) = 1 :=
          (QuotientGroup.eq_one_iff (N := Y) _).mpr ((le_sup_right : X ≤ Y) x.property)
        rw [map_mul, map_mul, map_inv, hxq, mul_one]
        change (QuotientGroup.mk' Y) p = (QuotientGroup.mk' Y) h at hp
        rw [hp, mul_inv_cancel]
      obtain ⟨k, hk, y, hy, he⟩ :
          ∃ k ∈ K, ∃ y ∈ X, k * y = h * (x : H) * (p : H)⁻¹ := by
        simpa only [Y, ← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] using hxp
      have hkp : ρ k = 1 := hK hk
      have hvp : ρ (p : H) v = v := hfix p
      have heq : ρ h (ρ x v) = ρ y v := by
        calc
          _ = ρ (h * (x : H) * (p : H)⁻¹) (ρ (p : H) v) := by
            simp only [← Module.End.mul_apply, ← map_mul]
            simp only [mul_assoc, inv_mul_cancel, mul_one]
          _ = ρ (k * y) v := by rw [hvp, ← he]
          _ = ρ y v := by rw [map_mul, hkp, one_mul]
      rw [heq]
      exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩
    | zero => simpa only [map_zero] using U.zero_mem
    | add a b ha hb iha ihb => simpa only [map_add] using U.add_mem iha ihb
    | smul c a ha iha => simpa only [map_smul] using U.smul_mem c iha
  let S : Subrepresentation ρ := ⟨U, hstable⟩
  have hne : S ≠ ⊥ := by
    intro he
    apply hv
    have hmem : v ∈ S := hvU
    rw [he] at hmem
    exact hmem
  have htop : S = ⊤ := (IsSimpleOrder.eq_bot_or_eq_top S).resolve_left hne
  have hspan : U = ⊤ := congrArg Subrepresentation.toSubmodule htop
  simpa only [Nat.card_eq_fintype_card] using (finrank_le_of_span_eq_top hspan)

/-- A nontrivial normal cubic action has dimension two when K acts trivially
and H/(KX) is a two-group. -/
theorem finrank_eq_two (ρ : Representation (ZMod 2) H V) [IsIrreducible ρ]
    (K X : Subgroup H) [K.Normal] [X.Normal] (hX : Nat.card X = 3)
    (hK : K ≤ ρ.ker) (hQ : IsPGroup 2 (H ⧸ (K ⊔ X))) (hne : ¬ X ≤ ρ.ker) :
    Module.finrank (ZMod 2) V = 2 := by
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial ρ
  have hfix : invariants (ρ.comp X.subtype) = ⊥ := by
    by_contra h
    exact hne (le_ker_of_normal_invariants_ne_bot ρ X h)
  let := action (ρ.comp X.subtype)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  have hfixed : MulAction.fixedPoints X V = {0} := by
    ext v
    change (∀ x : X, ρ x v = v) ↔ v = 0
    change v ∈ invariants (ρ.comp X.subtype) ↔ v = 0
    rw [hfix, Submodule.mem_bot]
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hmod := (IsPGroup.of_card (p := 3) (n := 1) (by simpa using hX)).card_modEq_card_fixedPoints V
  have hcardfix : Nat.card (MulAction.fixedPoints X V) = 1 := by
    rw [hfixed]
    exact Nat.card_unique
  rw [hcardfix, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hmod
  have hdim := finrank_le_card_of_kernel ρ K X hK hQ
  rw [hX] at hdim
  have hpos : 0 < Module.finrank (ZMod 2) V := Module.finrank_pos
  interval_cases Module.finrank (ZMod 2) V
  · norm_num [Nat.ModEq] at hmod
  · rfl
  · norm_num [Nat.ModEq] at hmod

end Representation.CubicClifford
