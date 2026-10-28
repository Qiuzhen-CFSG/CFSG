module
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Displacement.Odd
public import Theory.Representation.AbsolutelyIrreducible
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Mathieu.M22.Properties.Simplicity

/-!
# Absolute irreducibility of the actual ten-dimensional M22 modules

Odd-order fixed-space calculations show that order-eleven subgroups have
no fixed vectors and order-seven subgroups have a fixed line. Simplicity
makes every nonzero subrepresentation faithful; the order of two modulo
eleven forces its dimension to be at least ten. For an irreducible module,
an endomorphism acts by a scalar on the fixed line. Subtracting that scalar
and applying Schur's lemma shows it is scalar everywhere. The absolute
irreducibility criterion then applies to the literal code and cocode actions.

Source: Aschbacher--Smith, H.13.2, printed p.395, combined manuscript of
1 March 2004. This proof uses the genuine quotient actions and their native
coordinate duality, without identifying them by a representation-table label.
-/

public section
noncomputable section
open Representation Sporadic.Mathieu Representation.BinaryOffender
namespace MathieuCode

private theorem invariants_eq_bot_of_eleven
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    (hf : ∀ D : Subgroup M22, Nat.card D = 11 →
      Module.finrank (ZMod 2) (fixedSpace ρ D) = 0) : ρ.invariants = ⊥ := by
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := M22) 11
    (by rw [m22_order]; norm_num)
  have hz : fixedSpace ρ (Subgroup.zpowers g) = ⊥ := by
    exact Submodule.finrank_eq_zero.mp (hf _ ((Nat.card_zpowers g).trans hg))
  apply le_antisymm _ bot_le
  intro v hv
  apply hz.le
  intro a
  exact hv a.val

theorem m22Code_invariants_eq_bot : m22CodeRepresentation.invariants = ⊥ :=
  invariants_eq_bot_of_eleven _ m22_code_fixed_finrank_eleven

theorem m22Cocode_invariants_eq_bot : m22CocodeRepresentation.invariants = ⊥ :=
  invariants_eq_bot_of_eleven _ m22_cocode_fixed_finrank_eleven

private theorem irreducible_of_simple_of_degree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) M22 V) (hz : ρ.invariants = ⊥)
    (hd : Module.finrank (ZMod 2) V = 10) : ρ.IsIrreducible := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : Nontrivial V := Module.nontrivial_of_finrank_pos
    (by rw [hd]; decide : 0 < Module.finrank (ZMod 2) V)
  refine ⟨fun N => ?_⟩
  by_cases hN : N = ⊥
  · exact Or.inl hN
  right
  have hf : Function.Injective N.toRepresentation := by
    rcases N.toRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
    · exact N.toRepresentation.ker_eq_bot_iff.mp hk
    · have he : N.toRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
      have hle : N.toSubmodule ≤ ρ.invariants := by
        intro v hv g
        have h := DFunLike.congr_fun (congrArg (fun σ => σ g) he) ⟨v, hv⟩
        exact congrArg Subtype.val h
      rw [hz] at hle
      exact (hN (Subrepresentation.toSubmodule_injective (le_bot_iff.mp hle))).elim
  have hlo := BinaryPrimeDegree.orderOf_le_finrank N.toRepresentation hf
    (by decide : Nat.Prime 11) (by decide : 11 ≠ 2) (by rw [m22_order]; norm_num)
  rw [BinaryPrimeDegree.orderOf_two_mod_eleven] at hlo
  apply Subrepresentation.toSubmodule_injective
  by_contra hnt
  have hlt := Submodule.finrank_lt hnt
  rw [hd] at hlt
  omega

theorem m22Code_isIrreducible : m22CodeRepresentation.IsIrreducible :=
  irreducible_of_simple_of_degree _ m22Code_invariants_eq_bot finrank_m22Code

theorem m22Cocode_isIrreducible : m22CocodeRepresentation.IsIrreducible :=
  irreducible_of_simple_of_degree _ m22Cocode_invariants_eq_bot finrank_m22Cocode

private theorem absolutelyIrreducible_of_fixed_line {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    [ρ.IsIrreducible] (D : Subgroup G)
    (hd : Module.finrank (ZMod 2) (fixedSpace ρ D) = 1) :
    ρ.IsAbsolutelyIrreducible := by
  apply (isAbsolutelyIrreducible_iff_surjective ρ).mpr
  intro f
  have hne : fixedSpace ρ D ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hd
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hfv : f v ∈ fixedSpace ρ D := by
    intro g
    change ρ g.val (f v) = f v
    rw [← f.isIntertwining, show ρ g.val v = v from hv g]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hd hv hv0
  rw [hspan] at hfv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hfv
  refine ⟨c, ?_⟩
  have hz : f - algebraMap (ZMod 2) (End ρ) c = 0 := by
    rcases IsIrreducible.injective_or_eq_zero (f - algebraMap (ZMod 2) (End ρ) c) with hi | hz
    · exfalso
      apply hv0
      apply hi
      change f v - c • v = f 0 - c • (0 : V)
      rw [← hc, map_zero, smul_zero, sub_self, sub_self]
    · exact hz
  exact (sub_eq_zero.mp hz).symm

private theorem absolutelyIrreducible_of_seven
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) M22 V)
    [ρ.IsIrreducible]
    (hf : ∀ D : Subgroup M22, Nat.card D = 7 →
      Module.finrank (ZMod 2) (fixedSpace ρ D) = 1) : ρ.IsAbsolutelyIrreducible := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := M22) 7
    (by rw [m22_order]; norm_num)
  exact absolutelyIrreducible_of_fixed_line ρ (Subgroup.zpowers g)
    (hf _ ((Nat.card_zpowers g).trans hg))

/-- Absolute irreducibility of the actual native ten-dimensional code hyperplane. -/
theorem m22Code_isAbsolutelyIrreducible : m22CodeRepresentation.IsAbsolutelyIrreducible := by
  let : m22CodeRepresentation.IsIrreducible := m22Code_isIrreducible
  exact absolutelyIrreducible_of_seven _ m22_code_fixed_finrank_seven

/-- Absolute irreducibility of the literal quotient by the distinguished pair line. -/
theorem m22Cocode_isAbsolutelyIrreducible : m22CocodeRepresentation.IsAbsolutelyIrreducible := by
  let : m22CocodeRepresentation.IsIrreducible := m22Cocode_isIrreducible
  exact absolutelyIrreducible_of_seven _ m22_cocode_fixed_finrank_seven

end MathieuCode

