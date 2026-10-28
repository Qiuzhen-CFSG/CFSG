module

public import Theory.Representation.BinaryCoprimeDegree.TransitivePlane
public import Theory.Representation.AbelianFrobeniusDisplacement
public import Theory.Representation.Tits.FrobeniusDisplacement.GroupData

/-!
# Displacement in the Tits five-local subgroup

The certified abelian kernel of order 25 is elementary abelian. Its free
order-24 complement acts transitively on nonidentity elements, hence on the
six lines. The binary hyperplane decomposition gives equal positive line
contributions, each of dimension at least ord₅(2) = 4. A nonidentity kernel
element fixes exactly one contribution and therefore moves at least twenty
dimensions.

A nontrivial character supplies a regular complement submodule after scalar
extension. The literal quaternion square has order two in that complement,
so its twelve two-element basis orbits give displacement at least twelve.
The general Frobenius displacement theorem descends this rank to the original
field. Neither bound requires irreducibility or a degree assumption.

This replaces the small-degree reduction in the Tits case of Guralnick–Malle,
Classification of 2F-modules II, Lemma 8.8, internal p.57,
DOI 10.1515/9783110198126.117, used by Aschbacher–Smith K.3, printed p.457.
The concrete words and their ATLAS attribution are in Tits/FiveFrobenius.
-/

public section

namespace Representation.BinaryCoprimeDegree
open Subgroup
open scoped IsMulCommutative

private theorem plane_hyperplanes_conjugate
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : Nat.card P = p ^ 2)
    (htrans : ∀ x y : P, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (P : Set G), P.normalizerMonoidHom g x = y)
    (H K : Subgroup P) (hH : H.index = p) (hK : K.index = p) :
    K ∈ normalizerHyperplaneOrbit P H := by
  have hp := (Fact.out : p.Prime).two_le
  have hcH : Nat.card H = p := by
    have hc := H.card_mul_index
    rw [hP, hH] at hc
    nlinarith
  have hcK : Nat.card K = p := by
    have hc := K.card_mul_index
    rw [hP, hK] at hc
    nlinarith
  let : IsCyclic H := isCyclic_of_prime_card hcH
  let : IsCyclic K := isCyclic_of_prime_card hcK
  obtain ⟨x, hx⟩ := H.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  obtain ⟨y, hy⟩ := K.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance
  have hxn : x ≠ 1 := by
    intro hx1
    rw [← hx, hx1] at hcH
    simp at hcH
    omega
  have hyn : y ≠ 1 := by
    intro hy1
    rw [← hy, hy1] at hcK
    simp at hcK
    omega
  obtain ⟨g, hg⟩ := htrans x y hxn hyn
  refine ⟨g, ?_⟩
  change H.map (P.normalizerMonoidHom g).toMonoidHom = K
  rw [← hx, MonoidHom.map_zpowers]
  change zpowers (P.normalizerMonoidHom g x) = K
  rw [hg, hy]

/-- A nonidentity element of a transitive elementary plane moves all but one
of its equally sized hyperplane contributions. -/
theorem transitive_plane_displacement
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (hf : Function.Injective rho)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : Nat.card P = p ^ 2)
    (htrans : ∀ x y : P, x ≠ 1 → y ≠ 1 →
      ∃ g : normalizer (P : Set G), P.normalizerMonoidHom g x = y)
    (k : P) (hk : k ≠ 1) :
    p * orderOf (2 : ZMod p) ≤
      Module.finrank (ZMod 2) (LinearMap.range (rho k - 1)) := by
  classical
  have hp := (Fact.out : p.Prime).two_le
  let H : Subgroup P := zpowers k
  have hc : Nat.card H = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p P) k) hk
  have hH : H.index = p := by
    have hc' := H.card_mul_index
    rw [hc, hP] at hc'
    nlinarith
  have hne : P ≠ ⊥ := by
    intro he
    have : (k : G) = 1 := he ▸ k.property
    exact hk (Subtype.ext this)
  have hsum := hyperplane_dimension_sum rho hp2 P
  have hproper := fixed_finrank_lt_of_faithful rho hf P hne
  have hpos : 0 < hyperplaneDimensionSum rho P p := by omega
  obtain ⟨H₀, hH₀, hm₀⟩ := Finset.sum_pos_iff.mp hpos
  have hidx₀ := (mem_hyperplanes P p H₀).mp hH₀
  have hm : 0 < hyperplaneMultiplicity rho P H := by
    rw [hyperplaneMultiplicity_eq_of_mem_orbit rho P H₀ H
      (plane_hyperplanes_conjugate P hP htrans H₀ H hidx₀ hH)]
    exact hm₀
  have hlow := orderOf_le_hyperplaneMultiplicity rho hp2 P H hH hm
  have hbound := orbit_mul_multiplicity_le_sum rho P H hH
  rw [transitive_plane_hyperplane_orbit_card P hP htrans H hH] at hbound
  have hfix := hyperplaneMultiplicity_add_fixed_finrank rho P H
  have heq : invariants (rho.comp (P.subtype.comp H.subtype)) =
      LinearMap.ker (rho k - 1) := by
    exact (ker_sub_one_eq_cyclic_invariants (rho.comp P.subtype) k).symm
  rw [heq] at hfix
  have hrank := (rho k - 1).finrank_range_add_finrank_ker
  nlinarith

end Representation.BinaryCoprimeDegree



namespace Representation.TitsFrobeniusDisplacement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Every nonidentity element of the certified five-kernel moves at least
twenty dimensions in every faithful binary representation. -/
theorem fiveKernel_displacement (rho : Representation (ZMod 2) Tits.ParrottGroup V)
    (hf : Function.Injective rho) (k : Tits.fiveKernel) (hk : k ≠ 1) :
    20 ≤ Module.finrank (ZMod 2) (LinearMap.range (rho k - 1)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsElementaryAbelian 5 Tits.fiveKernel := fiveKernel_elementary
  have h := BinaryCoprimeDegree.transitive_plane_displacement rho hf
    (p := 5) (by decide) Tits.fiveKernel (by simpa using Tits.fiveKernel_card)
    five_transitive k hk
  simpa only [BinaryPrimeDegree.orderOf_two_mod_five] using h

/-- The literal quaternion square in the five-complement moves at least twelve
dimensions in every faithful binary representation. -/
theorem fiveInverter_displacement (rho : Representation (ZMod 2) Tits.ParrottGroup V)
    (hf : Function.Injective rho) :
    12 ≤ Module.finrank (ZMod 2) (LinearMap.range
      (rho (Tits.parrottFiniteImageEquiv.symm (Tits.FiveFrobenius.r ^ 2)) - 1)) := by
  let : Nontrivial Tits.fiveKernel :=
    (Finite.one_lt_card_iff_nontrivial (α := Tits.fiveKernel)).mp
      (by rw [Tits.fiveKernel_card]; decide)
  let c : Tits.fiveComplement := ⟨_, inverter_mem⟩
  have hc : orderOf c = 2 := by
    rw [← orderOf_injective Tits.fiveComplement.subtype Subtype.val_injective c]
    exact inverter_order
  have hb := prime_displacement_bounds_of_fixedPointFree_normalizer rho
    Tits.fiveKernel Tits.fiveComplement hf
    (by rw [Tits.fiveKernel_card]; decide)
    Tits.fiveComplement_normalizes Tits.fiveComplement_free c (by decide : Nat.Prime 2) hc
  simpa only [Tits.fiveComplement_card] using hb.1

end Representation.TitsFrobeniusDisplacement
