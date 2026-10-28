module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryGroupAction
public import Theory.Representation.InvertedOddSupportRank

/-!
# A binary degree bound from an inverted extraspecial seven-center

For a faithful binary action of a finite group containing an extraspecial
subgroup P of order 7³, suppose an involution inverts Z(P). Its central moving
space has dimension divisible by 7·ord₇(2)=21. Coprime action makes the central
fixed space on that support zero. Inversion makes the support order a square,
so its dimension is even. Faithfulness makes it nonzero, hence at least 42.

No irreducibility of the ambient representation or normality of P is required.
The center is mapped through the literal subgroup inclusion throughout.
This combines the extraspecial degree calculation in Aschbacher–Smith G.7.1(2)
with the inverted-support calculation of D.2.11. It supplies the stronger
Held degree bound needed at the cubic threshold two in K.4, printed p.457.
-/

public section
open Subgroup Representation
open scoped IsMulCommutative
namespace Representation.ExtraspecialInvertedCenterDegree

/-- A faithful binary representation containing an extraspecial seven-group
with an inverted center has degree at least forty-two. -/
theorem fortyTwo_le_finrank
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    (P : Subgroup G) [IsExtraspecial 7 P] (hP : Nat.card P = 7 ^ 3)
    (t : G) (ht : IsInvolution t)
    (hinv : ∀ z : center P, t * (z : G) * t⁻¹ = (z : G)⁻¹) :
    42 ≤ Module.finrank (ZMod 2) V := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.elementary (V := V)
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let Z : Subgroup G := (center P).map P.subtype
  let W : Subgroup (Multiplicative V) := commutatorAction Z (Multiplicative V)
  have hZ : Nat.card Z = 7 := by
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact IsExtraspecial.center_order_p 7 P
  have hn : P ≤ normalizer (Z : Set G) := by
    have h := (center P).le_normalizer_map P.subtype
    simpa only [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, P.range_subtype] using h
  let : IsInvariant P (Multiplicative V) W :=
    commutatorAction_isInvariant_of_normalizing_actor P Z hn
  let : IsElementaryAbelian 2 W := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun w =>
      Subtype.ext (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (Multiplicative V)) w) }
  let τ := ofElementaryAbelianAction (A := P) (G := W) (p := 2)
  let : FiniteDimensional (ZMod 2) (Additive W) := Module.Finite.of_finite
  have hcop : Nat.Coprime (Nat.card Z) (Nat.card (Multiplicative V)) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 (Multiplicative V)).exists_card_eq
    rw [hZ, hn]
    exact (by decide : Nat.Coprime 7 2).pow_right n
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := Multiplicative V) (A := Z)
      (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop inferInstance
  have hfix : invariants (τ.comp (center P).subtype) = ⊥ := by
    apply bot_unique
    intro w hw
    have hwZ : (w.toMul : Multiplicative V) ∈ FixedPoints.subgroup Z (Multiplicative V) := by
      rintro ⟨z, hz⟩
      obtain ⟨z, hz, rfl⟩ := hz
      exact congrArg (fun u : Additive W => (u.toMul : Multiplicative V)) (hw ⟨z, hz⟩)
    have hz := hcompl.disjoint.le_bot ⟨hwZ, w.toMul.property⟩
    exact Subtype.ext hz
  have hdiv : 21 ∣ Module.finrank (ZMod 2) (Additive W) := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_seven, Nat.reduceMul] using
      BinaryCoprimeDegree.extraspecial_degree_dvd_finrank (by decide : 7 ≠ 2) τ hP hfix
  have hW : W ≠ ⊥ := by
    intro he
    have htriv : ActsTrivially (A := Z) (G := Multiplicative V) :=
      actsTrivially_of_commutatorAction_eq_bot he
    have hzb : Z = ⊥ := by
      apply bot_unique
      intro z hz
      apply hf
      ext v
      rw [map_one]
      exact congrArg Multiplicative.toAdd (htriv ⟨z, hz⟩ (Multiplicative.ofAdd v))
    rw [hzb, Subgroup.card_bot] at hZ
    norm_num at hZ
  have hinvZ : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹ := by
    rintro z ⟨z, hz, rfl⟩
    exact hinv ⟨z, hz⟩
  obtain ⟨hsq, _, _⟩ := invertedOddSubgroup_support_card_data
    (W := Multiplicative V) Z (by rw [hZ]; decide) t ht hinvZ
  let D := commutatorSubgroup (zpowers t) (Multiplicative V) W
  obtain ⟨k, hk⟩ := ((IsElementaryAbelian.isPGroup 2 (Multiplicative V)).to_subgroup D).exists_card_eq
  have hc : Nat.card W = 2 ^ Module.finrank (ZMod 2) (Additive W) := by
    rw [← Nat.card_congr (Additive.toMul : Additive W ≃ W)]
    simpa only [Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive W))
  have heven : Module.finrank (ZMod 2) (Additive W) = 2 * k := by
    change Nat.card W = Nat.card D ^ 2 at hsq
    rw [hc, hk, ← pow_mul] at hsq
    have hh := Nat.pow_right_injective (by decide : 2 ≤ 2) hsq
    omega
  have hpos : 0 < Module.finrank (ZMod 2) (Additive W) := by
    have hcard : 1 < Nat.card W :=
      Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot W).mpr hW)
    rw [hc] at hcard
    by_contra hh
    have hh' : Module.finrank (ZMod 2) (Additive W) = 0 := by omega
    simp [hh'] at hcard
  have hle : Module.finrank (ZMod 2) (Additive W) ≤ Module.finrank (ZMod 2) V := by
    have hcard := Nat.card_le_card_of_injective W.subtype W.subtype_injective
    rw [hc] at hcard
    have hv : Nat.card (Multiplicative V) = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative V ≃ V)]
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V))
    rw [hv] at hcard
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  omega
end Representation.ExtraspecialInvertedCenterDegree
