module

public import Theory.Representation.BinaryOffender.NormalizerRank
public import Theory.GroupTheory.SolvableOuterQuotient


/-!
# Literal involutions above inner automorphisms

In the normalizer of an irreducible binary action, an involution inducing an
inner automorphism belongs to the actual action image. Schur's lemma excludes
centralizing involutions, so the finite centralizer has odd order. The quotient
of the actor by an inner representative has square in the image; odd order
then puts that quotient itself in the image. This removes the scalar ambiguity
without assuming the original action faithful or its image centerless.

The elementary-subgroup equivalence is used for the Schur-linear outer branch
of Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11, internal
pp.31--32, and Aschbacher--Smith K.3.3, printed p.456.
-/

public section

open Subgroup
namespace Representation.SU3.CubicDegree.SchurOuter

private theorem mem_of_inner_of_square_one
    {H : Type*} [Group H] [Finite H] (L : Subgroup H)
    (hc : ∀ x ∈ centralizer (L : Set H), x ^ 2 = 1 → x = 1)
    (t : (normalizer (L : Set H))) (ht : t ^ 2 = 1)
    (hi : L.normalizerMonoidHom t ∈ MulAut.innerSubgroup L) : (t : H) ∈ L := by
  have hodd : Odd (Nat.card (centralizer (L : Set H))) := by
    apply Nat.not_even_iff_odd.mp
    rw [even_iff_two_dvd]
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (L : Set H)) 2 hd
    have hx2 : x ^ 2 = 1 := hx ▸ pow_orderOf_eq_one x
    have hx1 : x = 1 := Subtype.ext (hc x x.property (congrArg Subtype.val hx2))
    simp [hx1] at hx
  obtain ⟨g, hg⟩ := hi
  let g' : normalizer (L : Set H) := ⟨g, L.le_normalizer g.property⟩
  have hg' : L.normalizerMonoidHom g' = MulAut.conj g := by
    ext h
    rfl
  have hk : g'⁻¹ * t ∈ L.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hg', hg, inv_mul_cancel]
  rw [Subgroup.normalizerMonoidHom_ker] at hk
  let c : centralizer (L : Set H) := ⟨(g : H)⁻¹ * (t : H), hk⟩
  have hcomm : Commute (g : H) (t : H) := by
    have hh := congrArg (fun a : MulAut L => (a g : H)) hg
    change (g : H) * g * (g : H)⁻¹ = (t : H) * g * (t : H)⁻¹ at hh
    have he : (t : H) * g * (t : H)⁻¹ = g := by
      simpa using hh.symm
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hc2 : (c : H) ^ 2 ∈ L := by
    change ((g : H)⁻¹ * (t : H)) ^ 2 ∈ L
    rw [hcomm.inv_left.mul_pow, show (t : H) ^ 2 = 1 from congrArg Subtype.val ht,
      mul_one]
    exact L.pow_mem (L.inv_mem g.property) 2
  have hoc : Odd (orderOf c) := hodd.of_dvd_nat (orderOf_dvd_natCard c)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hoc.coprime_two_left
  have hcmem : (c : H) ∈ L := by
    have hh := congrArg (fun x : centralizer (L : Set H) => (x : H)) hm
    exact hh ▸ L.pow_mem hc2 m
  have h := L.mul_mem g.property hcmem
  simpa [c, mul_assoc] using h

open Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (σ : Representation (ZMod 2) G V)

/-- Inner conjugation by an involution determines an operator in the literal image. -/
theorem involution_mem_image_of_inner (hi : σ.IsIrreducible)
    (t : linearNormalizer σ) (ht : t ^ 2 = 1)
    (hinner : (actionImage σ).normalizerMonoidHom t ∈
      MulAut.innerSubgroup (actionImage σ)) :
    t ∈ (actionImage σ).subgroupOf (linearNormalizer σ) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  let τ : Representation (ZMod 2) (Module.End (ZMod 2) V)ˣ V := Units.coeHom _
  let : Representation.IsIrreducible (τ.comp (actionImage σ).subtype) :=
    imageRepresentation_isIrreducible σ hi
  exact mem_of_inner_of_square_one (actionImage σ)
    (fun x hx h2 => BinaryIrreducibleCentralizer.centralizing_square_one_eq_one
      τ (actionImage σ) (fun _ _ h => Units.ext h) h2 hx) t ht hinner

/-- For elementary actors, literal containment is equivalent to inner conjugation. -/
theorem elementary_le_image_iff_inner (hi : σ.IsIrreducible)
    (A : Subgroup (linearNormalizer σ)) (hA : IsElementaryAbelian 2 A) :
    A ≤ (actionImage σ).subgroupOf (linearNormalizer σ) ↔
      ∀ t ∈ A, (actionImage σ).normalizerMonoidHom t ∈
        MulAut.innerSubgroup (actionImage σ) := by
  let : IsElementaryAbelian 2 A := hA
  constructor
  · intro ha t ht
    refine ⟨⟨t, ha ht⟩, ?_⟩
    ext g
    rfl
  · intro ha t ht
    exact involution_mem_image_of_inner σ hi t
      (elemPow_eq_one_of_isElementaryAbelian t ht) (ha t ht)

end Representation.SU3.CubicDegree.SchurOuter
