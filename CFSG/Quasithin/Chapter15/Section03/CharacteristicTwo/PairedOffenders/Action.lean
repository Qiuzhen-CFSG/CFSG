module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.Representation.BinaryOffender.Basic

/-!
# Transport from the natural eight action to actual centralizers

The coordinates in `NaturalEightAction` identify the fixed vectors of every
action image with the actual relative centralizer in the module. Cardinalities
then identify logarithmic subgroup ranks with fixed-space dimensions. Restricting
the actor to a local overgroup gives exactly the codimension expression used by
the paired rank inequality, without asserting surjectivity of the restricted
parabolic action onto S8.

No module rank or fixed codimension is assumed. In particular the module order
64 is obtained from the even-weight permutation section modulo constants.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.32(1),(5) and the proof of 15.3.25, printed pp.1132–1134.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
open Subgroup Representation.BinaryOffender BinaryPermutation
variable {G : Type*} [Group G] {I U : Subgroup G}
namespace NaturalEightAction
variable (d : NaturalEightAction I U)
include d

/-- Fixed vectors in the given coordinates are the actual relative centralizer. -/
theorem mem_fixedSpace_iff (A : Subgroup I) (u : U) :
    (d.coordinates u).toAdd ∈ fixedSpace (naturalRepresentation (Fin 8)) (A.map d.actor) ↔
      (u : G) ∈ centralizer ((A.map I.subtype : Subgroup G) : Set G) := by
  constructor
  · intro hu
    rintro a ⟨b, hb, rfl⟩
    have hh := hu ⟨d.actor b, mem_map_of_mem _ hb⟩
    have hc := d.compatible b u
    have he : U.normalizerMonoidHom ⟨b, d.normalizes b.property⟩ u = u := by
      apply d.coordinates.injective
      rw [hc]
      exact congrArg Multiplicative.ofAdd hh
    have he' := congrArg Subtype.val he
    change (b : G) * (u : G) * (b : G)⁻¹ = u at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro hu
    rintro ⟨a, b, hb, rfl⟩
    have he : U.normalizerMonoidHom ⟨b, d.normalizes b.property⟩ u = u := by
      apply Subtype.ext
      change (b : G) * (u : G) * (b : G)⁻¹ = u
      rw [hu b (mem_map_of_mem _ hb), mul_inv_cancel_right]
    have hc := d.compatible b u
    rw [he] at hc
    exact (congrArg Multiplicative.toAdd hc).symm

/-- The fixed-space calculation uses an equivalence of the actual carriers. -/
noncomputable def fixedSpaceEquiv (A : Subgroup I) :
    fixedSpace (naturalRepresentation (Fin 8)) (A.map d.actor) ≃
      (U ⊓ centralizer ((A.map I.subtype : Subgroup G) : Set G) : Subgroup G) where
  toFun v := ⟨d.coordinates.symm (Multiplicative.ofAdd v.val),
    (d.coordinates.symm (Multiplicative.ofAdd v.val)).property,
    (d.mem_fixedSpace_iff A _).mp (by simp)⟩
  invFun u := ⟨(d.coordinates ⟨u.val, u.property.1⟩).toAdd,
    (d.mem_fixedSpace_iff A _).mpr u.property.2⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv u := by apply Subtype.ext; simp

/-- The natural module has order 64, via the supplied module coordinates. -/
theorem card_module : Nat.card U = 64 := by
  have hdim : Module.finrank (ZMod 2) (natural (Fin 8)) = 6 := by
    simpa using finrank_natural_even (Fin 8) (by decide)
  calc
    Nat.card U = Nat.card (natural (Fin 8)) := Nat.card_congr d.coordinates.toEquiv
    _ = 64 := by rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hdim]; norm_num

/-- The source's module rank is derived from the actual coordinate carrier. -/
theorem rank_module : rank U = 6 := by rw [rank, d.card_module]; rfl

/-- The logarithmic rank of the actual fixed subgroup equals the fixed dimension. -/
theorem rank_fixed (A : Subgroup I) :
    rank (U ⊓ centralizer ((A.map I.subtype : Subgroup G) : Set G)) =
      Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) (A.map d.actor)) := by
  rw [rank, ← Nat.card_congr (d.fixedSpaceEquiv A),
    Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    Nat.log_pow Nat.one_lt_two]

/-- Transport codimensions from the computed representation to conjugation in G. -/
theorem fixedCodim_eq_rank_sub (A : Subgroup I) :
    fixedCodim (naturalRepresentation (Fin 8)) (A.map d.actor) =
      rank U - rank (U ⊓ centralizer ((A.map I.subtype : Subgroup G) : Set G)) := by
  have h := fixedCodim_add_finrank (naturalRepresentation (Fin 8)) (A.map d.actor)
  have hdim : Module.finrank (ZMod 2) (natural (Fin 8)) = 6 := by
    simpa using finrank_natural_even (Fin 8) (by decide)
  rw [d.rank_module, d.rank_fixed]
  rw [hdim] at h
  omega

/-- Trivial permutation action centralizes the genuine module. -/
theorem ker_le_centralizer :
    d.actor.ker.map I.subtype ≤ centralizer (U : Set G) := by
  rintro a ⟨b, hb, rfl⟩ u hu
  have hc := d.compatible b ⟨u, hu⟩
  have hb' : d.actor b = 1 := hb
  rw [hb', map_one] at hc
  have he : U.normalizerMonoidHom ⟨b, d.normalizes b.property⟩ ⟨u, hu⟩ = ⟨u, hu⟩ :=
    d.coordinates.injective hc
  have he' := congrArg Subtype.val he
  change (b : G) * u * (b : G)⁻¹ = u at he'
  exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- Restrict the actor to the local group XS; surjectivity onto S8 is
not asserted for this parabolic restriction. -/
@[expose] def restrictActor (J : Subgroup G) (hJI : J ≤ I) :
    J →* Equiv.Perm (Fin 8) := d.actor.comp (inclusion hJI)

omit d in
private theorem fixed_map (J : Subgroup G) (hUJ : U ≤ J) (A : Subgroup J) :
    ((U.subgroupOf J) ⊓ centralizer (A : Set J)).map J.subtype =
      U ⊓ centralizer ((A.map J.subtype : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy.1, ?_⟩
    rintro a ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (hy.2 b hb)
  · intro hx
    refine ⟨⟨x, hUJ hx.1⟩, ⟨hx.1, ?_⟩, rfl⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 a (mem_map_of_mem _ ha)

/-- The codimension used by the paired rank inequality is computed inside
the actual local group J, where the two conjugate modules are normal. -/
theorem fixedCodim_restrict (J : Subgroup G) (hJI : J ≤ I) (hUJ : U ≤ J)
    (A : Subgroup J) :
    fixedCodim (naturalRepresentation (Fin 8)) (A.map (d.restrictActor J hJI)) =
      rank (U.subgroupOf J) - rank ((U.subgroupOf J) ⊓ centralizer (A : Set J)) := by
  have hm (B : Subgroup J) : rank (B.map J.subtype) = rank B :=
    congrArg (Nat.log 2) (card_map_of_injective J.subtype_injective)
  have h := d.fixedCodim_eq_rank_sub (A.map (inclusion hJI))
  have hmap : (A.map (inclusion hJI)).map I.subtype = A.map J.subtype := by
    rw [map_map]
    rfl
  rw [map_map, hmap] at h
  change fixedCodim (naturalRepresentation (Fin 8)) (A.map (d.restrictActor J hJI)) = _ at h
  have hrU := hm (U.subgroupOf J)
  rw [map_subgroupOf_eq_of_le hUJ] at hrU
  have hrF := hm ((U.subgroupOf J) ⊓ centralizer (A : Set J))
  rw [fixed_map J hUJ A] at hrF
  rw [hrU, hrF] at h
  exact h

end NaturalEightAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo
end
