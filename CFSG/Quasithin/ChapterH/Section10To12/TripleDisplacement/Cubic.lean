module
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.Basic
public import CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement.AmbientActors
public import Theory.Representation.ExtraspecialCubicDisplacement

/-!
# Cubic actors and involution displacement in the genuine triple Mathieu setup

Place each noncentral order-three actor in an actual Sylow subgroup of L.
Its extraspecial center is Z(L), whose fixed space vanishes by ambient
irreducibility. The generic cubic calculation then gives displacement
`4 * (dim U / 6)`. Central cubic actors move the whole module. Every ambient
involution inverts a cubic actor, so the commutator rank inequality gives
`dim U ≤ 3 * fixedCodim ρ (zpowers t)`. This argument needs no minimum-degree
or uniqueness theorem and applies to every permitted outer extension.

Source: Aschbacher–Smith H.12.1, proof on printed p.394 (PDF p.405).
The resulting degree bound supplies the corrected U-displacement hypothesis
in clause (3), and the dimension-twelve specialization supplies the involution
lower bound used in the local argument.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- Every noncentral cubic actor in L has the extraspecial displacement. -/
theorem noncentral_three_fixedCodim (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (x : L) (hx : orderOf x = 3)
    (hxc : x ∉ center L) :
    fixedCodim ρ (zpowers (x : G)) = 4 * (Module.finrank (ZMod 2) V / 6) := by
  have hp : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨hc, he, hz⟩ := sylow_three_structure hL P
  let : IsExtraspecial 3 (P : Subgroup L) := he
  let y : (P : Subgroup L) := ⟨x, hP (mem_zpowers x)⟩
  have hy : orderOf y = 3 := (Subgroup.orderOf_coe y).symm.trans hx
  have hyc : y ∉ center (P : Subgroup L) := by
    intro h
    apply hxc
    rw [← hz]
    exact mem_map_of_mem (P : Subgroup L).subtype h
  have hd := BinaryCoprimeDegree.extraspecial_twentySeven_fixedCodim_zpowers
    (ρ.comp (L.subtype.comp (P : Subgroup L).subtype)) hc
    (sylow_center_invariants_eq_bot L hL hF P hz ρ hρ) hy hyc
  unfold fixedCodim at hd ⊢
  rw [fixedSpace_comp_map, MonoidHom.map_zpowers] at hd
  exact hd

/-- The literal restricted action has the same noncentral cubic displacement. -/
theorem noncentral_three_restriction_fixedCodim (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (x : L) (hx : orderOf x = 3)
    (hxc : x ∉ center L) :
    fixedCodim (ρ.comp L.subtype) (zpowers x) = 4 * (Module.finrank (ZMod 2) V / 6) := by
  have hd := noncentral_three_fixedCodim L hL hF ρ hρ x hx hxc
  unfold fixedCodim at hd ⊢
  rwa [fixedSpace_comp_map, MonoidHom.map_zpowers]

/-- Subgroups of order three distinct from Z(L) satisfy the same formula. -/
theorem noncentral_three_subgroup_fixedCodim (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (X : Subgroup L) (hX : Nat.card X = 3)
    (hXZ : X ≠ center L) :
    fixedCodim (ρ.comp L.subtype) X = 4 * (Module.finrank (ZMod 2) V / 6) := by
  let : Nontrivial X := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hx1 : (x : L) ≠ 1 := fun h => hx (Subtype.ext h)
  have hx3 : orderOf (x : L) = 3 := orderOf_eq_prime (by
    have h := pow_card_eq_one' (x := x)
    rw [hX] at h
    exact congrArg Subtype.val h) hx1
  have hgen : zpowers (x : L) = X := eq_of_le_of_card_ge
    (zpowers_le.mpr x.property) (by rw [Nat.card_zpowers, hx3, hX])
  have hxc : (x : L) ∉ center L := by
    intro h
    apply hXZ
    apply eq_of_le_of_card_ge
    · rw [← hgen]
      exact zpowers_le.mpr h
    · rw [hX, hL.center_card]
  rw [← hgen]
  exact noncentral_three_restriction_fixedCodim L hL hF ρ hρ x hx3 hxc

/-- Central cubic actors move the whole space; all others move two thirds. -/
theorem four_mul_sixth_le_fixedCodim_three (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (x : G) (hx : orderOf x = 3) :
    4 * (Module.finrank (ZMod 2) V / 6) ≤ fixedCodim ρ (zpowers x) := by
  have hm := AmbientActors.odd_prime_mem L hL hF Nat.prime_three (by decide) x hx
  let y : L := ⟨x, hm⟩
  have hy : orderOf y = 3 := (Subgroup.orderOf_coe y).symm.trans hx
  by_cases hxc : y ∈ center L
  · rw [central_three_fixedCodim L hL hF ρ hρ x
      (mem_map_of_mem L.subtype hxc) hx]
    omega
  · exact le_of_eq (noncentral_three_fixedCodim L hL hF ρ hρ y hy hxc).symm

/-- Every ambient involution moves at least one third of the module.
This upper bound on degree is independent of James's minimum-degree theorem. -/
theorem finrank_le_three_mul_fixedCodim_involution (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (t : G) (ht : orderOf t = 2) :
    Module.finrank (ZMod 2) V ≤ 3 * fixedCodim ρ (zpowers t) := by
  obtain ⟨y, _, hy, hi⟩ := AmbientActors.exists_inverted_three L hL hF t ht
  have hlow := four_mul_sixth_le_fixedCodim_three L hL hF ρ hρ y hy
  have hhigh := fixedCodim_three_le_twice_of_inverted ρ y t hy hi
  have hd := six_dvd_finrank L hL hF ρ hρ
  omega

/-- The small-displacement hypothesis in corrected H.12.1(3) gives degree at most twelve. -/
theorem finrank_le_twelve_of_small_involution (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ)
    (hsmall : ∃ t : G, orderOf t = 2 ∧ fixedCodim ρ (zpowers t) ≤ 4) :
    Module.finrank (ZMod 2) V ≤ 12 := by
  obtain ⟨t, ht, hs⟩ := hsmall
  have hb := finrank_le_three_mul_fixedCodim_involution L hL hF ρ hρ t ht
  omega

/-- In dimension twelve every involution moves at least four dimensions. -/
theorem four_le_fixedCodim_involution (L : Subgroup G) (hL : IsTripleM22 L)
    (hF : generalizedFitting G = L)
    (ρ : Representation (ZMod 2) G V) [ρ.IsIrreducible]
    (hρ : Function.Injective ρ) (hd : Module.finrank (ZMod 2) V = 12)
    (t : G) (ht : orderOf t = 2) : 4 ≤ fixedCodim ρ (zpowers t) := by
  have hb := finrank_le_three_mul_fixedCodim_involution L hL hF ρ hρ t ht
  omega
end CFSG.Quasithin.ChapterH.Section10To12.TripleDisplacement
