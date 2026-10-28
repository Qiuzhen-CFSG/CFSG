module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Decomposition
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.EquivariantOffender
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic

/-!
# Noncentral cubic displacement in extraspecial groups

For a binary representation of an extraspecial group of order 27, vanishing
of the central fixed space implies that every noncentral cubic subgroup fixes
one third of the module and has fixed codimension `4 * (dim V / 6)`.
Neither faithfulness nor irreducibility of the representation is required.

Choose a nontrivial central commutator `z = [y,x]`. Pull the action back along
`C₃ × C₃ → P`, with generators mapping to `x` and `z`. The four-line
hyperplane decomposition has zero contribution from the central line, and
conjugation by `y` identifies the other three fixed dimensions. This gives
`dim V = 3 * dim C_V(x)`; the existing divisibility by six finishes the formula.
The finite plane is enumerated by small kernel-checked computations; no
character-table or displacement value is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, H.12.1,
proof on printed p.394 (PDF p.405 of the combined 1 March 2004 manuscript).
This module supplies the generic calculation; the ambient triple-M₂₂ source
assembly remains in Chapter H.
-/

open scoped BigOperators
open Representation Representation.BinaryCoprimeDegree Representation.BinaryOffender
open Subgroup
namespace Representation.BinaryCoprimeDegree
private abbrev C := Multiplicative (ZMod 3)
private abbrev E := C × C
private abbrev T := (⊤ : Subgroup E)
private instance : Fintype T := Fintype.ofEquiv E Subgroup.topEquiv.symm.toEquiv
private abbrev a : C := Multiplicative.ofAdd 1
private abbrev u : E := (a, 1)
private abbrev v : E := (1, a)
private abbrev point (i : Fin 4) : T := ⟨![v, u, u * v, u * v ^ 2] i, mem_top _⟩
private lemma cube : ∀ c : T, c ^ 3 = 1 := by decide +kernel
private lemma point_ne : ∀ i, point i ≠ 1 := by decide +kernel
private lemma points_notpowers : ∀ i j, i ≠ j → ∀ n : Fin 3, point i ≠ point j ^ (n : ℕ) := by
  decide +kernel
-- Every vector in the nine-element plane lies on one of its four lines.
private lemma points_cover : ∀ c : T, ∃ i : Fin 4, ∃ n : Fin 3, point i ^ (n : ℕ) = c := by
  decide +kernel
private lemma point_order (i : Fin 4) : orderOf (point i) = 3 := orderOf_eq_prime (cube _) (point_ne i)
private lemma cardT : Nat.card T = 9 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private noncomputable def line (i : Fin 4) : Subgroup T := zpowers (point i)
private lemma line_card (i : Fin 4) : Nat.card (line i) = 3 := by rw [line, Nat.card_zpowers, point_order]
private lemma line_index (i : Fin 4) : (line i).index = 3 := by
  have h := (line i).card_mul_index
  rw [line_card, cardT] at h
  omega
private lemma line_injective : Function.Injective line := by
  intro i j hij
  by_contra hn
  have hm : point i ∈ zpowers (point j) := by
    change point i ∈ line j
    rw [← hij]
    exact mem_zpowers _
  obtain ⟨n, hnlt, hpow⟩ := Finset.mem_image.mp ((mem_zpowers_iff_mem_range_orderOf).mp hm)
  rw [Finset.mem_range, point_order] at hnlt
  exact points_notpowers i j hn ⟨n, hnlt⟩ hpow.symm
private lemma hyperplanes_eq : hyperplanes (⊤ : Subgroup E) 3 = Finset.univ.map ⟨line, line_injective⟩ := by
  classical
  ext H
  simp only [mem_hyperplanes, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hH
    have hcard : Nat.card H = 3 := by
      have hh := H.card_mul_index
      rw [hH, cardT] at hh
      omega
    let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr (by
      intro hh
      simp [hh] at hcard)
    obtain ⟨g, hg⟩ := exists_ne (1 : H)
    have hg' : (g : T) ≠ 1 := fun hh => hg (Subtype.ext hh)
    have horder : orderOf (g : T) = 3 := orderOf_eq_prime (cube _) hg'
    have hgen : zpowers (g : T) = H :=
      eq_of_le_of_card_ge (zpowers_le.mpr g.property) (by rw [Nat.card_zpowers, horder, hcard])
    obtain ⟨i, n, hn⟩ := points_cover (g : T)
    refine ⟨i, ?_⟩
    have hle : zpowers (g : T) ≤ line i := zpowers_le.mpr (hn ▸ pow_mem (mem_zpowers _) _)
    exact (eq_of_le_of_card_ge hle (by rw [line_card, Nat.card_zpowers, horder])).symm.trans hgen
  · rintro ⟨i, rfl⟩
    exact line_index i
private instance : IsElementaryAbelian 3 T where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr cube

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
-- The central line contributes zero to the hyperplane decomposition.
private lemma dimension_sum (ρ : Representation (ZMod 2) E V)
    (hz : fixedSpace ρ (zpowers v) = ⊥) :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers u)) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 2))) := by
  have htop : invariants (ρ.comp (⊤ : Subgroup E).subtype) = ⊥ := by
    apply bot_unique
    rw [← hz]
    intro w hw g
    exact hw ⟨g, mem_top _⟩
  have hm (i : Fin 4) : hyperplaneMultiplicity ρ (⊤ : Subgroup E) (line i) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers ((point i : T) : E))) := by
    unfold hyperplaneMultiplicity
    rw [htop, finrank_bot, Nat.sub_zero]
    change Module.finrank (ZMod 2) (fixedSpace (ρ.comp (⊤ : Subgroup E).subtype) (line i)) = _
    rw [fixedSpace_comp_map, line, MonoidHom.map_zpowers]
    rfl
  have h := hyperplane_dimension_sum ρ (p := 3) (by decide) (⊤ : Subgroup E)
  rw [htop, finrank_bot, Nat.add_zero] at h
  unfold hyperplaneDimensionSum at h
  rw [hyperplanes_eq, Finset.sum_map] at h
  change (∑ i : Fin 4, hyperplaneMultiplicity ρ (⊤ : Subgroup E) (line i)) = _ at h
  simp_rw [hm] at h
  simp only [Fin.sum_univ_succ] at h
  change Module.finrank (ZMod 2) (fixedSpace ρ (zpowers v)) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers u)) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v))) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 2))) + 0))) =
    Module.finrank (ZMod 2) V at h
  have hzdim : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers v)) = 0 := by
    rw [hz]
    exact finrank_bot _ _
  rw [hzdim, zero_add] at h
  omega

private lemma a_order : orderOf a = 3 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private lemma genC (c : C) : c ∈ zpowers a :=
  mem_zpowers_of_prime_card (p := 3) (by rw [Nat.card_eq_fintype_card]; decide +kernel) (by decide +kernel)
private noncomputable def cubeHom {P : Type*} [Group P] (x : P) (hx : x ^ 3 = 1) : C →* P :=
  monoidHomOfForallMemZpowers genC (by rw [a_order]; exact orderOf_dvd_of_pow_eq_one hx)
private lemma cubeHom_a {P : Type*} [Group P] (x : P) (hx : x ^ 3 = 1) : cubeHom x hx a = x :=
  monoidHomOfForallMemZpowers_apply_gen _ _
private lemma cubeHom_mem_center {P : Type*} [Group P] (z : P) (hz : z ^ 3 = 1)
    (hzc : z ∈ center P) (c : C) : cubeHom z hz c ∈ center P := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (genC c)
  rw [← hn, map_zpow, cubeHom_a]
  exact zpow_mem hzc n
private noncomputable def planeHom {P : Type*} [Group P] (x z : P) (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (hzc : z ∈ center P) : E →* P :=
  (cubeHom x hx).noncommCoprod (cubeHom z hz) (fun _ c =>
    (Subgroup.mem_center_iff.mp (cubeHom_mem_center z hz hzc c) _))
private lemma planeHom_u {P : Type*} [Group P] (x z : P) (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (hzc : z ∈ center P) : planeHom x z hx hz hzc u = x := by
  change cubeHom x hx a * cubeHom z hz 1 = x
  rw [cubeHom_a, map_one, mul_one]
private lemma planeHom_v {P : Type*} [Group P] (x z : P) (hx : x ^ 3 = 1)
    (hz : z ^ 3 = 1) (hzc : z ∈ center P) : planeHom x z hx hz hzc v = z := by
  change cubeHom x hx 1 * cubeHom z hz a = z
  rw [cubeHom_a, map_one, one_mul]
private lemma fixed_dimension_sum {P : Type*} [Group P] (ρ : Representation (ZMod 2) P V)
    (x z : P) (hx : x ^ 3 = 1) (hz : z ^ 3 = 1) (hzc : z ∈ center P)
    (hfix : fixedSpace ρ (zpowers z) = ⊥) :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z ^ 2))) := by
  let f := planeHom x z hx hz hzc
  have hf1 : f u = x := planeHom_u ..
  have hf2 : f v = z := planeHom_v ..
  have h := dimension_sum (ρ.comp f) (by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers, hf2]
    exact hfix)
  have hd (g : E) : Module.finrank (ZMod 2) (fixedSpace (ρ.comp f) (zpowers g)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (f g))) := by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
  rw [hd, hd, hd] at h
  rw [hf1, map_mul, hf1, hf2, map_mul, map_pow, hf1, hf2] at h
  exact h

open scoped commutatorElement
-- A nontrivial commutator generates the cubic center and rotates the other lines.
private lemma central_conjugates {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    (x : P) (hxc : x ∉ center P) :
    ∃ y z : P, z ∈ center P ∧ z ^ 3 = 1 ∧ zpowers z = center P ∧
      y * x * y⁻¹ = x * z ∧ y ^ 2 * x * (y ^ 2)⁻¹ = x * z ^ 2 := by
  obtain ⟨y, hy⟩ : ∃ y : P, y * x ≠ x * y := by
    simpa only [Subgroup.mem_center_iff, not_forall] using hxc
  let z := ⁅y, x⁆
  have hzne : z ≠ 1 := fun hh => hy (commutatorElement_eq_one_iff_mul_comm.mp hh)
  have hzc : z ∈ center P :=
    commutatorElement_mem_center_of_commutator_le_center_local
      (commutator_le_center_of_isExtraspecial_local (q := 3)) y x
  have hz3 : z ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z, hzc⟩ : center P))
    rw [IsExtraspecial.center_order_p 3 P] at hh
    exact congrArg Subtype.val hh
  have hZ : zpowers z = center P := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzc)
    rw [IsExtraspecial.center_order_p 3 P, Nat.card_zpowers, orderOf_eq_prime hz3 hzne]
  have hc (g : P) : g * z = z * g := Subgroup.mem_center_iff.mp hzc g
  have hyx : y * x * y⁻¹ = x * z := by
    rw [hc x]
    simp [z, commutatorElement_def, mul_assoc]
  refine ⟨y, z, hzc, hz3, hZ, hyx, ?_⟩
  calc
    y ^ 2 * x * (y ^ 2)⁻¹ = y * (y * x * y⁻¹) * y⁻¹ := by simp only [pow_two, mul_inv_rev]; group
    _ = y * (x * z) * y⁻¹ := by rw [hyx]
    _ = y * x * (z * y⁻¹) := by group
    _ = y * x * (y⁻¹ * z) := by rw [hc y⁻¹]
    _ = (y * x * y⁻¹) * z := by group
    _ = x * z ^ 2 := by rw [hyx]; simp only [pow_two, mul_assoc]

omit [FiniteDimensional (ZMod 2) V] in
private lemma fixed_finrank_conj {P : Type*} [Group P] (ρ : Representation (ZMod 2) P V)
    (g x : P) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (g * x * g⁻¹))) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) := by
  have h := (fixedSpaceConjEquiv ρ (zpowers x) g).finrank_eq
  rw [MonoidHom.map_zpowers] at h
  exact h.symm

/-- A noncentral cubic element fixes exactly one third of a binary module
on which the center of an extraspecial 3-group has no fixed vectors.
The representation need not be faithful or irreducible. -/
public theorem extraspecial_cubic_fixed_finrank
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    (ρ : Representation (ZMod 2) P V)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥)
    {x : P} (hx : orderOf x = 3) (hxc : x ∉ center P) :
    Module.finrank (ZMod 2) V = 3 * Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) := by
  obtain ⟨y, z, hzc, hz3, hZ, hy, hy2⟩ := central_conjugates x hxc
  have hzfix : fixedSpace ρ (zpowers z) = ⊥ := by rw [hZ]; exact hfix
  have h := fixed_dimension_sum ρ x z (hx ▸ pow_orderOf_eq_one x) hz3 hzc hzfix
  have h1 := fixed_finrank_conj ρ y x
  have h2 := fixed_finrank_conj ρ (y ^ 2) x
  rw [hy] at h1
  rw [hy2] at h2
  omega

/-- A noncentral element of order three in an extraspecial group of order 27
has displacement `4k` on a binary module of dimension `6k` with zero central
fixed space. -/
public theorem extraspecial_twentySeven_fixedCodim_zpowers
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = 27)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥)
    {x : P} (hx : orderOf x = 3) (hxc : x ∉ center P) :
    fixedCodim ρ (zpowers x) = 4 * (Module.finrank (ZMod 2) V / 6) := by
  have hd := six_dvd_finrank_of_extraspecial_twentySeven ρ hcard hfix
  have hf := extraspecial_cubic_fixed_finrank ρ hfix hx hxc
  have hc := fixedCodim_add_finrank ρ (zpowers x)
  omega

/-- The subgroup formulation of the extraspecial cubic displacement formula:
every subgroup of order three distinct from the center has fixed codimension
four times one sixth of the dimension. -/
public theorem extraspecial_twentySeven_fixedCodim_subgroup
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 3 P]
    (ρ : Representation (ZMod 2) P V) (hcard : Nat.card P = 27)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥)
    (X : Subgroup P) (hX : Nat.card X = 3) (hXZ : X ≠ center P) :
    fixedCodim ρ X = 4 * (Module.finrank (ZMod 2) V / 6) := by
  have hXbot : X ≠ ⊥ := by intro hh; simp [hh] at hX
  let : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hXbot
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  have hx1 : (x : P) ≠ 1 := fun hh => hx (Subtype.ext hh)
  have hx3 : (x : P) ^ 3 = 1 := by
    have hh := pow_card_eq_one' (x := x)
    rw [hX] at hh
    exact congrArg Subtype.val hh
  have hxo : orderOf (x : P) = 3 := orderOf_eq_prime hx3 hx1
  have hgen : zpowers (x : P) = X := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr x.property)
    rw [Nat.card_zpowers, hX, hxo]
  have hxc : (x : P) ∉ center P := by
    intro hcenter
    apply hXZ
    apply eq_of_le_of_card_ge
    · rw [← hgen]
      exact zpowers_le.mpr hcenter
    · rw [hX, IsExtraspecial.center_order_p 3 P]
  rw [← hgen]
  exact extraspecial_twentySeven_fixedCodim_zpowers ρ hcard hfix hxo hxc
end Representation.BinaryCoprimeDegree
