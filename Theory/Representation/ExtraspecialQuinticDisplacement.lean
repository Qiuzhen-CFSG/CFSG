module

public import Theory.Representation.BinaryCoprimeDegree
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Decomposition
public import Theory.Representation.BinaryOffender.PermutationConjugacy
public import Theory.Representation.BinaryOffender.EquivariantOffender
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic

/-!
# Quintic fixed spaces in extraspecial groups

In a binary representation of an extraspecial five-group, if the center fixes
no vectors, every noncentral element of order five fixes exactly one fifth of
the space. No faithfulness or irreducibility hypothesis is needed.

The six lines of C₅ × C₅ decompose the fixed-space contributions. The central
line contributes zero; conjugation by an element with nontrivial central
commutator permutes the other five lines transitively. Their dimensions are
therefore equal. This is the order-five counterpart of
`ExtraspecialCubicDisplacement`, using the same hyperplane decomposition.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, author preprint pp.16--17; Aschbacher--Smith K.4,
printed p.457. The actual HS consumer is `SourceTwenty.Inner.FiveRestrictions`.
-/

open scoped BigOperators
open Representation Representation.BinaryCoprimeDegree Representation.BinaryOffender
open Subgroup
namespace Representation.BinaryCoprimeDegree
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev C := Multiplicative (ZMod 5)
private abbrev E := C × C
private abbrev T := (⊤ : Subgroup E)
private instance : Fintype T := Fintype.ofEquiv E Subgroup.topEquiv.symm.toEquiv
private abbrev a : C := Multiplicative.ofAdd 1
private abbrev u : E := (a, 1)
private abbrev v : E := (1, a)
private abbrev point (i : Fin 6) : T := ⟨![v, u, u * v, u * v ^ 2, u * v ^ 3, u * v ^ 4] i, mem_top _⟩
private lemma fifth : ∀ c : T, c ^ 5 = 1 := by decide +kernel
private lemma point_ne : ∀ i, point i ≠ 1 := by decide +kernel
private lemma points_notpowers : ∀ i j, i ≠ j → ∀ n : Fin 5, point i ≠ point j ^ (n : ℕ) := by
  decide +kernel
-- Every vector in the twenty-five-element plane lies on one of its six lines.
private lemma points_cover : ∀ c : T, ∃ i : Fin 6, ∃ n : Fin 5, point i ^ (n : ℕ) = c := by
  decide +kernel
private lemma point_order (i : Fin 6) : orderOf (point i) = 5 := orderOf_eq_prime (fifth _) (point_ne i)
private lemma cardT : Nat.card T = 25 := by rw [Nat.card_eq_fintype_card]; decide +kernel
private noncomputable def line (i : Fin 6) : Subgroup T := zpowers (point i)
private lemma line_card (i : Fin 6) : Nat.card (line i) = 5 := by rw [line, Nat.card_zpowers, point_order]
private lemma line_index (i : Fin 6) : (line i).index = 5 := by
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
private lemma hyperplanes_eq : hyperplanes (⊤ : Subgroup E) 5 = Finset.univ.map ⟨line, line_injective⟩ := by
  classical
  ext H
  simp only [mem_hyperplanes, Finset.mem_map, Finset.mem_univ, true_and]
  constructor
  · intro hH
    have hcard : Nat.card H = 5 := by
      have hh := H.card_mul_index
      rw [hH, cardT] at hh
      omega
    let : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr (by
      intro hh
      simp [hh] at hcard)
    obtain ⟨g, hg⟩ := exists_ne (1 : H)
    have hg' : (g : T) ≠ 1 := fun hh => hg (Subtype.ext hh)
    have horder : orderOf (g : T) = 5 := orderOf_eq_prime (fifth _) hg'
    have hgen : zpowers (g : T) = H :=
      eq_of_le_of_card_ge (zpowers_le.mpr g.property) (by rw [Nat.card_zpowers, horder, hcard])
    obtain ⟨i, n, hn⟩ := points_cover (g : T)
    refine ⟨i, ?_⟩
    have hle : zpowers (g : T) ≤ line i := zpowers_le.mpr (hn ▸ pow_mem (mem_zpowers _) _)
    exact (eq_of_le_of_card_ge hle (by rw [line_card, Nat.card_zpowers, horder])).symm.trans hgen
  · rintro ⟨i, rfl⟩
    exact line_index i
private instance : IsElementaryAbelian 5 T where
  toIsMulCommutative := inferInstance
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fifth

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
-- The central line contributes zero to the hyperplane decomposition.
private lemma dimension_sum (ρ : Representation (ZMod 2) E V)
    (hz : fixedSpace ρ (zpowers v) = ⊥) :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers u)) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 2))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 3))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 4))) := by
  have htop : invariants (ρ.comp (⊤ : Subgroup E).subtype) = ⊥ := by
    apply bot_unique
    rw [← hz]
    intro w hw g
    exact hw ⟨g, mem_top _⟩
  have hm (i : Fin 6) : hyperplaneMultiplicity ρ (⊤ : Subgroup E) (line i) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers ((point i : T) : E))) := by
    unfold hyperplaneMultiplicity
    rw [htop, finrank_bot, Nat.sub_zero]
    change Module.finrank (ZMod 2) (fixedSpace (ρ.comp (⊤ : Subgroup E).subtype) (line i)) = _
    rw [fixedSpace_comp_map, line, MonoidHom.map_zpowers]
    rfl
  have h := hyperplane_dimension_sum ρ (p := 5) (by decide) (⊤ : Subgroup E)
  rw [htop, finrank_bot, Nat.add_zero] at h
  unfold hyperplaneDimensionSum at h
  rw [hyperplanes_eq, Finset.sum_map] at h
  change (∑ i : Fin 6, hyperplaneMultiplicity ρ (⊤ : Subgroup E) (line i)) = _ at h
  simp_rw [hm] at h
  simp only [Fin.sum_univ_succ] at h
  change Module.finrank (ZMod 2) (fixedSpace ρ (zpowers v)) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers u)) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v))) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 2))) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 3))) +
    (Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (u * v ^ 4))) + 0))))) =
    Module.finrank (ZMod 2) V at h
  have hzdim : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers v)) = 0 := by
    rw [hz]
    exact finrank_bot _ _
  rw [hzdim, zero_add] at h
  omega

private lemma a_order : orderOf a = 5 := orderOf_eq_prime (by decide +kernel) (by decide +kernel)
private lemma genC (c : C) : c ∈ zpowers a :=
  mem_zpowers_of_prime_card (p := 5) (by rw [Nat.card_eq_fintype_card]; decide +kernel) (by decide +kernel)
private noncomputable def fifthHom {P : Type*} [Group P] (x : P) (hx : x ^ 5 = 1) : C →* P :=
  monoidHomOfForallMemZpowers genC (by rw [a_order]; exact orderOf_dvd_of_pow_eq_one hx)
private lemma fifthHom_a {P : Type*} [Group P] (x : P) (hx : x ^ 5 = 1) : fifthHom x hx a = x :=
  monoidHomOfForallMemZpowers_apply_gen _ _
private lemma fifthHom_mem_center {P : Type*} [Group P] (z : P) (hz : z ^ 5 = 1)
    (hzc : z ∈ center P) (c : C) : fifthHom z hz c ∈ center P := by
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (genC c)
  rw [← hn, map_zpow, fifthHom_a]
  exact zpow_mem hzc n
private noncomputable def planeHom {P : Type*} [Group P] (x z : P) (hx : x ^ 5 = 1)
    (hz : z ^ 5 = 1) (hzc : z ∈ center P) : E →* P :=
  (fifthHom x hx).noncommCoprod (fifthHom z hz) (fun _ c =>
    (Subgroup.mem_center_iff.mp (fifthHom_mem_center z hz hzc c) _))
private lemma planeHom_u {P : Type*} [Group P] (x z : P) (hx : x ^ 5 = 1)
    (hz : z ^ 5 = 1) (hzc : z ∈ center P) : planeHom x z hx hz hzc u = x := by
  change fifthHom x hx a * fifthHom z hz 1 = x
  rw [fifthHom_a, map_one, mul_one]
private lemma planeHom_v {P : Type*} [Group P] (x z : P) (hx : x ^ 5 = 1)
    (hz : z ^ 5 = 1) (hzc : z ∈ center P) : planeHom x z hx hz hzc v = z := by
  change fifthHom x hx 1 * fifthHom z hz a = z
  rw [fifthHom_a, map_one, one_mul]
private lemma fixed_dimension_sum {P : Type*} [Group P] (ρ : Representation (ZMod 2) P V)
    (x z : P) (hx : x ^ 5 = 1) (hz : z ^ 5 = 1) (hzc : z ∈ center P)
    (hfix : fixedSpace ρ (zpowers z) = ⊥) :
    Module.finrank (ZMod 2) V =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z ^ 2))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z ^ 3))) +
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z ^ 4))) := by
  let f := planeHom x z hx hz hzc
  have hf1 : f u = x := planeHom_u ..
  have hf2 : f v = z := planeHom_v ..
  have h := dimension_sum (ρ.comp f) (by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers, hf2]
    exact hfix)
  have hd (g : E) : Module.finrank (ZMod 2) (fixedSpace (ρ.comp f) (zpowers g)) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (f g))) := by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers]
  rw [hd, hd, hd, hd, hd] at h
  rw [hf1, map_mul, hf1, hf2, map_mul, map_pow, hf1, hf2,
    map_mul, map_pow, hf1, hf2, map_mul, map_pow, hf1, hf2] at h
  exact h

open scoped commutatorElement
private lemma central_conjugates {P : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    (x : P) (hxc : x ∉ center P) :
    ∃ y z : P, z ∈ center P ∧ z ^ 5 = 1 ∧ zpowers z = center P ∧
      ∀ n : ℕ, y ^ n * x * (y ^ n)⁻¹ = x * z ^ n := by
  obtain ⟨y, hy⟩ : ∃ y : P, y * x ≠ x * y := by
    simpa only [Subgroup.mem_center_iff, not_forall] using hxc
  let z := ⁅y, x⁆
  have hzne : z ≠ 1 := fun hh => hy (commutatorElement_eq_one_iff_mul_comm.mp hh)
  have hzc : z ∈ center P :=
    commutatorElement_mem_center_of_commutator_le_center_local
      (commutator_le_center_of_isExtraspecial_local (q := 5)) y x
  have hz5 : z ^ 5 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨z, hzc⟩ : center P))
    rw [IsExtraspecial.center_order_p 5 P] at hh
    exact congrArg Subtype.val hh
  have hZ : zpowers z = center P := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr hzc)
    rw [IsExtraspecial.center_order_p 5 P, Nat.card_zpowers, orderOf_eq_prime hz5 hzne]
  have hc (g : P) : g * z = z * g := Subgroup.mem_center_iff.mp hzc g
  have hyx : y * x * y⁻¹ = x * z := by
    rw [hc x]
    simp [z, commutatorElement_def, mul_assoc]
  refine ⟨y, z, hzc, hz5, hZ, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      y ^ (n + 1) * x * (y ^ (n + 1))⁻¹ =
          y * (y ^ n * x * (y ^ n)⁻¹) * y⁻¹ := by group
      _ = y * (x * z ^ n) * y⁻¹ := by rw [ih]
      _ = (y * x * y⁻¹) * z ^ n := by
        have hzcomm := (Subgroup.mem_center_iff.mp (pow_mem hzc n) y⁻¹)
        calc
          _ = y * x * (z ^ n * y⁻¹) := by group
          _ = y * x * (y⁻¹ * z ^ n) := by rw [hzcomm]
          _ = _ := by group
      _ = x * z ^ (n + 1) := by rw [hyx, pow_succ']; group

omit [FiniteDimensional (ZMod 2) V] in
private lemma fixed_finrank_conj {P : Type*} [Group P] (ρ : Representation (ZMod 2) P V)
    (g x : P) :
    Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (g * x * g⁻¹))) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) := by
  have h := (fixedSpaceConjEquiv ρ (zpowers x) g).finrank_eq
  rw [MonoidHom.map_zpowers] at h
  exact h.symm

/-- A noncentral five-element fixes exactly one fifth of a binary module
whose central fixed space is zero. -/
public theorem extraspecial_quintic_fixed_finrank
    {P : Type*} [Group P] [Finite P] [IsExtraspecial 5 P]
    (ρ : Representation (ZMod 2) P V)
    (hfix : invariants (ρ.comp (center P).subtype) = ⊥)
    {x : P} (hx : orderOf x = 5) (hxc : x ∉ center P) :
    Module.finrank (ZMod 2) V = 5 * Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) := by
  obtain ⟨y, z, hzc, hz5, hZ, hy⟩ := central_conjugates x hxc
  have hzfix : fixedSpace ρ (zpowers z) = ⊥ := by rw [hZ]; exact hfix
  have h := fixed_dimension_sum ρ x z (hx ▸ pow_orderOf_eq_one x) hz5 hzc hzfix
  have he (n : ℕ) : Module.finrank (ZMod 2) (fixedSpace ρ (zpowers (x * z ^ n))) =
      Module.finrank (ZMod 2) (fixedSpace ρ (zpowers x)) := by
    rw [← hy n]
    exact fixed_finrank_conj ρ (y ^ n) x
  have he1 := he 1
  rw [pow_one] at he1
  rw [he1, he 2, he 3, he 4] at h
  omega
end Representation.BinaryCoprimeDegree
