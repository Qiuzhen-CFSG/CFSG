module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.SingularInvolutionPairs
public import Theory.GroupTheory.OrderThreeNormalizer.Cardinality
public import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.Tactic.NormNum

/-!
# A cubic subgroup centralized by a singular actor in O₄⁺(2)

In the concrete S₃ wreath C₂ action on the binary plus space, every
nonidentity actor with totally singular displacement swaps the two
anisotropic planes. A cubic subgroup centralized by such an actor therefore
has nontrivial projection on both planes. It is one of the diagonal and
antidiagonal cubic lines.

For these two literal lines, explicit commuting S₃ homomorphisms identify
the normalizer with S₃×S₃, while a cubic factor and the other S₃ identify
the centralizer with C₃×S₃. Their orders are 36 and 18. The normalizer count
uses the order-three inversion action. The checked finite calculations use
the 72-element wreath model and its explicit six-element factors, never a
subgroup-lattice enumeration. The image wrappers retain the original
faithful action, cubic subgroup and singular actor.

Source: Aschbacher–Smith, Lemma 13.5.15, printed pp.919–920, especially the
orthogonal-action argument establishing clauses (8) and (9). The actual
source constructs the action on U_H/Φ(U_H), the normal cubic image L₁*,
and the nonidentity singular-displacement element from V*.
-/

open Subgroup
namespace BinaryFourPlus.CubicNormalizer
abbrev S3 := Equiv.Perm (Fin 3)
abbrev C3 := Multiplicative (ZMod 3)
private instance : DecidableEq Wreath := (RegularWreathProduct.equivProd S3 C2).injective.decidableEq
private instance : Fintype Wreath := Fintype.ofEquiv _ (RegularWreathProduct.equivProd S3 C2).symm

def cycle : S3 := Equiv.swap 0 1 * Equiv.swap 1 2
def reflection : S3 := Equiv.swap 1 2

def wreathElement (a b : S3) (e : C2) : Wreath := ⟨fun i => if i=1 then a else b,e⟩
def rotation (side : Bool) : Wreath := wreathElement cycle (if side then cycle⁻¹ else cycle) 1
def flip (side : Bool) : Wreath :=
  if side then wreathElement 1 1 swapIndex else wreathElement reflection reflection swapIndex

def factorWord (side : Bool) (p : S3) : Wreath :=
  rotation side ^ (p 0).val * (if Equiv.Perm.sign p = 1 then 1 else flip side)

def factor (side : Bool) : S3 →* Wreath where
  toFun := factorWord side
  map_one' := by cases side <;> decide +kernel
  map_mul' := by cases side <;> decide +kernel

theorem factor_commute (a b : S3) : Commute (factor false a) (factor true b) := by
  change factor false a * factor true b = factor true b * factor false a
  revert a b
  decide +kernel

def full : S3 × S3 →* Wreath := MonoidHom.noncommCoprod (factor false) (factor true) factor_commute

theorem full_injective : Function.Injective full := by decide +kernel

def rotationHom (side : Bool) : C3 →* Wreath where
  toFun i := rotation side ^ i.toAdd.val
  map_one' := by simp
  map_mul' i j := by
    change rotation side ^ (i.toAdd+j.toAdd).val =
      rotation side ^ i.toAdd.val * rotation side ^ j.toAdd.val
    rw [ZMod.val_add, ← pow_add]
    have h : rotation side ^ 3 = 1 := by cases side <;> decide +kernel
    exact (pow_eq_pow_mod _ h).symm

def central (side : Bool) : C3 × S3 →* Wreath :=
  MonoidHom.noncommCoprod (rotationHom side) (factor (!side)) (by
    intro i p
    change rotation side ^ i.toAdd.val * factor (!side) p =
      factor (!side) p * rotation side ^ i.toAdd.val
    have h : ∀ (side : Bool) (i : C3) (p : S3),
        rotation side ^ i.toAdd.val * factor (!side) p =
          factor (!side) p * rotation side ^ i.toAdd.val := by decide +kernel
    exact h side i p)

theorem central_injective (side : Bool) : Function.Injective (central side) := by
  cases side <;> decide +kernel

theorem central_range (side : Bool) :
    (central side).range = centralizer ({rotation side} : Set Wreath) := by
  ext w
  rw [mem_centralizer_singleton_iff]
  change (∃ x, central side x = w) ↔ w * rotation side = rotation side * w
  have h : ∀ (side : Bool) (w : Wreath),
      (∃ x, central side x = w) ↔ w * rotation side = rotation side * w := by decide +kernel
  exact h side w

theorem rotation_order (side : Bool) : orderOf (rotation side) = 3 := by
  apply orderOf_eq_prime
  · cases side <;> decide +kernel
  · cases side <;> decide +kernel

theorem full_normalizes (side : Bool) : full.range ≤ normalizer (zpowers (rotation side) : Set Wreath) := by
  rintro _ ⟨p, rfl⟩
  rw [mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change zpowers (full p * rotation side * (full p)⁻¹) = zpowers (rotation side)
  have h : ∀ (side : Bool) (p : S3 × S3),
      full p * rotation side * (full p)⁻¹ = rotation side ∨
      full p * rotation side * (full p)⁻¹ = (rotation side)⁻¹ := by decide +kernel
  rcases h side p with h | h <;> rw [h]
  exact zpowers_inv

theorem models (side : Bool) :
    Nonempty (normalizer (zpowers (rotation side) : Set Wreath) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    Nonempty (centralizer (zpowers (rotation side) : Set Wreath) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)) := by
  have hc : centralizer (zpowers (rotation side) : Set Wreath) =
      centralizer ({rotation side} : Set Wreath) := by
    rw [zpowers_eq_closure, centralizer_closure]
  let ec := (MonoidHom.ofInjective (central_injective side)).trans
    (MulEquiv.subgroupCongr (central_range side))
  have hC : Nat.card (centralizer ({rotation side} : Set Wreath)) = 18 := by
    rw [← Nat.card_congr ec.toEquiv, Nat.card_prod]
    norm_num [C3, S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hinv : flip side * rotation side * (flip side)⁻¹ = (rotation side)⁻¹ := by
    cases side <;> decide +kernel
  have hN := normalizer_card_of_order_three_inverter (rotation side) (flip side) (rotation_order side) hinv
  rw [hC] at hN
  let f := full.codRestrict (normalizer (zpowers (rotation side) : Set Wreath))
    (fun x => full_normalizes side ⟨x, rfl⟩)
  have hf : Function.Injective f := by
    intro x y hxy
    exact full_injective (congrArg Subtype.val hxy)
  have hcard : Nat.card (S3 × S3) = Nat.card (normalizer (zpowers (rotation side) : Set Wreath)) := by
    rw [hN, Nat.card_prod]
    norm_num [S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  refine ⟨⟨(MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hf,hcard⟩)).symm⟩, ?_⟩
  exact ⟨(MulEquiv.subgroupCongr hc).trans ec.symm⟩

theorem cubic_swap_cases (x s : Wreath) (hx : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hs : s.right ≠ 1) (hcomm : s * x = x * s) :
    ∃ side : Bool, x = rotation side ∨ x = (rotation side)⁻¹ := by
  have h : ∀ (x s : Wreath), x ^ 3 = 1 → x ≠ 1 → s.right ≠ 1 → s*x=x*s →
      ∃ side : Bool, x = rotation side ∨ x = (rotation side)⁻¹ := by decide +kernel
  exact h x s hx hx1 hs hcomm

/-- The original cyclic subgroup is one of the two full-support cubic lines. -/
theorem cyclic_position (A : Subgroup Wreath) (hA : Nat.card A = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (A : Set Wreath)) :
    ∃ side : Bool, A = zpowers (rotation side) := by
  obtain ⟨x, hx⟩ := (ne_bot_iff_exists_ne_one (H := A)).mp
    (by intro hb; simp [hb] at hA)
  have hx1 : (x : Wreath) ≠ 1 := fun h => hx (Subtype.ext h)
  have hx3 : (x : Wreath) ^ 3 = 1 := congrArg Subtype.val
    (show x ^ 3 = 1 by simpa only [hA] using pow_card_eq_one' (x := x))
  have hgen : zpowers (x : Wreath) = A := eq_of_le_of_card_ge
    (zpowers_le.mpr x.property) (by
      rw [hA, Nat.card_zpowers, orderOf_eq_prime hx3 hx1])
  have hsr : s.right ≠ 1 := fun h => hs (eq_one_of_singular_preserving s hss h)
  have hc : s * x = x * s := (mem_centralizer_iff.mp hcentral x x.property).symm
  obtain ⟨side, he | he⟩ := cubic_swap_cases x s hx3 hx1 hsr hc
  · exact ⟨side, hgen.symm.trans (congrArg zpowers he)⟩
  · refine ⟨side, hgen.symm.trans ?_⟩
    rw [he, zpowers_inv]

/-- A nonidentity singular-displacement actor centralizing the marked cubic
subgroup forces its full normalizer and centralizer models. -/
public theorem normalizer_centralizer_models (A : Subgroup Wreath) (hA : Nat.card A = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (A : Set Wreath)) :
    Nonempty (normalizer (A : Set Wreath) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    Nonempty (centralizer (A : Set Wreath) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)) := by
  obtain ⟨side, rfl⟩ := cyclic_position A hA s hs hss hcentral
  exact models side

public theorem normalizer_centralizer_card (A : Subgroup Wreath) (hA : Nat.card A = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (A : Set Wreath)) :
    Nat.card (normalizer (A : Set Wreath)) = 36 ∧
      Nat.card (centralizer (A : Set Wreath)) = 18 := by
  obtain ⟨⟨e⟩, ⟨f⟩⟩ := normalizer_centralizer_models A hA s hs hss hcentral
  constructor
  · rw [Nat.card_congr e.toEquiv, Nat.card_prod]
    norm_num [S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  · rw [Nat.card_congr f.toEquiv, Nat.card_prod]
    norm_num [C3, S3, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The actual faithful action and original cubic subgroup give the ambient
normalizer and centralizer models of the literal image. -/
public theorem image_models {H : Type*} [Group H] (f : H →* Wreath)
    (hf : Function.Injective f) (A : Subgroup H) (hA : Nat.card A = 3)
    (s : H) (hs : s ≠ 1) (hss : SingularDisplacements (f s))
    (hcentral : s ∈ centralizer (A : Set H)) :
    Nonempty (normalizer (A.map f : Set Wreath) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    Nonempty (centralizer (A.map f : Set Wreath) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 3)) ∧
    Nat.card (normalizer (A.map f : Set Wreath)) = 36 ∧
    Nat.card (centralizer (A.map f : Set Wreath)) = 18 := by
  have hB : Nat.card (A.map f) = 3 := (card_map_of_injective hf).trans hA
  have hs' : f s ≠ 1 := fun h => hs (hf (h.trans f.map_one.symm))
  have hc : f s ∈ centralizer (A.map f : Set Wreath) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨a, ha, rfl⟩
    simpa only [map_mul] using congrArg f (mem_centralizer_iff.mp hcentral a ha)
  have hm := normalizer_centralizer_models (A.map f) hB (f s) hs' hss hc
  have hn := normalizer_centralizer_card (A.map f) hB (f s) hs' hss hc
  exact ⟨hm.1, hm.2, hn⟩

/-- Normality of the original cubic group embeds the entire acting group in
its now recognized order-36 normalizer. -/
public theorem image_le_normalizer_and_card_dvd {H : Type*} [Group H] [Finite H]
    (f : H →* Wreath) (hf : Function.Injective f) (A : Subgroup H) [A.Normal]
    (hA : Nat.card A = 3) (s : H) (hs : s ≠ 1)
    (hss : SingularDisplacements (f s)) (hcentral : s ∈ centralizer (A : Set H)) :
    f.range ≤ normalizer (A.map f : Set Wreath) ∧ Nat.card H ∣ 36 := by
  have hr : f.range ≤ normalizer (A.map f : Set Wreath) := by
    have hh := A.le_normalizer_map f
    rwa [A.normalizer_eq_top, ← f.range_eq_map] at hh
  refine ⟨hr, ?_⟩
  have hn := (image_models f hf A hA s hs hss hcentral).2.2.1
  rw [← hn]
  exact card_dvd_of_injective (f.codRestrict _ (fun x => hr ⟨x, rfl⟩))
    (fun x y h => hf (congrArg Subtype.val h))

end BinaryFourPlus.CubicNormalizer
