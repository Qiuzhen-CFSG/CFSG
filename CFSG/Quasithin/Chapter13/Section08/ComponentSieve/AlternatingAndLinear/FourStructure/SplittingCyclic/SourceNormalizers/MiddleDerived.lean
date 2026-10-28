module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.MiddleParabolic.FlagTransport
public import Theory.ElementaryAbelian.Basic

/-!
# The middle-parabolic obstruction needs only the derived action

Seven explicit commutators in the standard middle parabolic already send
every involution outside its central line to at least four distinct
nonidentity conjugates. A normalized four-group cannot contain any such
involution. The remaining elements are determined by one binary coordinate,
so cannot form a four-group either. The finite calculation is checked by
kernel reduction and connected to the actual GL₄(2) conjugation action.
An adapted basis transports the result to any marked incident flag.

This strengthens the existing middle-parabolic obstruction just enough for
central-section lifting: derived line stabilizers have exact centralizing
lifts, while individual line stabilizers may retain a central error.
Source: Aschbacher–Smith 13.8.25, printed p.962 (PDF p.979). The block
calculation adapts `SplittingCyclic.MiddleParabolic.Obstruction`.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.MiddleDerived
open BinaryLinear BinaryLinear.MiddleParabolic
open Subgroup
open scoped commutatorElement

private def identity : Params := ![0,0,0,1,0,0,0,1,0]
private def square (p : Params) : Params :=
 ![p 0 + p 0*p 3 + p 1*p 6, p 1 + p 0*p 4 + p 1*p 7,
 p 0*p 5 + p 1*p 8, p 3*p 3 + p 4*p 6, p 3*p 4 + p 4*p 7,
 p 3*p 5 + p 4*p 8 + p 5, p 6*p 3 + p 7*p 6, p 6*p 4 + p 7*p 7,
 p 6*p 5 + p 7*p 8 + p 8]
private def baseConjugate (k : Fin 8) (p : Params) : Params :=
 match k with
 | 0 => p
 | 1 => ![p 0+p 3+1,p 1+p 4,p 2+p 5,p 3,p 4,p 5,p 6,p 7,p 8]
 | 2 => ![p 0+p 6,p 1+p 7+1,p 2+p 8,p 3,p 4,p 5,p 6,p 7,p 8]
 | 3 => ![p 0,p 1,p 2+p 0,p 3,p 4,p 5+p 3+1,p 6,p 7,p 8+p 6]
 | 4 => ![p 0,p 1,p 2+p 1,p 3,p 4,p 5+p 4,p 6,p 7,p 8+p 7+1]
 | 5 => ![p 0,p 1+p 0,p 2,p 3+p 6,p 4+p 3+p 7+p 6,p 5+p 8,p 6,p 7+p 6,p 8]
 | 6 => ![p 1,p 0,p 2,p 7,p 6,p 8,p 4,p 3,p 5]
 | 7 => ![p 0+p 1,p 1,p 2,p 3+p 4,p 4,p 5,p 6+p 3+p 7+p 4,p 7+p 4,p 8+p 5]

private theorem block_square (p : Params) (v : V) :
    block p (block p v) = block (square p) v := by
  ext i
  fin_cases i <;> simp [block, square] <;> ring_nf
  simp [show (2 : ZMod 2) = 0 by decide]

private theorem block_conjugate (p : Params) (k : Fin 8) (v : V) :
    actorFun k (block p (actorFun k v)) = block (baseConjugate k p) v := by
  fin_cases k <;> ext i <;> fin_cases i <;> simp [block, baseConjugate, actorFun] <;> ring

private theorem coordinates_of_apply {g : BinaryLinear.GL V} {p : Params}
    (h : ∀ v, g v = block p v) : coordinates g = p := by
  ext i
  fin_cases i <;> simp [coordinates, h, block]

@[simp] private theorem coordinates_one : coordinates (1 : BinaryLinear.GL V) = identity := by
  decide +kernel

private theorem coordinates_square {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic line ⊓ parabolic hyperplane) :
    coordinates (g * g) = square (coordinates g) := by
  apply coordinates_of_apply
  intro v
  change g (g v) = _
  rw [apply_eq_block hg, apply_eq_block hg, block_square]

private theorem coordinates_conjugate (k : Fin 8) {g : BinaryLinear.GL V}
    (hg : g ∈ parabolic line ⊓ parabolic hyperplane) :
    coordinates (actor k * g * (actor k)⁻¹) = baseConjugate k (coordinates g) := by
  apply coordinates_of_apply
  intro v
  change actorFun k (g (actorFun k v)) = _
  rw [apply_eq_block hg, block_conjugate]



private def pair : Fin 7 → Fin 8 × Fin 8
  | 0 => (0, 0) | 1 => (2, 7) | 2 => (1, 5) | 3 => (4, 5)
  | 4 => (3, 7) | 5 => (5, 6) | 6 => (5, 7)
private def derivedActor (k : Fin 7) : BinaryLinear.GL V :=
  ⁅actor (pair k).1, actor (pair k).2⁆
private def conjugate (k : Fin 7) (p : Params) : Params :=
  baseConjugate (pair k).1 (baseConjugate (pair k).2
    (baseConjugate (pair k).1 (baseConjugate (pair k).2 p)))
private def orbit (p : Params) : Finset Params := Finset.univ.image (fun k => conjugate k p)

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1600000 in
private theorem orbit_bound : ∀ p : Params, square p = identity →
    (5 ≤ (insert identity (orbit p)).card ∨
      p = ![0,0,p 2,1,0,0,0,1,0]) := by
  decide +kernel

private theorem derivedActor_mem (k : Fin 7) :
    derivedActor k ∈ ⁅middle line hyperplane, middle line hyperplane⁆ :=
  commutator_mem_commutator (actor_mem _) (actor_mem _)

private theorem coordinates_derived_conjugate (k : Fin 7) {g : BinaryLinear.GL V}
    (hg : g ∈ middle line hyperplane) :
    coordinates (derivedActor k * g * (derivedActor k)⁻¹) = conjugate k (coordinates g) := by
  have hn (j : Fin 8) {x : BinaryLinear.GL V} (hx : x ∈ middle line hyperplane) :
      actor j * x * (actor j)⁻¹ ∈ middle line hyperplane :=
    (middle line hyperplane).mul_mem ((middle line hyperplane).mul_mem (actor_mem j) hx)
      ((middle line hyperplane).inv_mem (actor_mem j))
  have he : derivedActor k * g * (derivedActor k)⁻¹ =
      actor (pair k).1 * (actor (pair k).2 * (actor (pair k).1 *
        (actor (pair k).2 * g * (actor (pair k).2)⁻¹) * (actor (pair k).1)⁻¹) *
        (actor (pair k).2)⁻¹) * (actor (pair k).1)⁻¹ := by
    simp only [derivedActor, commutatorElement_def, mul_inv_rev, actor_inv]
    simp only [mul_assoc]
  rw [he, coordinates_conjugate _ (hn _ (hn _ (hn _ hg))),
    coordinates_conjugate _ (hn _ (hn _ hg)), coordinates_conjugate _ (hn _ hg),
    coordinates_conjugate _ hg]
  rfl

/-- No subgroup of order four and exponent two is normalized by the derived subgroup of the standard middle parabolic. -/
private theorem standard_no_derived_normal_four (E : Subgroup (BinaryLinear.GL V))
    (hE : ∀ x ∈ E, x ^ 2 = 1) (hcard : Nat.card E = 4)
    (hEH : E ≤ parabolic line ⊓ parabolic hyperplane)
    (hHE : ⁅middle line hyperplane, middle line hyperplane⁆ ≤ Subgroup.normalizer E) : False := by
  classical
  let : Finite E := Nat.finite_of_card_ne_zero (by omega)
  let : Fintype E := Fintype.ofFinite E
  let C : Finset Params := Finset.univ.image (fun x : E => coordinates x.val)
  have hC : C.card ≤ 4 := by
    calc
      C.card ≤ Fintype.card E := Finset.card_image_le
      _ = 4 := by rwa [← Nat.card_eq_fintype_card]
  have hp (x : E) : coordinates x.val = ![0,0,coordinates x.val 2,1,0,0,0,1,0] := by
    have hs : square (coordinates x.val) = identity := by
      rw [← coordinates_square (hEH x.property), ← pow_two, hE x.val x.property,
        coordinates_one]
    rcases orbit_bound (coordinates x.val) hs with hlarge | hcentral
    · have hsubset : insert identity (orbit (coordinates x.val)) ⊆ C := by
        intro p hp
        rcases Finset.mem_insert.mp hp with rfl | hp
        · apply Finset.mem_image.mpr
          exact ⟨1, Finset.mem_univ _, coordinates_one⟩
        · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hp
          let y : E := ⟨derivedActor k * x.val * (derivedActor k)⁻¹,
            (hHE (derivedActor_mem k) x.val).mp x.property⟩
          exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _,
            coordinates_derived_conjugate k (hEH x.property)⟩
      have := Finset.card_le_card hsubset
      omega
    · exact hcentral
  have hinj : Function.Injective (fun x : E => coordinates x.val 2) := by
    intro x y hxy
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    rw [apply_eq_block (hEH x.property), apply_eq_block (hEH y.property), hp x, hp y]
    change coordinates x.val 2 = coordinates y.val 2 at hxy
    rw [hxy]
  have hb := Nat.card_le_card_of_injective _ hinj
  have : Nat.card E ≤ 2 := by simpa using hb
  omega

/-- An elementary abelian subgroup of order four cannot be normalized by the derived subgroup of the
middle minimal parabolic of an incident 1,2,3 flag in GL₄(2). -/
theorem no_derived_normal_elementary_four
    {L P F : Submodule (ZMod 2) V} (hLP : L ≤ P) (hPF : P ≤ F)
    (hL : Module.finrank (ZMod 2) L = 1)
    (hP : Module.finrank (ZMod 2) P = 2)
    (hF : Module.finrank (ZMod 2) F = 3)
    (E : Subgroup (BinaryLinear.GL V)) [IsElementaryAbelian 2 E]
    (hcard : Nat.card E = 4) (hEH : E ≤ middle L F)
    (hHE : ⁅middle L F, middle L F⁆ ≤ Subgroup.normalizer E) : False := by
  obtain ⟨e, heH, _⟩ := exists_flag_conjugation L P F hLP hPF hL hP hF
  let a := MulAut.conj e
  have hmem (x : BinaryLinear.GL V) : a x ∈ middle L F ↔ x ∈ middle line hyperplane := by
    rw [← heH, Subgroup.mem_map_equiv]
    change a.symm (a x) ∈ middle line hyperplane ↔ x ∈ middle line hyperplane
    rw [a.symm_apply_apply]
  let E' := E.comap a.toMonoidHom
  apply standard_no_derived_normal_four E'
  · intro x hx
    apply a.injective
    simpa only [map_pow, map_one] using elemPow_eq_one_of_isElementaryAbelian (a x) hx
  · change Nat.card (E.comap a.toMonoidHom) = 4
    have heq : E.comap a.toMonoidHom = E.map a.symm.toMonoidHom :=
      Subgroup.comap_equiv_eq_map_symm a E
    exact (Nat.card_congr (MulEquiv.subgroupCongr heq).toEquiv).trans
      ((Nat.card_congr (a.symm.subgroupMap E).toEquiv).symm.trans hcard)
  · intro x hx
    exact (hmem x).mp (hEH hx)
  · intro x hx
    apply Subgroup.le_normalizer_comap a.toMonoidHom
    apply hHE
    rw [← heH, ← Subgroup.map_commutator]
    exact Subgroup.mem_map_of_mem _ hx

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingCyclic.SourceNormalizers.MiddleDerived
