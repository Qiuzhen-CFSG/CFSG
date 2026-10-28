module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime.TorusLifts
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime.PositiveRoots
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField.Relations
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring

/-!
# Positive-root relations in odd-prime symplectic central extensions

Four commuting pairs are separated by diagonal torus weights. For the two
crossing relations, conjugation by a lift of diag(d,d,d⁻¹,d⁻¹) fixes root 6
and scales each of roots 0, 4, 2 by d². Two additive lifts with the same
projection and this nontrivial scalar equivariance are equal: their
commutators with the torus lift are independent of the central error.
This proves both crossing relations, including the structure constant 2.

The scalar condition is d² ≠ 1, available for every p > 3. In particular
no fourth-power condition excludes p = 5. Only characteristic-independent
matrix identities and a general central-commutator lemma are reused from
the even-characteristic development.

Source: GLS3 §6.1, type C₂ multiplier, and Aschbacher–Smith I.1.1–4,
printed pp.407–408.
-/

public section
noncomputable section
open Matrix
open scoped commutatorElement
open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.LargeField
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime

/-- Nontrivial scalar equivariance removes the ambiguity between additive lifts. -/
theorem additive_lifts_eq_of_equivariant {F E G : Type*} [Field F] [Group E] [Group G]
    (f : E →* G) (hk : f.ker ≤ Subgroup.center E)
    (u v : F → E) (hu : ∀ x y, u (x+y) = u x * u y)
    (hv : ∀ x y, v (x+y) = v x * v y) (hproj : ∀ x, f (u x) = f (v x))
    (z : E) (c : F) (hc : c ≠ 1)
    (htu : ∀ x, z * u x * z⁻¹ = u (c*x))
    (htv : ∀ x, z * v x * z⁻¹ = v (c*x)) (x : F) : u x = v x := by
  have hcomm (w : F → E) (ha : ∀ s t, w (s+t) = w s * w t)
      (ht : ∀ t, z * w t * z⁻¹ = w (c*t)) (t : F) :
      ⁅z,w t⁆ = w ((c-1)*t) := by
    rw [commutatorElement_def, ht, show c*t = (c-1)*t+t by ring, ha,
      mul_assoc, mul_inv_cancel, mul_one]
  have h := CentralExtension.commutator_eq_of_image_eq f hk
    (x := z) (x' := z) rfl (hproj ((c-1)⁻¹*x))
  rw [hcomm u hu htu, hcomm v hv htv,
    mul_inv_cancel_left₀ (sub_ne_zero.mpr hc)] at h
  exact h

private theorem additive_product {F E : Type*} [Field F] [Group E]
    (u v : F → E) (hu : ∀ x y, u (x+y) = u x * u y)
    (hv : ∀ x y, v (x+y) = v x * v y)
    (hc : ∀ x y, Commute (u x) (v y)) (x y : F) :
    u (x+y) * v (x+y) = (u x*v x)*(u y*v y) := by
  rw [hu,hv]
  exact (hc y x).mul_mul_mul_comm _ _

private theorem matrix_crossing46 {F : Type*} [Field F] (w c : F) :
    rootElement 4 w * rootElement 6 c =
      rootElement 6 c * rootElement 0 (-2*c*w) * rootElement 4 w := by
  apply Subtype.ext
  change rootMatrix 4 w * rootMatrix 6 c =
    rootMatrix 6 c * rootMatrix 0 (-2*c*w) * rootMatrix 4 w
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single]
  all_goals ring

private theorem matrix_crossing26 {F : Type*} [Field F] (v c : F) :
    rootElement 2 v * rootElement 6 c =
      rootElement 6 c * rootElement 0 (c^2*v) * rootElement 4 (-c*v) * rootElement 2 v := by
  apply Subtype.ext
  change rootMatrix 2 v * rootMatrix 6 c =
    rootMatrix 6 c * rootMatrix 0 (c^2*v) * rootMatrix 4 (-c*v) * rootMatrix 2 v
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [rootMatrix, Matrix.fromBlocks, Matrix.mul_apply,
      Fintype.sum_sum_type, Fin.sum_univ_two, Matrix.single]
  all_goals ring

variable {p : ℕ} [Fact p.Prime] {E : Type*} [Group E]

private def PositiveCommutingPair (r s : Fin 8) : Prop :=
  (r = 6 ∧ s = 0) ∨ (r = 0 ∧ s = 4) ∨ (r = 0 ∧ s = 2) ∨ (r = 4 ∧ s = 2)

private theorem separating_torus (hp : 3 < p) {r s : Fin 8}
    (h : PositiveCommutingPair r s) :
    ∃ a b : (ZMod p)ˣ, torusWeight r a b ≠ 1 ∧ torusWeight s a b = 1 := by
  obtain ⟨c,hc⟩ := exists_unit_sq_ne_one hp
  have hc1 : c ≠ 1 := fun h => hc (by rw [h, one_pow])
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨1,c,by simpa [torusWeight] using hc1,by simp [torusWeight]⟩
  · exact ⟨c,c⁻¹,by simpa [torusWeight] using hc,by simp [torusWeight]⟩
  · exact ⟨c,1,by simpa [torusWeight] using hc,by simp [torusWeight]⟩
  · exact ⟨c,1,by simpa [torusWeight] using hc1,by simp [torusWeight]⟩

private theorem lifted_commute (hp : 3 < p)
    (f : E →* Sp (ZMod p)) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (u : Fin 8 → Multiplicative (ZMod p) →* E)
    (hu : ∀ r, f.comp (u r) = RootSubgroup.parameter r)
    (ht : ∀ (r : Fin 8) (a b : (ZMod p)ˣ) (z : E), f z = diagonalTorus a b →
      ∀ t : ZMod p, z * u r (.ofAdd t) * z⁻¹ =
        u r (.ofAdd ((torusWeight r a b : ZMod p)*t)))
    {r s : Fin 8} (hrs : PositiveCommutingPair r s) (x y : ZMod p) :
    Commute (u r (.ofAdd x)) (u s (.ofAdd y)) := by
  obtain ⟨a,b,ha,hb⟩ := separating_torus hp hrs
  obtain ⟨z,hz⟩ := hf (diagonalTorus a b)
  apply commute_of_fixed_scale f hk (u r) (u s (.ofAdd y)) z
    (torusWeight r a b : ZMod p) (fun H => ha (Units.ext H)) ?_ (ht r a b z hz) ?_ x
  · intro t
    change Commute ((f.comp (u r)) (.ofAdd t)) ((f.comp (u s)) (.ofAdd y))
    rw [hu,hu]
    rcases hrs with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact matrix_commute60 t y
    · exact matrix_commute04 t y
    · exact matrix_commute02 t y
    · exact matrix_commute42 t y
  · simpa only [hb, Units.val_one, one_mul] using ht s a b z hz y

/-- The complete positive-root relations lift in every central extension of Sp₄(Fₚ). -/
theorem positiveRootLifts_of_central_extension (hp : 3 < p)
    (f : E →* Sp (ZMod p)) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    Nonempty (PositiveRootLifts f) := by
  choose u hu ht using fun r => exists_equivariant_root_lift hp f hf hk r
  let X : Fin 8 → ZMod p → E := fun r x => u r (.ofAdd x)
  have hXa (r : Fin 8) (x y : ZMod p) : X r (x+y) = X r x * X r y :=
    (u r).map_mul (.ofAdd x) (.ofAdd y)
  have hXp (r : Fin 8) (x : ZMod p) : f (X r x) = rootElement r x :=
    DFunLike.congr_fun (hu r) (.ofAdd x)
  have h60 := lifted_commute hp f hf hk u hu ht (r := 6) (s := 0) (Or.inl ⟨rfl,rfl⟩)
  have h04 := lifted_commute hp f hf hk u hu ht (r := 0) (s := 4) (Or.inr (Or.inl ⟨rfl,rfl⟩))
  have h02 := lifted_commute hp f hf hk u hu ht (r := 0) (s := 2)
    (Or.inr (Or.inr (Or.inl ⟨rfl,rfl⟩)))
  have h42 := lifted_commute hp f hf hk u hu ht (r := 4) (s := 2)
    (Or.inr (Or.inr (Or.inr ⟨rfl,rfl⟩)))
  obtain ⟨d,hd⟩ := exists_unit_sq_ne_one hp
  obtain ⟨z,hz⟩ := hf (diagonalTorus d d)
  let e : E ≃* E := MulAut.conj z
  let q : ZMod p := (d : ZMod p)^2
  have hq : q ≠ 1 := fun h => hd (Units.ext h)
  have he6 (x : ZMod p) : e (X 6 x) = X 6 x := by
    simpa [torusWeight,e,X,MulAut.conj_apply] using ht 6 d d z hz x
  have he0 (x : ZMod p) : e (X 0 x) = X 0 (q*x) := by
    simpa [torusWeight,q,e,X,MulAut.conj_apply] using ht 0 d d z hz x
  have he4 (x : ZMod p) : e (X 4 x) = X 4 (q*x) := by
    simpa [torusWeight,q,pow_two,e,X,MulAut.conj_apply] using ht 4 d d z hz x
  have he2 (x : ZMod p) : e (X 2 x) = X 2 (q*x) := by
    simpa [torusWeight,q,e,X,MulAut.conj_apply] using ht 2 d d z hz x
  have cross46 (w c : ZMod p) : X 4 w * X 6 c = X 6 c * X 0 (-2*c*w) * X 4 w := by
    let C : ZMod p → E := fun x => (X 6 c)⁻¹ * X 4 x * X 6 c
    let P : ZMod p → E := fun x => X 0 (-2*c*x) * X 4 x
    have hCa (x y : ZMod p) : C (x+y) = C x * C y := by
      dsimp [C]
      rw [hXa]
      group
    have hPa (x y : ZMod p) : P (x+y) = P x * P y := by
      apply additive_product (fun x => X 0 (-2*c*x)) (X 4)
        (fun x y => by rw [mul_add,hXa]) (hXa 4) (fun x y => h04 _ _)
    have hproj (x : ZMod p) : f (C x) = f (P x) := by
      simp only [C,P,map_mul,map_inv,hXp]
      rw [mul_assoc, matrix_crossing46]
      simp only [mul_assoc, inv_mul_cancel_left]
    have hCt (x : ZMod p) : z*C x*z⁻¹ = C (q*x) := by
      change e (C x) = _
      simp only [C,map_mul,map_inv,he6,he4]
    have hPt (x : ZMod p) : z*P x*z⁻¹ = P (q*x) := by
      change e (P x) = _
      simp only [P,map_mul,he0,he4]
      congr 2
      ring
    have H := additive_lifts_eq_of_equivariant f hk C P hCa hPa hproj z q hq hCt hPt w
    have H' := congrArg (fun a => X 6 c * a) H
    simpa only [C,P,mul_assoc,mul_inv_cancel_left] using H'
  have cross26 (v c : ZMod p) : X 2 v * X 6 c =
      X 6 c * X 0 (c^2*v) * X 4 (-c*v) * X 2 v := by
    let C : ZMod p → E := fun x => (X 6 c)⁻¹ * X 2 x * X 6 c
    let P : ZMod p → E := fun x => X 0 (c^2*x) * X 4 (-c*x) * X 2 x
    have hCa (x y : ZMod p) : C (x+y) = C x * C y := by
      dsimp [C]
      rw [hXa]
      group
    have hPa (x y : ZMod p) : P (x+y) = P x * P y := by
      apply additive_product (fun x => X 0 (c^2*x) * X 4 (-c*x)) (X 2)
      · intro s t
        apply additive_product (fun x => X 0 (c^2*x)) (fun x => X 4 (-c*x))
          (fun x y => by rw [mul_add,hXa]) (fun x y => by rw [mul_add,hXa])
          (fun x y => h04 _ _)
      · exact hXa 2
      · intro s t
        exact (h02 _ _).mul_left (h42 _ _)
    have hproj (x : ZMod p) : f (C x) = f (P x) := by
      simp only [C,P,map_mul,map_inv,hXp]
      rw [mul_assoc, matrix_crossing26]
      simp only [mul_assoc, inv_mul_cancel_left]
    have hCt (x : ZMod p) : z*C x*z⁻¹ = C (q*x) := by
      change e (C x) = _
      simp only [C,map_mul,map_inv,he6,he2]
    have hPt (x : ZMod p) : z*P x*z⁻¹ = P (q*x) := by
      change e (P x) = _
      simp only [P,map_mul,he0,he4,he2]
      congr 2 <;> congr 1 <;> ring
    have H := additive_lifts_eq_of_equivariant f hk C P hCa hPa hproj z q hq hCt hPt v
    have H' := congrArg (fun a => X 6 c * a) H
    simpa only [C,P,mul_assoc,mul_inv_cancel_left] using H'
  exact ⟨{ x6 := u 6
           x0 := u 0
           x4 := u 4
           x2 := u 2
           project6 := hu 6
           project0 := hu 0
           project4 := hu 4
           project2 := hu 2
           commute60 := h60
           commute04 := h04
           commute02 := h02
           commute42 := h42
           crossing46 := cross46
           crossing26 := cross26 }⟩

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
