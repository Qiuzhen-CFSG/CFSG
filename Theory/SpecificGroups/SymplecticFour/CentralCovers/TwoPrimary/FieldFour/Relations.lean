module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour.Roots
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.PositiveRoots
import Mathlib.Tactic.Group

/-!
# All positive-root relations in a central extension

The torus-equivariant root sections satisfy the five commuting relations.
For fixed v, both [x₂(v),x₆(c)] and x₀(c²v)x₄(cv) are additive functions of c.
They have the same matrix image and the same action of diag(a,1). Two such
homomorphisms agree: their commutators with a lift of diag(a,1) agree, and
multiplication by a−1 is surjective when a ≠ 1. This proves the remaining
crossing relation, including over the field of four elements.

The resulting `PositiveRootLifts` supplies all relations needed by the actual
matrix unipotent-section construction. No presentation-lifting assumption or
multiplier computation is used.

Source: the defining-prime calculation for type C₂ underlying Aschbacher–Smith
I.1.3, printed p.407, and GLS3 §6.1.
-/

public section

open Representation.OneCohomology.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
open scoped commutatorElement

namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
variable {F E : Type*} [Field F] [Group E]

private theorem hom_eq_of_scalar_equivariance (f : E →* Sp F)
    (hk : f.ker ≤ Subgroup.center E) (u w : Multiplicative F →* E)
    (hproj : ∀ x : F, f (u (.ofAdd x)) = f (w (.ofAdd x)))
    (c : F) (hc : c ≠ 1) (d : E)
    (hu : ∀ x : F, d*u (.ofAdd x)*d⁻¹ = u (.ofAdd (c*x)))
    (hw : ∀ x : F, d*w (.ofAdd x)*d⁻¹ = w (.ofAdd (c*x))) : u = w := by
  apply MonoidHom.ext
  intro x
  let y := (c-1)⁻¹*x.toAdd
  have h := CentralExtension.commutator_eq_of_image_eq f hk
    (x := d) (x' := d) rfl (hproj y)
  rw [commutatorElement_def, commutatorElement_def, hu, hw,
    ← u.map_inv, ← w.map_inv, ← u.map_mul, ← w.map_mul] at h
  change u (.ofAdd (c*y + -y)) = w (.ofAdd (c*y + -y)) at h
  have hy : c*y + -y = x.toAdd := by
    calc
      _ = (c-1)*y := by ring
      _ = x.toAdd := mul_inv_cancel_left₀ (sub_ne_zero.mpr hc) _
  rw [hy] at h
  exact h

variable [Finite F] [CharP F 2]

private theorem lifted_crossing (hF : 2 < Nat.card F)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E)
    (L : ∀ r : Fin 8, RootSection f r) (v c : F) :
    (L 2).lift (.ofAdd v) * (L 6).lift (.ofAdd c) =
      (L 6).lift (.ofAdd c) * (L 0).lift (.ofAdd (c^2*v)) *
        (L 4).lift (.ofAdd (c*v)) * (L 2).lift (.ofAdd v) := by
  let x (r : Fin 8) (t : F) : E := (L r).lift (.ofAdd t)
  have hx (r : Fin 8) (t : F) : f (x r t) = rootElement r t :=
    DFunLike.congr_fun (L r).project (.ofAdd t)
  have hadd (r : Fin 8) (s t : F) : x r (s+t) = x r s*x r t :=
    (L r).lift.map_mul (.ofAdd s) (.ofAdd t)
  have hzero (r : Fin 8) : x r 0 = 1 := (L r).lift.map_one
  have hcomm {r s : Fin 8} (h : CommutingPair r s) (t u : F) :
      Commute (x r t) (x s u) := commuting_pair_lifts hF f hf hk h (hx r t) (hx s u)
  have hproj (t : F) : f ⁅x 2 v,x 6 t⁆ = f (x 0 (t^2*v)*x 4 (t*v)) := by
    rw [map_commutatorElement, map_mul, hx, hx, hx, hx, matrix_commutator]
  have hc6 (s t : F) : Commute (x 6 s) ⁅x 2 v,x 6 t⁆ := by
    apply commutatorElement_eq_one_iff_commute.mp
    rw [CentralExtension.commutator_eq_of_image_eq f hk rfl (hproj t)]
    exact ((hcomm (by simp [CommutingPair]) s (t^2*v)).mul_right
      (hcomm (by simp [CommutingPair]) s (t*v))).commutator_eq
  let C : Multiplicative F →* E := {
    toFun t := ⁅x 2 v,x 6 t.toAdd⁆
    map_one' := by change ⁅x 2 v,x 6 0⁆ = 1; rw [hzero]; simp
    map_mul' s t := by
      change ⁅x 2 v,x 6 (s.toAdd+t.toAdd)⁆ = _
      rw [hadd, commutatorElement_mul_right_eq_mul_conj]
      rw [mul_assoc ⁅x 2 v,x 6 s.toAdd⁆, (hc6 s.toAdd t.toAdd).eq]
      simp [mul_assoc] }
  let P : Multiplicative F →* E := {
    toFun t := x 0 (t.toAdd^2*v)*x 4 (t.toAdd*v)
    map_one' := by change x 0 (0^2*v)*x 4 (0*v) = 1; simp [hzero]
    map_mul' s t := by
      change x 0 ((s.toAdd+t.toAdd)^2*v)*x 4 ((s.toAdd+t.toAdd)*v) = _
      rw [CharTwo.add_sq, add_mul, add_mul, hadd, hadd]
      exact (hcomm (by simp [CommutingPair]) (t.toAdd^2*v) (s.toAdd*v)).mul_mul_mul_comm _ _ }
  have hu : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Fˣ := (Finite.one_lt_card_iff_nontrivial).mp hu
  obtain ⟨a,ha⟩ := exists_ne (1 : Fˣ)
  obtain ⟨d,hd⟩ := hf (diagonalTorus a 1)
  have heq (r : Fin 8) (t : F) :
      d*x r t*d⁻¹ = x r ((diagonalWeight r a 1 : F)*t) :=
    (L r).equivariant a 1 d hd t
  have hCP : C = P := by
    apply hom_eq_of_scalar_equivariance f hk C P hproj (a : F)
      (fun h => ha (Units.ext h)) d
    · intro t
      change d*⁅x 2 v,x 6 t⁆*d⁻¹ = ⁅x 2 v,x 6 ((a : F)*t)⁆
      rw [conjugate_commutatorElement, heq, heq]
      simp [diagonalWeight]
    · intro t
      change d*(x 0 (t^2*v)*x 4 (t*v))*d⁻¹ =
        x 0 (((a : F)*t)^2*v)*x 4 (((a : F)*t)*v)
      have hmul : d*(x 0 (t^2*v)*x 4 (t*v))*d⁻¹ =
          (d*x 0 (t^2*v)*d⁻¹)*(d*x 4 (t*v)*d⁻¹) := by group
      rw [hmul, heq, heq]
      simp [diagonalWeight, mul_pow, mul_assoc]
  have hcc : ⁅x 2 v,x 6 c⁆ = x 0 (c^2*v)*x 4 (c*v) :=
    DFunLike.congr_fun hCP (.ofAdd c)
  change x 2 v*x 6 c = x 6 c*x 0 (c^2*v)*x 4 (c*v)*x 2 v
  have hmove : Commute (x 6 c) (x 0 (c^2*v)*x 4 (c*v)) :=
    (hcomm (by simp [CommutingPair]) c (c^2*v)).mul_right
    (hcomm (by simp [CommutingPair]) c (c*v))
  calc
    x 2 v*x 6 c = ⁅x 2 v,x 6 c⁆*x 6 c*x 2 v := by
      simp [commutatorElement_def, mul_assoc]
    _ = (x 0 (c^2*v)*x 4 (c*v))*x 6 c*x 2 v := by rw [hcc]
    _ = _ := by rw [← hmove.eq]; simp only [mul_assoc]

/-- Every surjective central extension admits all four positive-root sections
with the literal projections, five commuting pairs and crossing relation. -/
theorem exists_positive_root_lifts (hF : 2 < Nat.card F)
    (f : E →* Sp F) (hf : Function.Surjective f) (hk : f.ker ≤ Subgroup.center E) :
    Nonempty (PositiveRootLifts f) := by
  classical
  let L (r : Fin 8) : RootSection f r := (exists_root_section hF f hf hk r).some
  have hcomm {r s : Fin 8} (h : CommutingPair r s) (v w : F) :
      Commute ((L r).lift (.ofAdd v)) ((L s).lift (.ofAdd w)) :=
    commuting_pair_lifts hF f hf hk h
      (DFunLike.congr_fun (L r).project (.ofAdd v))
      (DFunLike.congr_fun (L s).project (.ofAdd w))
  exact ⟨{
    x6 := (L 6).lift
    x0 := (L 0).lift
    x4 := (L 4).lift
    x2 := (L 2).lift
    project6 := (L 6).project
    project0 := (L 0).project
    project4 := (L 4).project
    project2 := (L 2).project
    commute60 := hcomm (by simp [CommutingPair])
    commute64 := hcomm (by simp [CommutingPair])
    commute04 := hcomm (by simp [CommutingPair])
    commute02 := hcomm (by simp [CommutingPair])
    commute42 := hcomm (by simp [CommutingPair])
    crossing := lifted_crossing hF f hf hk L }⟩

end Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.FieldFour
