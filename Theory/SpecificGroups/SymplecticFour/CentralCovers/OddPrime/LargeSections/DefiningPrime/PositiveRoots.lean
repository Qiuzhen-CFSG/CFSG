module

public import Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime.Coordinates
public import Theory.SpecificGroups.SymplecticFour.CentralCovers.TwoPrimary.Transfer

/-!
# The odd-characteristic positive-root section criterion

Four additive lifts satisfying four commuting relations and the two crossing
relations give a section over the literal matrix unipotent subgroup. We
collect their ordered products using the coordinate multiplication law, then
apply transfer at its prime-to-p index. Existence of these compatible lifts
is a separate obligation; this criterion does not assume a global section.

Source: the type C₂ multiplier calculation in GLS3 §6.1 and
Aschbacher–Smith A.2.2(2), I.1.1–4, printed pp.33 and 407–408.
-/

public section
noncomputable section
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
variable {F E : Type*} [Field F] [Group E]

/-- Positive-root relations with the signs and structure constants valid in
all characteristics. These are equations in the covering group. -/
structure PositiveRootLifts (f : E →* Sp F) where
  x6 : Multiplicative F →* E
  x0 : Multiplicative F →* E
  x4 : Multiplicative F →* E
  x2 : Multiplicative F →* E
  project6 : f.comp x6 = RootSubgroup.parameter 6
  project0 : f.comp x0 = RootSubgroup.parameter 0
  project4 : f.comp x4 = RootSubgroup.parameter 4
  project2 : f.comp x2 = RootSubgroup.parameter 2
  commute60 : ∀ b k : F, Commute (x6 (.ofAdd b)) (x0 (.ofAdd k))
  commute04 : ∀ k w : F, Commute (x0 (.ofAdd k)) (x4 (.ofAdd w))
  commute02 : ∀ k v : F, Commute (x0 (.ofAdd k)) (x2 (.ofAdd v))
  commute42 : ∀ w v : F, Commute (x4 (.ofAdd w)) (x2 (.ofAdd v))
  crossing46 : ∀ w c : F,
    x4 (.ofAdd w) * x6 (.ofAdd c) =
      x6 (.ofAdd c) * x0 (.ofAdd (-2*c*w)) * x4 (.ofAdd w)
  crossing26 : ∀ v c : F,
    x2 (.ofAdd v) * x6 (.ofAdd c) =
      x6 (.ofAdd c) * x0 (.ofAdd (c^2*v)) * x4 (.ofAdd (-c*v)) * x2 (.ofAdd v)

namespace PositiveRootLifts
variable {f : E →* Sp F} (L : PositiveRootLifts f)

private def product (b k w v : F) : E :=
  L.x6 (.ofAdd b) * L.x0 (.ofAdd k) * L.x4 (.ofAdd w) * L.x2 (.ofAdd v)

private theorem add_left (x : Multiplicative F →* E) (s t : F) (z : E) :
    x (.ofAdd s) * (x (.ofAdd t) * z) = x (.ofAdd (s+t)) * z := by
  rw [← mul_assoc, ← map_mul]
  rfl

private theorem product_mul (b k w v c l t a : F) :
    L.product b k w v * L.product c l t a =
      L.product (b+c) (k+l-2*c*w+c^2*v) (w+t-c*v) (v+a) := by
  simp only [product, mul_assoc]
  rw [← mul_assoc (L.x2 (.ofAdd v)) (L.x6 (.ofAdd c)), L.crossing26]
  simp only [mul_assoc]
  rw [← mul_assoc (L.x4 (.ofAdd w)) (L.x6 (.ofAdd c)), L.crossing46]
  simp only [mul_assoc]
  rw [(L.commute60 c k).symm.left_comm]
  rw [(L.commute02 l v).symm.left_comm, (L.commute42 t v).symm.left_comm]
  rw [(L.commute04 (c^2*v) w).symm.left_comm]
  rw [(L.commute04 l (-c*v)).symm.left_comm, (L.commute04 l w).symm.left_comm]
  rw [add_left, add_left, add_left, add_left, add_left, add_left, ← map_mul]
  change L.x6 (.ofAdd (b+c)) * (L.x0 (.ofAdd (k+ -2*(c*w)+c^2*v+l)) *
    (L.x4 (.ofAdd (w+ -c*v+t)) * L.x2 (.ofAdd (v+a)))) = _
  rw [show k+ -2*(c*w)+c^2*v+l = k+l-2*(c*w)+c^2*v by ring,
    show w+ -c*v+t = w+t-c*v by ring]

include L in
/-- Collecting lifted roots defines a section with the actual subgroup inclusion. -/
theorem exists_unipotent_section [Finite F] :
    ∃ s : unipotent (F := F) →* E, f.comp s = (unipotent (F := F)).subtype := by
  let e : (F × F × F × F) ≃ unipotent (F := F) := Equiv.ofBijective
    (fun p => element p.1 p.2.1 p.2.2.1 p.2.2.2)
    ⟨element_injective, element_surjective⟩
  let j : unipotent (F := F) → E := fun g =>
    let p := e.symm g
    L.product p.1 p.2.1 p.2.2.1 p.2.2.2
  have hj (b k w v : F) : j (element b k w v) = L.product b k w v := by
    change L.product (e.symm (e (b,k,w,v))).1 (e.symm (e (b,k,w,v))).2.1
      (e.symm (e (b,k,w,v))).2.2.1 (e.symm (e (b,k,w,v))).2.2.2 = _
    rw [e.symm_apply_apply]
  have hjone : j 1 = 1 := by
    rw [← element_zero, hj]
    simp [product]
  have hjmul (x y : unipotent (F := F)) : j (x*y) = j x*j y := by
    obtain ⟨⟨b,k,w,v⟩, rfl⟩ := element_surjective x
    obtain ⟨⟨c,l,t,a⟩, rfl⟩ := element_surjective y
    rw [element_mul, hj, hj, hj, L.product_mul]
  refine ⟨{toFun := j, map_one' := hjone, map_mul' := hjmul}, ?_⟩
  apply MonoidHom.ext
  intro g
  obtain ⟨⟨b,k,w,v⟩, rfl⟩ := element_surjective g
  change f (j (element b k w v)) = _
  rw [hj]
  simp only [product, map_mul]
  simp only [← MonoidHom.comp_apply, L.project6, L.project0, L.project4, L.project2]
  rfl

end PositiveRootLifts

/-- Transfer consumes the complete positive-root relations at the literal
unipotent subgroup. Constructing those relations discharges the extra premise. -/
theorem not_dvd_card_kernel_of_positive_root_lifts {p : ℕ} [Fact p.Prime]
    [Finite E] (f : PerfectCentralCovering.Cover E (Sp (ZMod p)))
    (L : PositiveRootLifts f.toMonoidHom) : ¬ p ∣ Nat.card f.toMonoidHom.ker := by
  obtain ⟨s,hs⟩ := L.exists_unipotent_section
  exact PerfectCentralCovering.not_dvd_card_kernel_of_section f _
    not_dvd_index_unipotent s hs

end Theory.SpecificGroups.SymplecticFour.CentralCovers.OddPrime.LargeSections.DefiningPrime
